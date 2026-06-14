"""The boundary: options, serialization, verdict readers, FFI utilities, and Python oracles.

The compiler itself is the pure lambda term ``_compile_term.COMPILE``; this module is everything
Python does AROUND it. Encoding an option dataclass to its Scott union, quoting the input, running
the interpreter, and serializing the resulting Scott Python AST are boundary codecs; reading a
lambda-level verdict (typability, closedness, normalization) back as a Python bool is a readout;
``compile_callable``/``value_island``/``lazy_island`` are FFI utilities over the runtime; and the
Python implementations at the bottom (``_Inference``, ``call_by_value_islands``,
``needs_folding``, the interpret-target reconstruction) are SPECIFICATIONS and test oracles, off
the lambda production path.

The analyses certify, per sub-term, the runtime that preserves the interpreted behaviour:

- ``is_typable`` (algorithm-W): a simply-typed term is strongly normalizing, so strict call-by-value
  terminates with the same normal form.
- ``needs_folding`` consults the interpreter as a sound oracle: a finite normal form means
  call-by-name/need (which never folds) reaches the same value.

``choose_runtime`` layers these: call-by-value if typable; else call-by-need if the behaviour is a
finite normal form; else interpret, meaning leave the term to the interpreter, which always folds
correctly. Anything not certified stays interpreted.
"""

from __future__ import annotations

import ast

from dataclasses import dataclass
from enum import Enum, auto
from typing import Callable

from co_lambda._analysis import IS_CLOSED
from co_lambda._ast import App, Lam, Native, Node, Var
from co_lambda._codec import church, int_to_binnat, interpret_boolean, quote
from co_lambda._compile_term import CHOOSE_RUNTIME, COMPILE
from co_lambda._compiler import CODEGEN, CODEGEN_NEED
from co_lambda._dsl import app, build, curry
from co_lambda._prelude import FALSE, TRUE
from co_lambda._pyast import _church_to_int, _reset_gensym, decode, memoized_decode, to_anf_source
from co_lambda._reduce import NORMALIZES
from co_lambda._render import render
from co_lambda._runtime import (
    _LazyThunk,
    _NeedThunk,
    call_by_need_globals,
    force,
    recursion_headroom,
    run_in_large_stack,
    value_island as _runtime_value_island,
    value_island_by_name as _runtime_value_island_by_name,
)
from co_lambda._typecheck import TYPABLE, TYPABLE_BU


class Runtime(Enum):
    CALL_BY_VALUE = auto()  # strict: an argument is evaluated to a value before the call
    CALL_BY_NAME = auto()  # an argument is a thunk recomputed on each force (no sharing)
    CALL_BY_NEED = auto()  # call-by-name plus memoisation: the thunk computes once and shares
    INTERPRET = auto()  # not a compiled target: re-submit the term to the interpreter


def _option(runtime: Runtime):
    """The Scott compilation option for a compiled expression target: a Church boolean ``thunked``."""
    if runtime is Runtime.CALL_BY_VALUE:
        return FALSE
    if runtime is Runtime.CALL_BY_NAME:
        return TRUE
    if runtime is Runtime.CALL_BY_NEED:
        raise NotImplementedError("the call-by-need target is a module, not an expression option")
    raise ValueError("the interpret target is not compiled; compile call-by-value or call-by-name")


def runtime_globals(runtime: Runtime) -> dict:
    """The evaluation globals for a compiled program under the given runtime.

    Call-by-value source is self-contained; call-by-name source needs ``force`` and the
    recompute-on-force ``Thunk``; call-by-need needs the memo-cell sentinel.
    """
    if runtime is Runtime.CALL_BY_VALUE:
        return {}
    if runtime is Runtime.CALL_BY_NAME:
        return {"force": force, "Thunk": _LazyThunk}
    if runtime is Runtime.CALL_BY_NEED:
        return call_by_need_globals()
    raise ValueError("the interpret target is interpreted; it has no compiled runtime globals")


def compile_quoted(option, quoted) -> Node:
    """Run ``CODEGEN`` (at the given option) on a quoted source term, returning the Scott Python expr."""
    return build(app(app(app(CODEGEN, option), church(0)), quoted))


def _dedupe_lifted_factories(module: ast.AST) -> ast.Module:
    """Drop the byte-identical duplicate factory defs that lambda-lifted CODEGEN_NEED emits once per
    occurrence of a shared sub-term.

    Each distinct (depth, sub-term) is one top-level factory inside ``_program``; because the factories
    are lambda-lifted (every free variable arrives as a parameter, nothing is captured lexically), all
    copies of a name are structurally identical and one suffices. This collapses the per-occurrence
    unfolding (COMPILE shares ~19x) back to one def per distinct sub-term. Run before
    ``fix_missing_locations`` so the structural equality check ignores positions.
    """
    assert isinstance(module, ast.Module), f"expected an ast.Module, got {type(module).__name__}"
    program_def, = [
        statement for statement in module.body
        if isinstance(statement, ast.FunctionDef) and statement.name == "_program"
    ]
    seen: "dict[str, ast.FunctionDef]" = {}
    deduped: "list[ast.stmt]" = []
    for statement in program_def.body:
        if isinstance(statement, ast.FunctionDef):
            kept = seen.get(statement.name)
            if kept is not None:
                assert kept is statement or ast.dump(kept) == ast.dump(statement), (
                    f"lambda-lifted factory {statement.name!r} has two non-identical definitions"
                )
                continue
            seen[statement.name] = statement
        deduped.append(statement)
    program_def.body = deduped
    return module


def _compile_need_source(node: Node) -> str:
    """Compile a term to the call-by-need module source (lambda-lifted memoising-thunk factories).

    CODEGEN_NEED emits the generic Scott ``ast.Module`` directly, decoded by the generic
    ``_pyast.decode``; the per-occurrence duplicate factories are dropped after decoding.
    """
    module = build(app(CODEGEN_NEED, quote(node)))
    _reset_gensym()  # fresh vg_<n> names per compile, so call-by-need output is reproducible
    with memoized_decode():  # decode each distinct factory once, not once per occurrence
        decoded = _dedupe_lifted_factories(decode(module))
    return ast.unparse(ast.fix_missing_locations(decoded))


def codegen(node: Node, runtime: Runtime = Runtime.CALL_BY_VALUE) -> str:
    """Run the ``CODEGEN``/``CODEGEN_NEED`` lambda terms to emit Python source for ``node`` under a
    compiled ``runtime``: the per-target in-process utility (the production entry is ``compile``).

    Call-by-value yields a strict expression; call-by-name yields the expression with the lambda
    term's ``force``/``Thunk`` wrapping; call-by-need yields a memoising-thunk module. Every target
    is built as the generic Scott ast and decoded by ``_pyast.decode``.
    """
    with recursion_headroom():
        if runtime is Runtime.CALL_BY_NEED:
            return _compile_need_source(node)
        compiled = compile_quoted(_option(runtime), quote(node))
        return ast.unparse(ast.fix_missing_locations(decode(compiled)))


# --- the one compiler: options encoded to the Scott union, COMPILE run, the result serialized -----

_ISLAND_DEPTH_SMALL = 8


@dataclass(frozen=True)
class SpecializedOption:
    """The default compiler option: emit locally-specialized Python with islands up to
    ``island_depth`` (a depth past the deepest sub-term admits every island)."""

    island_depth: int = _ISLAND_DEPTH_SMALL

    def scott(self):
        return curry(lambda specialized, whole, need: app(specialized, church(self.island_depth)))


@dataclass(frozen=True)
class WholeOption:
    """A compiler option for the whole-program targets (call-by-value / call-by-name expressions;
    the call-by-need memoising-thunk module)."""

    runtime: Runtime

    def scott(self):
        if self.runtime is Runtime.CALL_BY_NEED:
            return curry(lambda specialized, whole, need: need)
        return curry(lambda specialized, whole, need: app(whole, _option(self.runtime)))


CompileOption = "SpecializedOption | WholeOption"


def compile(node: Node, option: "SpecializedOption | WholeOption" = SpecializedOption()) -> str:
    """The one compiler. By default (``SpecializedOption``) it emits locally-specialized Python: a closed
    simply-typable whole term is a strict call-by-value expression, otherwise ``interpret(<reconstruction>)``
    with the maximal closed simply-typable sub-terms up to the island depth spliced as compiled by-value
    islands. ``WholeOption(runtime)`` selects a whole-program target (call-by-value or call-by-name
    expression; call-by-need memoising-thunk module). EVERY target is selected and generated by the one
    lambda term ``COMPILE``; Python only encodes the option, quotes, runs the interpreter, and serializes
    (the specialized output is a shared interpret-headed graph, serialized to A-normal form; a whole
    expression target unparses an expression; the need target unparses a module). The interpret "target"
    is not compiled: ``WholeOption(Runtime.INTERPRET)`` raises at option encoding.
    """
    def _run() -> str:
        result = build(app(app(COMPILE, option.scott()), quote(node)))
        if isinstance(option, SpecializedOption):
            return to_anf_source(result, "compiled_compiler")
        _reset_gensym()  # fresh vg_<n> names per compile (only the call-by-need module uses them)
        if isinstance(option, WholeOption) and option.runtime is Runtime.CALL_BY_NEED:
            with memoized_decode():  # decode each distinct factory once, then drop the duplicate copies
                decoded = _dedupe_lifted_factories(decode(result))
            return ast.unparse(ast.fix_missing_locations(decoded))
        return ast.unparse(ast.fix_missing_locations(decode(result)))

    return run_in_large_stack(_run)


# --- lambda-level verdict readers ------------------------------------------------------------------
# Each runs a pure-lambda certificate on the quoted term and reads the Church-boolean verdict back.

# The default step budget for the lambda-level normalization oracle. A normalizing term reaches its
# normal form well within a few hundred steps (the test corpus does); a non-normalizing term runs the
# whole budget before the conservative "needs fold" verdict. Raising it only ever turns more terms
# call-by-need (never unsound: exhaustion always falls back to interpret). Mirrored by the lambda-side
# ``_compile_term._LAZY_ISLAND_FUEL``.
DEFAULT_FUEL = 256


def is_closed(node: Node) -> bool:
    """Whether ``node`` is closed, decided by running the lambda-level ``IS_CLOSED`` analysis on it."""
    return interpret_boolean(build(app(IS_CLOSED, quote(node))))


def is_typable_lambda(node: Node) -> bool:
    """Whether ``node`` is simply typable, decided by running the lambda-level ``TYPABLE`` analysis.

    The verdict is computed by the interpreter from the quoted term, so the typability certificate that
    drives specialization is itself a lambda term, not Python code. This is the lambda port of
    ``is_typable`` (algorithm-W), which remains as the specification and the test oracle.
    """
    with recursion_headroom():
        return interpret_boolean(build(app(TYPABLE, quote(node))))


def typable_bu_lambda(node: Node) -> bool:
    """Whether ``node`` is simply typable, decided by the path-free bottom-up fold ``TYPABLE_BU``.

    ``PRINCIPAL`` types every distinct sub-term once (the interpreter tables it, since it is path-free)
    and reconciles locally per application, so it shares work across the term DAG that the state-
    threading ``TYPABLE`` cannot. This is the certificate the island specializer consults;
    ``is_typable`` remains the oracle it is checked against.
    """
    with recursion_headroom():
        return interpret_boolean(build(app(TYPABLE_BU, quote(node))))


def normalizes_lambda(node: Node, fuel: int = DEFAULT_FUEL) -> bool:
    """Whether ``node`` has a finite normal form, decided by the lambda-level bounded normalizer.

    Runs ``NORMALIZES`` at ``fuel`` (a BinNat step budget) on the quoted term: ``True`` means a finite
    normal form was positively observed within the fuel (call-by-need safe); ``False`` means the fuel
    ran out, read conservatively as needs-fold (interpret). This is the pure-lambda port of
    ``needs_folding`` (whose verdict is its complement). The normalization runs in a large-stack
    thread because a non-normalizing term drives the interpreter as deep as the fuel.
    """
    return run_in_large_stack(
        lambda: interpret_boolean(build(app(app(NORMALIZES, int_to_binnat(fuel)), quote(node)))),
    )


_RUNTIME_TAGS: "tuple[Runtime, ...]" = (Runtime.CALL_BY_VALUE, Runtime.CALL_BY_NEED, Runtime.INTERPRET)


def choose_runtime(node: Node, fuel: int = DEFAULT_FUEL) -> Runtime:
    """The fastest runtime certified to preserve ``node``'s interpreted behaviour, decided by lambda.

    Runs ``CHOOSE_RUNTIME`` on the quoted term and reads its Church-numeral tag: call-by-value if closed
    and simply typable (strongly normalizing); else call-by-need if a finite normal form is observed
    within ``fuel`` (normalizing, so the lazy regime is viable and call-by-need shares); else interpret.
    The decision is the lambda term; Python only reads the tag back as a ``Runtime`` label. Call-by-name
    is never selected even where viable: call-by-need is preferred for its sharing.
    """
    tag = run_in_large_stack(
        lambda: _church_to_int(build(app(app(CHOOSE_RUNTIME, int_to_binnat(fuel)), quote(node)))),
    )
    return _RUNTIME_TAGS[tag]


def specialize(node: Node) -> tuple[Runtime, str | None]:
    """Specialize ``node`` to its certified runtime.

    Returns the chosen runtime and, for the compiled targets, the compiled Python source. The
    interpret target returns ``None`` source: the fixpoint-thunk graph is the AST, so the interpreter
    is the compilation.
    """
    runtime = choose_runtime(node)
    if runtime is Runtime.INTERPRET:
        return runtime, None
    return runtime, codegen(node, runtime)


# --- compile once, run many: a reusable compiled function fed lambda-term inputs (FFI utilities) ---
# A solution written in the lambda-calculus is compiled ONCE to a Python callable; the Python side
# then feeds it many lambda-term inputs. Inputs and outputs stay lambda values (no Python-domain
# marshalling).


def compile_callable(node: Node, runtime: Runtime) -> Callable:
    """Compile ``node`` ONCE to a Python callable under ``runtime``.

    Call-by-value source is strict and self-contained; call-by-name source refers to the free names
    ``force`` and ``Thunk`` supplied by ``runtime_globals``.
    """
    source = codegen(node, runtime)
    if runtime is Runtime.CALL_BY_VALUE:
        return eval(source)
    return eval(source, runtime_globals(runtime))


def host_value(node: Node, runtime: Runtime) -> object:
    """Compile a lambda-term input to its host (compiled) value under ``runtime``.

    The same operation as ``compile_callable``: a closed term's compiled value, ready to be applied
    to or by another compiled value of the same runtime.
    """
    return compile_callable(node, runtime)


def apply_compiled(function: object, argument: object, runtime: Runtime) -> object:
    """Apply a compiled ``function`` to a compiled ``argument`` under ``runtime``'s calling convention.

    Call-by-value passes the argument directly; call-by-name passes it as a thunk, since the compiled
    body forces its variables.
    """
    if runtime is Runtime.CALL_BY_VALUE:
        return function(argument)  # type: ignore[operator]
    thunk = runtime_globals(runtime)["Thunk"]
    return function(thunk(lambda: argument))  # type: ignore[operator]


def compile_solution(node: Node, runtime: Runtime | None = None) -> Callable[..., object]:
    """Compile a reusable lambda function ONCE; return ``solve(*input_nodes)`` applying it to its
    inputs.

    ``runtime`` defaults to call-by-value if the solution is simply typable (strongly normalizing),
    else call-by-name. ``solve`` compiles each input term to a host value (cheap; the solution is the
    expensive part, compiled once) and applies the function under the runtime's calling convention,
    returning the host lambda value.
    """
    if runtime is None:
        runtime = Runtime.CALL_BY_VALUE if is_typable(node) else Runtime.CALL_BY_NAME
    chosen = runtime
    function = compile_callable(node, chosen)

    def solve(*argument_nodes: Node) -> object:
        result = function
        for argument_node in argument_nodes:
            result = apply_compiled(result, host_value(argument_node, chosen), chosen)
        return result

    return solve


# --- local specialization FFI: a compiled island embedded in an interpreted graph -----------------


def value_island(node: Node) -> Native:
    """Wrap a CLOSED, simply-typable (strongly normalizing) term as a compiled by-value ``Native``
    island.

    The term is compiled once to strict Python and run; its normal form is reified to a PURE Scott
    node by NbE read-back (``_runtime.value_island``), so the island composes with the interpreter
    through the node graph and the generic decoder reads it. Faithfulness is convergence to the same
    value, not structural identity.
    """
    if node.loose_bound != 0:
        raise ValueError("value_island requires a closed term")
    return _runtime_value_island(compile_callable(node, Runtime.CALL_BY_VALUE))


def lazy_island(node: Node, lazy_runtime: Runtime = Runtime.CALL_BY_NEED) -> Native:
    """Wrap a CLOSED term with a FINITE NORMAL FORM (a terminating Y recursion) as a compiled lazy
    island.

    Compiled by the call-by-name codegen (an expression, so it splices like a by-value island) and
    read back by the fuel-bounded ``_runtime.value_island_by_name``. The ``lazy_runtime`` option
    chooses the thunk semantics, the same codegen either way: ``CALL_BY_NEED`` (default) memoises,
    the efficient choice for a recursion that reuses sub-terms; ``CALL_BY_NAME`` recomputes on every
    force, which a reuse-heavy term makes exponential, so it is only for comparison.

    Soundness restriction: the lazy read-back reifies a value by forcing it and probing a function
    under a fresh binder, which terminates exactly when the term reaches a finite normal form. A
    closed term WITHOUT a finite normal form (a bare recursive function such as ``FACTORIAL``, whose
    behaviour folds rather than terminating) would drive that probe into the live recursion and
    diverge, so it is rejected here and left for the interpreter, which folds the cycle via lfp
    tabling. ``needs_folding`` is the existing sound oracle for "no finite normal form".
    """
    if node.loose_bound != 0:
        raise ValueError("lazy_island requires a closed term")
    if needs_folding(node):
        raise ValueError(
            "lazy_island requires a term with a finite normal form; this term's behaviour folds "
            "(no finite normal form), so it must stay interpreted rather than become a lazy island"
        )
    if lazy_runtime not in (Runtime.CALL_BY_NAME, Runtime.CALL_BY_NEED):
        raise ValueError("a lazy island is call-by-name or call-by-need")
    source = codegen(node, Runtime.CALL_BY_NAME)
    thunk = _NeedThunk if lazy_runtime is Runtime.CALL_BY_NEED else _LazyThunk
    value = eval(source, {"force": force, "Thunk": thunk})  # noqa: S307 - our own generated source
    return _runtime_value_island_by_name(value)


# === Python specifications and test oracles (off the lambda production path) ======================


@dataclass(frozen=True)
class _TVar:
    """A type variable, identified by a fresh integer."""

    id: int


@dataclass(frozen=True)
class _TArrow:
    """A function type ``left -> right``."""

    left: "_Type"
    right: "_Type"


_Type = "_TVar | _TArrow"


class _Inference:
    """Algorithm-W style simple-type inference over de Bruijn terms.

    No generalization (STLC, not Hindley-Milner): each binder gets one fresh monotype. Unification
    uses an occurs check, so the self-application ``x x`` (whose constraint is ``α = α -> β``) fails,
    which is exactly why ``Y``/``Ω`` and the recursive terms built on them are untypable.
    Failure is recorded in ``failed`` rather than raised, so the caller reads a plain boolean.
    """

    def __init__(self) -> None:
        self._next = 0
        self._substitution: dict[int, _Type] = {}
        self.failed = False

    def _fresh(self) -> _TVar:
        variable = _TVar(self._next)
        self._next += 1
        return variable

    def _resolve(self, type_: _Type) -> _Type:
        while isinstance(type_, _TVar) and type_.id in self._substitution:
            type_ = self._substitution[type_.id]
        return type_

    def _occurs(self, variable_id: int, type_: _Type) -> bool:
        type_ = self._resolve(type_)
        if isinstance(type_, _TVar):
            return type_.id == variable_id
        return self._occurs(variable_id, type_.left) or self._occurs(variable_id, type_.right)

    def _unify(self, left: _Type, right: _Type) -> None:
        if self.failed:
            return
        left = self._resolve(left)
        right = self._resolve(right)
        if isinstance(left, _TVar) and isinstance(right, _TVar) and left.id == right.id:
            return
        if isinstance(left, _TVar):
            if self._occurs(left.id, right):
                self.failed = True
                return
            self._substitution[left.id] = right
            return
        if isinstance(right, _TVar):
            if self._occurs(right.id, left):
                self.failed = True
                return
            self._substitution[right.id] = left
            return
        self._unify(left.left, right.left)
        self._unify(left.right, right.right)

    def infer(self, node: Node, context: tuple[_Type, ...]) -> _Type:
        """Infer ``node``'s type under ``context`` (``context[i]`` is the type of ``Var(i)``)."""
        if self.failed:
            return self._fresh()
        match node:
            case Var(index=index):
                if index >= len(context):
                    # A free variable stands for an unconstrained external binding; closed terms,
                    # which is what we specialize, never reach this.
                    return self._fresh()
                return context[index]
            case Lam(body=body):
                parameter = self._fresh()
                result = self.infer(body, (parameter, *context))
                return _TArrow(parameter, result)
            case App(function=function, argument=argument):
                function_type = self.infer(function, context)
                argument_type = self.infer(argument, context)
                result = self._fresh()
                self._unify(function_type, _TArrow(argument_type, result))
                return result
            case _:
                raise TypeError(f"Unknown node {node!r}")


def is_typable(node: Node) -> bool:
    """Whether ``node`` is simply typable, a sound certificate of strong normalization.

    A simply-typed term is strongly normalizing, so the strict call-by-value runtime terminates with
    the interpreter's normal form. This is sound but conservative: an untypable term may still
    normalize (factorial does), so untypability only means call-by-value is not certified, not unsafe.
    """
    inference = _Inference()
    with recursion_headroom():
        inference.infer(node, ())
    return not inference.failed


# The fold oracle reads the behaviour out under two bounds. A finite normal form fits well within them
# (a Church numeral is a short spine); a non-rational behaviour (the open inner structure of a fixpoint
# combinator, e.g. the compiler's Y, which never folds) is infinite, so a branch past the bounds
# truncates to a ``…`` leaf, read as fold-requiring. ``_FOLD_ORACLE_DEPTH`` caps the rendering recursion
# depth well under the interpreter's stack limit; ``_FOLD_ORACLE_NODES`` caps total work, since the
# behaviour tree branches. Conservative past either (a bigger normal form is left interpreted, never
# miscompiled).
_FOLD_ORACLE_DEPTH = 400
_FOLD_ORACLE_NODES = 50_000


def needs_folding(node: Node) -> bool:
    """Whether reading ``node``'s behaviour needs the fixpoint fold (so it is not a finite normal form).

    The interpreter is a sound oracle: it folds a cycle to a back-reference ``#`` (or ``⊥`` for an
    unproductive cycle). A behaviour rendered in full with neither marker is a finite normal form, so
    the term is normalizing and the call-by-need runtime, which never folds, reaches the same value.
    Reading is bounded in depth and node count: a non-rational behaviour truncates to ``…``, which
    counts as fold-requiring, so call-by-need is chosen only when a complete finite normal form was
    positively observed. Normalization is undecidable; the bounded read is the pragmatic sound test.
    """
    behaviour = render(node, budget=_FOLD_ORACLE_DEPTH, max_nodes=_FOLD_ORACLE_NODES)
    return "#" in behaviour or "⊥" in behaviour or "…" in behaviour


def call_by_value_islands(node: Node) -> tuple[Node, ...]:
    """The maximal closed, simply-typable sub-terms of ``node``: its call-by-value islands.

    A sub-term that is closed (no free variable) and simply typable is strongly normalizing, so strict
    evaluation reaches the interpreter's normal form: it is a sound call-by-value island. ``Maximal``
    means not contained in a larger such sub-term, so the result is the largest strict regions, not
    every typable leaf. Scanning is top-down: a found island is not descended into. The complement,
    the untypable skeleton (e.g. the ``Y`` fixpoint of the compiler), stays interpreted. Islands are
    distinct by node identity, so a combinator the interning shares across positions is reported once.
    This Python scan is the specification mirror of the lambda-level island certificate in
    ``_compile_term``.
    """
    found: list[Node] = []
    seen: set[int] = set()

    def visit(current: Node) -> None:
        if current.loose_bound == 0 and is_typable(current):
            if id(current) not in seen:
                seen.add(id(current))
                found.append(current)
            return
        match current:
            case Var():
                return
            case Lam(body=body):
                visit(body)
            case App(function=function, argument=argument):
                visit(function)
                visit(argument)
            case Native():
                return
            case _:
                raise TypeError(f"cannot scan {current!r}")

    with recursion_headroom():
        visit(node)
    return tuple(found)


# --- the interpret-target reconstruction, in Python (specification/test oracle) -------------------
# A term the analysis does not certify for a compiled target keeps the interpreter. Its compiled
# Python is an ``interpret(...)`` call whose argument reconstructs the term as an interpreter ``Node``
# with ``make_var`` / ``make_lam`` / ``make_app`` (the interning constructors). This Python
# reconstruction mirrors the lambda-level ``_compile_term._reconstruct``; the production path is the
# lambda term, this is the oracle the tests compare against.


def _node_to_ast(node: Node, islands: "frozenset[int]") -> ast.expr:
    """Reconstruct ``node`` as Python that rebuilds the interpreter ``Node`` with ``make_*``.

    A node whose identity is in ``islands`` is a certified by-value island: rather than reconstructing
    its subtree, splice ``value_island(<the island compiled to call-by-value>)``, an FFI ``Native`` the
    interpreter drives in place of interpreting the subtree.
    """
    if id(node) in islands:
        compiled = ast.parse(codegen(node, Runtime.CALL_BY_VALUE), mode="eval").body
        return ast.Call(func=ast.Name(id="value_island", ctx=ast.Load()), args=[compiled], keywords=[])
    match node:
        case Var(index=index):
            return ast.Call(
                func=ast.Name(id="make_var", ctx=ast.Load()),
                args=[ast.Constant(value=index)], keywords=[],
            )
        case Lam(body=body):
            return ast.Call(
                func=ast.Name(id="make_lam", ctx=ast.Load()), args=[_node_to_ast(body, islands)],
                keywords=[],
            )
        case App(function=function, argument=argument):
            return ast.Call(
                func=ast.Name(id="make_app", ctx=ast.Load()),
                args=[_node_to_ast(function, islands), _node_to_ast(argument, islands)], keywords=[],
            )
        case _:
            raise ValueError(f"cannot reconstruct {node!r}")


def compile_interpreted(node: Node, islands: "frozenset[int] | None" = None) -> str:
    """Compile ``node`` to interpret-headed Python: ``interpret(<node reconstructed with make_*>)``.

    Sub-nodes whose identity is in ``islands`` are spliced as ``value_island(...)`` compiled islands
    rather than reconstructed, so they run compiled inside the interpreted skeleton. This nests
    deeply for a large term; for a standalone module use ``compile_interpreted_module``.
    """
    call = ast.Call(
        func=ast.Name(id="interpret", ctx=ast.Load()),
        args=[_node_to_ast(node, islands if islands is not None else frozenset())], keywords=[],
    )
    return ast.unparse(ast.fix_missing_locations(call))


def compile_interpreted_module(node: Node, islands: "frozenset[int] | None" = None) -> str:
    """Compile ``node`` to an interpret-headed Python MODULE in A-normal form.

    The nested ``interpret(make_...(...))`` reconstruction grows as deep as the term, which overflows
    CPython's fixed parser nesting cap for a large term like the compiler itself. This emits the same
    reconstruction flattened to a statement sequence binding one temporary per node (shared by node
    identity, so interned sub-terms are built once), ending in
    ``compiled_compiler = interpret(<root temp>)``.
    """
    island_set = islands if islands is not None else frozenset()
    statements: "list[ast.stmt]" = []
    names: "dict[int, str]" = {}

    def emit(current: Node) -> str:
        if id(current) in names:
            return names[id(current)]
        if id(current) in island_set:
            compiled = ast.parse(codegen(current, Runtime.CALL_BY_VALUE), mode="eval").body
            value: ast.expr = ast.Call(
                func=ast.Name(id="value_island", ctx=ast.Load()), args=[compiled], keywords=[],
            )
        else:
            match current:
                case Var(index=index):
                    value = ast.Call(
                        func=ast.Name(id="make_var", ctx=ast.Load()),
                        args=[ast.Constant(value=index)], keywords=[],
                    )
                case Lam(body=body):
                    value = ast.Call(
                        func=ast.Name(id="make_lam", ctx=ast.Load()),
                        args=[ast.Name(id=emit(body), ctx=ast.Load())], keywords=[],
                    )
                case App(function=function, argument=argument):
                    value = ast.Call(
                        func=ast.Name(id="make_app", ctx=ast.Load()),
                        args=[
                            ast.Name(id=emit(function), ctx=ast.Load()),
                            ast.Name(id=emit(argument), ctx=ast.Load()),
                        ], keywords=[],
                    )
                case _:
                    raise ValueError(f"cannot reconstruct {current!r}")
        name = f"_{len(names)}"
        statements.append(ast.Assign(targets=[ast.Name(id=name, ctx=ast.Store())], value=value))
        names[id(current)] = name
        return name

    with recursion_headroom():
        root = emit(node)
        statements.append(ast.Assign(
            targets=[ast.Name(id="compiled_compiler", ctx=ast.Store())],
            value=ast.Call(
                func=ast.Name(id="interpret", ctx=ast.Load()),
                args=[ast.Name(id=root, ctx=ast.Load())], keywords=[],
            ),
        ))
        return ast.unparse(ast.fix_missing_locations(ast.Module(body=statements, type_ignores=[])))


def compiled_compiler() -> Node:
    """The self-hosted code generator as an interpreter ``Node``: CODEGEN handed back to the
    interpreter.

    CODEGEN is untypable (its Y fixpoint self-applies), so the interpret target is the CODEGEN node
    itself; ``compile_with_interpreted`` runs it as a compiler. In process, the node IS the
    self-compiled compiler. (The committed self-hosted compilers are the staged compilers in this
    package's ``_generated_stages`` directory, the COMPILE term compiled at each island depth and
    serialized to A-normal form by the multi-stage bootstrap.)
    """
    return build(CODEGEN)


def compile_with_interpreted(compiler_node: Node, node: Node, runtime: Runtime = Runtime.CALL_BY_VALUE) -> str:
    """Compile ``node`` with an interpret-headed compiler, a ``CODEGEN`` ``Node`` run by the interpreter.

    ``compiler_node`` is what ``compile_interpreted(build(CODEGEN))`` evaluates to: the compiler itself,
    handed back to the interpreter. The interpreter applies it to the option, the zero binder depth,
    and the quoted program, and the resulting generic Scott Python AST is decoded by the same generic
    ``_pyast.decode`` the in-process compiler uses. So the self-hosted compiler, compiled to
    interpret-headed Python, compiles any program to the same source as ``codegen``: the
    bootstrap through the interpret target.
    """
    with recursion_headroom():
        applied = compiler_node(
            build(_option(runtime)), build(church(0)), build(quote(node)),
        )
        return ast.unparse(ast.fix_missing_locations(decode(applied)))
