"""Analysis-driven specialization: interpret by default, compile to Python only when sound.

The interpreter is the default. A ``Node``'s ``weak_head_normal_form`` is a
``fixpoint_cached_property`` thunk, interned and possibly cyclic, so the term graph already *is*
a fixpoint-thunk graph the interpreter folds; handing that graph back is the identity. The only
compilations that change anything are the two that pick a different evaluation strategy, call-by-value
(strict) and call-by-name, and they preserve the interpreter's result only under conditions a static
analysis can certify:

- ``is_typable`` decides simple typability (STLC, algorithm-W style). A simply-typed term is
  strongly normalizing, so strict evaluation terminates with the same normal form: call-by-value is
  safe.
- ``needs_folding`` consults the interpreter as a sound oracle: it reads the behaviour out and
  checks whether the fixpoint fold was used (a back-reference ``#`` or the ``⊥`` leaf). If the
  behaviour is a finite normal form, the term is normalizing and call-by-name (which recomputes,
  never folds) reaches the same value.

``choose_runtime`` layers these: call-by-value if typable; else call-by-name if the behaviour is a
finite normal form; else interpret, meaning leave the sub-term to the interpreter, which always folds
correctly. This is a partial evaluator with a soundness analysis and the interpreter as the fixpoint
fallback; no totality is claimed, and anything not certified stays interpreted.
"""

from __future__ import annotations

from dataclasses import dataclass

from typing import Callable

from first_order_lambda._analysis import CLOSED
from first_order_lambda._ast import App, Lam, Native, Node, Var
from first_order_lambda._binnat import int_to_binnat
from first_order_lambda._compiler import (
    Runtime,
    _recursion_headroom,
    compile_interpreted,
    compile_to_source,
    quote,
    runtime_globals,
    value_island as _compiler_value_island,
)
from first_order_lambda._dsl import app, build, lam
from first_order_lambda._prelude import AND, church
from first_order_lambda._pyast import _church_to_int
from first_order_lambda._reduce import DEFAULT_FUEL, NORMALIZES, run_in_large_stack
from first_order_lambda._render import render
from first_order_lambda._typecheck import TYPABLE


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
    which is exactly why ``Y``/``Z``/``Ω`` and the recursive terms built on them are untypable.
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
    with _recursion_headroom():
        inference.infer(node, ())
    return not inference.failed


# The fold oracle reads the behaviour out under two bounds. A finite normal form fits well within them
# (a Church numeral is a short spine); a non-rational behaviour (the open inner structure of a fixpoint
# combinator, e.g. the compiler's Z, which never folds) is infinite, so a branch past the bounds
# truncates to a ``…`` leaf, read as fold-requiring. ``_FOLD_ORACLE_DEPTH`` caps the rendering recursion
# depth well under the interpreter's stack limit (a leaf also walks the node for ``loose_bound`` and its
# weak head normal form, which recurse to a comparable depth); ``_FOLD_ORACLE_NODES`` caps total work,
# since the behaviour tree branches. Conservative past either (a bigger normal form is left interpreted,
# never miscompiled).
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


# CHOOSE_RUNTIME fuel quoted: the runtime tag (a Church numeral) certified to preserve the term's
# interpreted behaviour, by the fixed priority of H'. Closed and simply typable -> call-by-value (tag 0,
# strongly normalizing so strict is safe); else a finite normal form within the fuel -> call-by-need
# (tag 1, the lazy regime is viable and call-by-need shares); else interpret (tag 2). The Church if is
# lazy, so the expensive NORMALIZES branch is only reached for an untypable term. The whole decision is
# the lambda term; Python only reads the tag back as a Runtime label.
_RUNTIME_TAGS: "tuple[Runtime, ...]" = (Runtime.CALL_BY_VALUE, Runtime.CALL_BY_NEED, Runtime.INTERPRET)

CHOOSE_RUNTIME: "object" = lam(lambda fuel: lam(lambda quoted: app(app(
    app(app(AND, app(app(CLOSED, church(0)), quoted)), app(TYPABLE, quoted)),
    church(0),
    ),
    app(app(
        app(app(NORMALIZES, fuel), quoted),
        church(1),
        ),
        church(2),
    ),
)))


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
    return runtime, compile_to_source(node, runtime)


def compile_specialized(node: Node) -> str:
    """Compile ``node`` in specialized mode, always returning Python.

    The head is non-interpreter code when the whole graph carries the by-value certificate (closed and
    simply typable, hence strongly normalizing, so strict evaluation reaches the interpreter's normal
    form); otherwise it is an ``interpret(...)`` call that re-submits the term to the interpreter, with
    its maximal closed simply-typable sub-terms spliced as compiled by-value islands (run, then reified
    to a pure node by NbE read-back). This is the compiler in the sense the paper means: interpret by
    default, compile the certified parts; the island reify is church-agnostic, not type-classified.
    """
    if node.loose_bound == 0 and is_typable(node):
        return compile_to_source(node, Runtime.CALL_BY_VALUE)
    islands = frozenset(id(island) for island in call_by_value_islands(node))
    return compile_interpreted(node, islands)


# --- finding call-by-value islands: the maximal certified-strict regions of a program -----------
# The flagship of local specialization. A whole untypable program (a Y/Z recursion, the compiler
# itself) is not call-by-value as a whole, but it contains closed simply-typable sub-terms, each
# strongly normalizing, so each compiles soundly to a strict call-by-value island. The specializer
# carves out the MAXIMAL such regions and leaves the untypable skeleton interpreted; the islands are
# where the strict compiled code runs, the skeleton is where the interpreter folds.


def call_by_value_islands(node: Node) -> tuple[Node, ...]:
    """The maximal closed, simply-typable sub-terms of ``node``: its call-by-value islands.

    A sub-term that is closed (no free variable) and simply typable is strongly normalizing, so strict
    evaluation reaches the interpreter's normal form: it is a sound call-by-value island. ``Maximal``
    means not contained in a larger such sub-term, so the result is the largest strict regions, not
    every typable leaf. Scanning is top-down: a found island is not descended into. The complement,
    the untypable skeleton (e.g. the ``Z`` fixpoint of the compiler), stays interpreted. Islands are
    distinct by node identity, so a combinator the interning shares across positions is reported once.
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

    with _recursion_headroom():
        visit(node)
    return tuple(found)


# --- compile once, run many: a reusable compiled function fed lambda-term inputs ----------------
# A solution written in the lambda-calculus is compiled ONCE to a Python callable; the Python side
# then feeds it many lambda-term inputs. Inputs and outputs stay lambda values (no Python-domain
# marshalling): an input term is compiled to its host value under the same runtime and applied, and
# the result is the host lambda value, which the caller observes however it likes. Call-by-value is
# chosen for a simply-typed (strongly normalizing) solution, otherwise call-by-name: it is faithful on
# every terminating application (it reaches the unique fixpoint, the denotation, rather than
# diverging), which is exactly the regime of concrete test inputs.


def compile_callable(node: Node, runtime: Runtime) -> Callable:
    """Compile ``node`` ONCE to a Python callable under ``runtime``.

    Call-by-value source is strict and self-contained; call-by-name source refers to the free names
    ``force`` and ``Thunk`` supplied by ``runtime_globals``.
    """
    source = compile_to_source(node, runtime)
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
    returning the host lambda value. The function is never classed interpret here: the caller is
    asserting it is a function to be applied, and call-by-name converges on every terminating
    application.
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


# --- local specialization: a compiled island embedded in an interpreted graph -------------------
# A closed compilable sub-term is wrapped as a Native (FFI) node, compiled once. Embedded in an
# otherwise interpreted graph (e.g. inside a fold-requiring cyclic shell), the interpreter drives
# the island and folds around it, so the program is neither all-interpreted nor all-compiled. The
# boundary reifies the island's result back to a node; faithfulness is convergence to the unique
# fixpoint, not structural identity, so the canonical reified shape is sound.


def value_island(node: Node) -> Native:
    """Wrap a CLOSED, simply-typable (strongly normalizing) term as a compiled by-value ``Native`` island.

    The term is compiled once to strict Python and run; its normal form is reified to a PURE Scott node
    by NbE read-back (``_compiler.value_island``), so the island composes with the interpreter through
    the node graph and the generic decoder reads it. The reify is church-agnostic (it reifies a Church
    numeral, a Scott value, or a function alike); faithfulness is convergence to the same value, not
    structural identity.
    """
    if node.loose_bound != 0:
        raise ValueError("value_island requires a closed term")
    return _compiler_value_island(compile_callable(node, Runtime.CALL_BY_VALUE))
