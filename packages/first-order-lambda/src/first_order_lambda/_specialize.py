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

from first_order_lambda._ast import App, Lam, Native, Node, Var, make_native
from first_order_lambda._compiler import Runtime, compile_to_source, runtime_globals
from first_order_lambda._dsl import build
from first_order_lambda._prelude import church
from first_order_lambda._render import render


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
    inference.infer(node, ())
    return not inference.failed


def needs_folding(node: Node) -> bool:
    """Whether the interpreter used the fixpoint fold to read ``node``'s behaviour.

    The interpreter is a sound oracle: it always terminates on rational behaviour and folds cycles
    to a back-reference ``#`` (or ``⊥`` for an unproductive cycle). A behaviour with neither marker
    is a finite normal form, so the term is normalizing and the call-by-name runtime, which recomputes
    and never folds, reaches the same value. Normalization is undecidable in general; running the safe
    interpreter and reading off whether it folded is the pragmatic sound test.
    """
    behaviour = render(node)
    return "#" in behaviour or "⊥" in behaviour


def choose_runtime(node: Node) -> Runtime:
    """The fastest runtime certified to preserve ``node``'s interpreted behaviour.

    Call-by-value if simply typable (strongly normalizing); else call-by-need if the behaviour is a
    finite normal form (normalizing); else interpret, leaving it to the interpreter, which folds
    correctly. Call-by-need, not call-by-name, is the lazy choice: it computes the same values and
    terminates in the same cases (memoisation is referentially transparent in a pure calculus) and
    only ever shares work, so call-by-name is never needed for correctness and the specializer never
    picks it.
    """
    if is_typable(node):
        return Runtime.CALL_BY_VALUE
    if not needs_folding(node):
        return Runtime.CALL_BY_NEED
    return Runtime.INTERPRET


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


def _decode_church_host(value: object, runtime: Runtime) -> int:
    if runtime is Runtime.CALL_BY_VALUE:
        return value(lambda predecessor: predecessor + 1)(0)  # type: ignore[operator]
    globals_ = runtime_globals(runtime)
    thunk, force = globals_["Thunk"], globals_["force"]
    successor = lambda counted: force(counted) + 1
    return value(thunk(lambda: successor))(thunk(lambda: 0))  # type: ignore[operator]


def church_island(node: Node, runtime: Runtime | None = None) -> Native:
    """Wrap a CLOSED, Church-numeral-producing term as a compiled ``Native`` island (arity 0).

    The term is compiled once; the island's ``run`` evaluates it and reifies the result Church
    numeral back to a node, so the island composes with the interpreter through the Node graph. The
    runtime defaults to call-by-value when the term is simply typable, else call-by-name.
    """
    if node.loose_bound != 0:
        raise ValueError("church_island requires a closed term")
    chosen = runtime if runtime is not None else (Runtime.CALL_BY_VALUE if is_typable(node) else Runtime.CALL_BY_NAME)
    compiled = compile_callable(node, chosen)

    def run() -> Node:
        return build(church(_decode_church_host(compiled, chosen)))

    return make_native(run, 0)
