"""Analysis-driven specialization: interpret by default, compile to Python only when sound.

The interpreter is the default. A ``Node``'s ``weak_head_normal_form`` is a
``fixpoint_cached_property`` thunk, interned and possibly cyclic, so the term graph already *is*
a fixpoint-thunk graph the interpreter folds; handing that graph back is the identity. The only
compilations that change anything are the two that pick a different evaluation strategy, EAGER
(strict, call-by-value) and LAZY (call-by-name), and they preserve the interpreter's result only
under conditions a static analysis can certify:

- ``is_typable`` decides simple typability (STLC, algorithm-W style). A simply-typed term is
  strongly normalizing, so strict evaluation terminates with the same normal form: EAGER is safe.
- ``needs_folding`` consults the interpreter as a sound oracle: it reads the behaviour out and
  checks whether the fixpoint fold was used (a back-reference ``#`` or the ``⊥`` leaf). If the
  behaviour is a finite normal form, the term is normalizing and LAZY (which recomputes, never
  folds) reaches the same value.

``choose_runtime`` layers these: EAGER if typable; else LAZY if the behaviour is a finite normal
form; else FIXPOINT, meaning leave the sub-term to the interpreter, which always folds correctly.
This is a partial evaluator with a soundness analysis and the interpreter as the fixpoint fallback;
no totality is claimed, and anything not certified stays interpreted.
"""

from __future__ import annotations

from dataclasses import dataclass

from first_order_lambda._ast import App, Lam, Node, Var
from first_order_lambda._compiler import Runtime, compile_to_source
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

    A simply-typed term is strongly normalizing, so the strict EAGER runtime terminates with the
    interpreter's normal form. This is sound but conservative: an untypable term may still
    normalize (factorial does), so untypability only means EAGER is not certified, not unsafe.
    """
    inference = _Inference()
    inference.infer(node, ())
    return not inference.failed


def needs_folding(node: Node) -> bool:
    """Whether the interpreter used the fixpoint fold to read ``node``'s behaviour.

    The interpreter is a sound oracle: it always terminates on rational behaviour and folds cycles
    to a back-reference ``#`` (or ``⊥`` for an unproductive cycle). A behaviour with neither marker
    is a finite normal form, so the term is normalizing and the LAZY runtime, which recomputes and
    never folds, reaches the same value. Normalization is undecidable in general; running the safe
    interpreter and reading off whether it folded is the pragmatic sound test.
    """
    behaviour = render(node)
    return "#" in behaviour or "⊥" in behaviour


def choose_runtime(node: Node) -> Runtime:
    """The fastest runtime certified to preserve ``node``'s interpreted behaviour.

    EAGER if simply typable (strongly normalizing); else LAZY if the behaviour is a finite normal
    form (normalizing); else FIXPOINT, meaning leave it to the interpreter, which folds correctly.
    """
    if is_typable(node):
        return Runtime.EAGER
    if not needs_folding(node):
        return Runtime.LAZY
    return Runtime.FIXPOINT


def specialize(node: Node) -> tuple[Runtime, str | None]:
    """Specialize ``node`` to its certified runtime.

    Returns the chosen runtime and, for EAGER/LAZY, the compiled Python source. FIXPOINT returns
    ``None`` source, meaning "interpret": the fixpoint-thunk graph is the AST, so the interpreter
    is the compilation.
    """
    runtime = choose_runtime(node)
    if runtime is Runtime.FIXPOINT:
        return runtime, None
    return runtime, compile_to_source(node, runtime)
