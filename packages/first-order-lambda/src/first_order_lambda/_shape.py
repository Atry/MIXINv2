"""Weak head normalization: the structure map ``out`` of the lambda-calculus coalgebra.

``weak_head_normalize`` exposes a node's outermost constructor after weak head reduction (it stops
at the outermost constructor and does not reduce under ``lambda``). A deterministic calculus
exposes exactly one constructor at a node, so the value is a single shape
(``VarShape``/``LamShape``/``AppShape``) or ``BOTTOM`` (no constructor), never a set.
``compute_weak_head_normal_form`` is the per-node clause body; ``Node.weak_head_normal_form`` wraps
it in a ``fixpoint_cached_property`` resolved as a least fixpoint from ``BOTTOM`` upward. Because
nodes are interned, a node reached again during its own computation is caught by a pointer test; an
unproductive cycle (a re-entry with no constructor exposed, as in ``Omega`` or ``Y (lambda x. x)``)
stabilizes at ``BOTTOM``.

A reduction budget (a context variable) bounds beta-reduction so a genuinely non-rational reduction
surfaces as ``ReductionBudgetExceeded`` instead of hanging.
"""

from __future__ import annotations

from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass, field
from typing import Iterator, cast, final

from first_order_lambda._ast import (
    BOTTOM,
    App,
    Lam,
    Node,
    ShapeBottom,
    Var,
    substitute,
)


@final
@dataclass(kw_only=True, slots=True, frozen=True, weakref_slot=True)
class VarShape:
    index: int


@final
@dataclass(kw_only=True, slots=True, frozen=True, weakref_slot=True)
class LamShape:
    body: Node


@final
@dataclass(kw_only=True, slots=True, frozen=True, weakref_slot=True)
class AppShape:
    function: Node
    argument: Node


Shape = VarShape | LamShape | AppShape


class ReductionBudgetExceeded(RuntimeError):
    """Raised when a bounded reduction runs out of beta-steps (a divergent term)."""


@final
@dataclass(kw_only=True, slots=True, weakref_slot=True)
class _Budget:
    remaining: int = field(default=0)


_reduction_budget: ContextVar[_Budget | None] = ContextVar(
    "first_order_lambda._reduction_budget", default=None
)


@contextmanager
def reduction_budget(steps: int) -> Iterator[None]:
    """Bound beta-reduction to ``steps`` head redexes within this context."""
    if steps <= 0:
        raise ValueError("reduction budget must be positive")
    token = _reduction_budget.set(_Budget(remaining=steps))
    try:
        yield
    finally:
        _reduction_budget.reset(token)


def _consume_redex() -> None:
    budget = _reduction_budget.get()
    if budget is None:
        return
    if budget.remaining <= 0:
        raise ReductionBudgetExceeded("reduction budget exhausted")
    budget.remaining -= 1


def weak_head_normalize(node: Node) -> Shape | ShapeBottom:
    """The weak head normal form of ``node``: its outermost constructor, or ``BOTTOM`` (none).

    Typed via ``Node.weak_head_normal_form`` (a ``fixpoint_cached_property`` typed as ``object``).
    """
    return cast("Shape | ShapeBottom", node.weak_head_normal_form)


def compute_weak_head_normal_form(node: Node) -> Shape | ShapeBottom:
    """The per-node clause body of weak head normalization; single-valued, no aggregate."""
    match node:
        case Var(index=index):
            return VarShape(index=index)
        case Lam(body=body):
            return LamShape(body=body)
        case App(function=function, argument=argument):
            head = weak_head_normalize(function)
            match head:
                case LamShape(body=lambda_body):
                    _consume_redex()
                    return weak_head_normalize(substitute(lambda_body, depth=0, argument=argument))
                case VarShape() | AppShape():
                    return AppShape(function=function, argument=argument)
                case ShapeBottom.BOTTOM:
                    return BOTTOM
                case _:
                    raise TypeError(f"Unknown head {head!r}")
        case _:
            raise TypeError(f"Unknown node {node!r}")


def head_normalize(node: Node) -> Shape | ShapeBottom:
    """The head normal form of ``node`` (the Boehm reading): its outermost constructor after head
    reduction, which reduces under ``lambda`` to expose the head, or ``BOTTOM`` (no head normal form).

    Typed via ``Node.head_normal_form`` (a ``fixpoint_cached_property`` typed as ``object``).
    """
    return cast("Shape | ShapeBottom", node.head_normal_form)


def compute_head_normal_form(node: Node) -> Shape | ShapeBottom:
    """The per-node clause body of head normalization (the Boehm reading).

    The only difference from weak head normalization is the ``Lam`` clause: a ``lambda`` whose body
    has no head normal form is itself meaningless (``BOTTOM``), because head reduction continues under
    the ``lambda``. The ``App`` clause is identical (a head redex fires on the weak head of the
    function, whether or not its body has a head normal form).
    """
    match node:
        case Var(index=index):
            return VarShape(index=index)
        case Lam(body=body):
            if head_normalize(body) is BOTTOM:
                return BOTTOM
            return LamShape(body=body)
        case App(function=function, argument=argument):
            head = weak_head_normalize(function)
            match head:
                case LamShape(body=lambda_body):
                    _consume_redex()
                    return head_normalize(substitute(lambda_body, depth=0, argument=argument))
                case VarShape() | AppShape():
                    return AppShape(function=function, argument=argument)
                case ShapeBottom.BOTTOM:
                    return BOTTOM
                case _:
                    raise TypeError(f"Unknown head {head!r}")
        case _:
            raise TypeError(f"Unknown node {node!r}")
