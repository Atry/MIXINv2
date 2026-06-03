"""The weak-head shape relation ``Sh`` (Definition ``def:sh``), single-valued.

A deterministic calculus exposes exactly one weak-head constructor at a position, so ``Sh``
is single-valued, not a set: the value at a position is a shape or ``BOTTOM`` (no shape), not
a set of shapes. ``compute_shape`` is the per-node clause body; ``Node.shape`` wraps it in a
``fixpoint_cached_property`` resolved as a least fixpoint from ``BOTTOM`` upward. Because
nodes are interned, a position reached again during its own computation is caught by a
pointer test; an unproductive head cycle (such a reentry with no constructor exposed, as in
``Omega`` or ``Y (lambda x. x)``) stabilizes at ``BOTTOM``.

A reduction budget (a context variable) bounds beta-reduction so any genuinely non-rational
reduction surfaces as ``ReductionBudgetExceeded`` in tests instead of hanging.
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


def shape_of(node: Node) -> Shape | ShapeBottom:
    """The stabilized shape of ``node`` (``fixpoint_cached_property`` is typed as ``object``)."""
    return cast("Shape | ShapeBottom", node.shape)


def compute_shape(node: Node) -> Shape | ShapeBottom:
    """The clauses of ``Sh`` (Definition ``def:sh``); single-valued, no aggregate."""
    match node:
        case Var(index=index):
            return VarShape(index=index)
        case Lam(body=body):
            return LamShape(body=body)
        case App(function=function, argument=argument):
            head = shape_of(function)
            match head:
                case LamShape(body=lambda_body):
                    _consume_redex()
                    return shape_of(substitute(lambda_body, depth=0, argument=argument))
                case VarShape() | AppShape():
                    return AppShape(function=function, argument=argument)
                case ShapeBottom.BOTTOM:
                    return BOTTOM
                case _:
                    raise TypeError(f"Unknown head shape {head!r}")
        case _:
            raise TypeError(f"Unknown node {node!r}")
