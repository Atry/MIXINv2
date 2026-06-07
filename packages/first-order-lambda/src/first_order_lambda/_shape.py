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
from typing import Callable, Iterator, cast, final

from first_order_lambda._ast import (
    BOTTOM,
    App,
    Lam,
    Native,
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


@final
@dataclass(kw_only=True, slots=True, frozen=True, weakref_slot=True)
class NativeShape:
    """The shape of an under-applied foreign function: a value awaiting more arguments.

    A saturated native fires and never surfaces this shape (its weak head normal form is the fired
    result); only a bare or partially applied ``Native`` reads as a ``NativeShape``."""

    run: "Callable[..., Node]"
    arity: int
    collected: tuple[Node, ...]


Shape = VarShape | LamShape | AppShape | NativeShape


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
        case Native(run=run, arity=arity):
            if arity == 0:
                return weak_head_normalize(run())
            return NativeShape(run=run, arity=arity, collected=())
        case App(function=function, argument=argument):
            head = weak_head_normalize(function)
            match head:
                case LamShape(body=lambda_body):
                    _consume_redex()
                    return weak_head_normalize(substitute(lambda_body, depth=0, argument=argument))
                case NativeShape(run=run, arity=arity, collected=collected):
                    saturated = (*collected, argument)
                    if len(saturated) == arity:
                        return weak_head_normalize(run(*saturated))
                    return NativeShape(run=run, arity=arity, collected=saturated)
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
        case Native(run=run, arity=arity):
            if arity == 0:
                return head_normalize(run())
            return NativeShape(run=run, arity=arity, collected=())
        case App(function=function, argument=argument):
            head = weak_head_normalize(function)
            match head:
                case LamShape(body=lambda_body):
                    _consume_redex()
                    return head_normalize(substitute(lambda_body, depth=0, argument=argument))
                case NativeShape(run=run, arity=arity, collected=collected):
                    saturated = (*collected, argument)
                    if len(saturated) == arity:
                        return head_normalize(run(*saturated))
                    return NativeShape(run=run, arity=arity, collected=saturated)
                case VarShape() | AppShape():
                    return AppShape(function=function, argument=argument)
                case ShapeBottom.BOTTOM:
                    return BOTTOM
                case _:
                    raise TypeError(f"Unknown head {head!r}")
        case _:
            raise TypeError(f"Unknown node {node!r}")


def normalize_to_depth(node: Node, depth: int) -> Shape | ShapeBottom:
    """Depth-bounded call-by-name beta normalization: the compiler's reference semantics.

    This is the fusion of weak head normalization and combinatory (SK) reduction. From weak head
    normalization it keeps call-by-name beta, where the argument is inserted by reference (not
    reduced), so the caller's tabling folds both an unproductive cycle (``Omega`` to bottom) and a
    productive one (``Y (cons 0)`` to a finite cyclic graph); a fully lazy SK reduction cannot fold,
    because its ``S`` rule grows the argument into suspensions that never re-form the cyclic node, and
    reducing them first (call by value) diverges on a productive cycle. From combinatory reduction it
    keeps the motivation to avoid copying the whole tree: it fires at most ``depth`` beta contractions
    per application position and leaves a still-unfired redex ``App(Lam(body), argument)`` (the
    let-stub ``(\\a. body) argument``) as a guarded value, rather than substituting an unbounded tree.

    A ``depth`` large enough reproduces the Levy-Longo weak head normal form, ``depth == 1`` is the
    one-layer reading, and ``depth == 0`` reads the term raw. It never consults the cached
    ``weak_head_normal_form`` (the unbounded least fixpoint), so the cached semantics is untouched;
    each contraction goes through ``substitute`` (which returns closed subterms by reference and builds
    with the interning ``make_*``), so closed cyclic data is shared and structurally identical results
    fold at every reduced layer, the per-layer tabling guarantee that lets a cycle closing within the
    depth fold and halt. ``depth`` bounds firings, so every head reduction terminates regardless of
    rationality; the readout's tree is folded by the caller (``render`` tables re-entrant closed
    nodes), so a rational behaviour whose cycle closes within the depth reads as a finite cyclic graph.
    """
    match node:
        case Var(index=index):
            return VarShape(index=index)
        case Lam(body=body):
            return LamShape(body=body)
        case Native(run=run, arity=arity):
            if arity == 0:
                return normalize_to_depth(run(), depth)
            return NativeShape(run=run, arity=arity, collected=())
        case App(function=function, argument=argument):
            head = normalize_to_depth(function, depth)
            match head:
                case LamShape(body=lambda_body):
                    if depth <= 0:
                        return AppShape(function=function, argument=argument)
                    fired = substitute(lambda_body, depth=0, argument=argument)
                    return normalize_to_depth(fired, depth - 1)
                case NativeShape(run=run, arity=arity, collected=collected):
                    saturated = (*collected, argument)
                    if len(saturated) == arity:
                        return normalize_to_depth(run(*saturated), depth)
                    return NativeShape(run=run, arity=arity, collected=saturated)
                case VarShape() | AppShape():
                    return AppShape(function=function, argument=argument)
                case ShapeBottom.BOTTOM:
                    return BOTTOM
                case _:
                    raise TypeError(f"Unknown head {head!r}")
        case _:
            raise TypeError(f"Unknown node {node!r}")


def one_layer_normalize(node: Node) -> Shape | ShapeBottom:
    """The one-layer-beta structure map: one contraction per application position (``depth == 1``).

    A distinct denotational variant beside ``weak_head_normalize`` (Levy-Longo) and ``head_normalize``
    (Boehm): where weak head normalization fires the head spine to a constructor, this fires a single
    redex per position and leaves any remaining redex as a guarded let-stub.
    """
    return normalize_to_depth(node, 1)
