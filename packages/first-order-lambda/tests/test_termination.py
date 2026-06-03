"""When a single readout terminates: iff the Berarducci tree is rational.

An infinite singly-linked list is representable when it is *rational* (finitely many distinct
interned positions): a cyclic list folds to a finite representation and the readout
terminates. A non-rational infinite list (every cell distinct, e.g. the stream of all
naturals) has no finite representation, so the readout produces ever-new positions and does
not terminate.

Two budgets bound the two ways a computation can fail to terminate:
- ``fixpoints``' ``max_fixpoint_iterations`` bounds the reentrant shape digest (a cyclic
  position whose own shape is demanded); in this single-valued / bottom setting that digest
  converges in a couple of iterations, but with a budget of 0 a reentry is reported as
  ``FixpointRecursionError`` instead of being resolved.
- ``reduction_budget`` bounds beta-steps, which is what a non-rational (non-reentrant)
  readout exhausts.
"""

import pytest

from fixpoints._core import FixpointRecursionError, fixpoint_cached_property

from first_order_lambda._dsl import app, build, lam
from first_order_lambda._prelude import IDENTITY, SUCC, Y, ZERO, cons
from first_order_lambda._readout import berarducci, render
from first_order_lambda._shape import ReductionBudgetExceeded, reduction_budget

# An infinite RATIONAL singly-linked list: cons 0 (cons 0 (...)), finitely many positions.
CYCLIC_LIST = build(app(Y, lam(lambda self_: cons(ZERO, self_))))

# An infinite NON-RATIONAL singly-linked list: 0, 1, 2, ... every cell distinct.
NATS = build(app(app(Y, lam(lambda self_: lam(lambda n: cons(n, app(self_, app(SUCC, n)))))), ZERO))


def test_infinite_cyclic_list_is_representable() -> None:
    # Infinite but rational: the readout folds it into a finite cyclic representation.
    assert "#" in render(berarducci(CYCLIC_LIST))


def test_infinite_non_rational_list_does_not_terminate() -> None:
    # Infinite and non-rational: no finite representation, so a single readout cannot
    # terminate. It exhausts the reduction budget, or Python's stack first; both are
    # RuntimeError subclasses.
    with reduction_budget(50_000):
        with pytest.raises((ReductionBudgetExceeded, RecursionError)):
            berarducci(NATS)


def test_fixpoints_iteration_budget_bounds_a_reentrant_cycle() -> None:
    # A structurally-unique unproductive cycle whose shape is not computed elsewhere, so
    # interning's shape cache does not pre-empt the digest. Under a 0-iteration budget the
    # reentry cannot be resolved and fixpoints raises FixpointRecursionError.
    unique_loop = build(app(Y, lam(lambda x: app(IDENTITY, x))))  # Y (lambda x. id x)
    token = fixpoint_cached_property.max_fixpoint_iterations.set(0)
    try:
        with pytest.raises(FixpointRecursionError):
            _ = unique_loop.shape
    finally:
        fixpoint_cached_property.max_fixpoint_iterations.reset(token)
