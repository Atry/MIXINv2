"""Weak head (Levy-Longo) versus head (Boehm) normalization.

Two structure maps over the same coalgebra, the same ``render``/tabling, folding on the same node
identity. This pins the two claims:

- The *semantics* differ: the two readings disagree exactly on a ``lambda`` whose body has no head
  normal form. Witness ``lambda x. Omega``: weak head keeps the ``lambda`` (``(λ ⊥)``), head
  normalization bottoms the whole term (``⊥``).
- The *convergence* (whether ``render`` terminates) coincides: head normalization does eagerly,
  along the head spine, exactly the weak-head reductions the Levy-Longo readout does lazily, so both
  terminate on the same terms (differing only in the value at meaningless ``lambda``-nodes).
"""

from __future__ import annotations

import pytest

from co_lambda._ast import BOTTOM
from co_lambda._codec import church
from co_lambda._dsl import app, build, lam
from co_lambda._examples import CYCLIC_ZEROS, IDENTITY_TERM, OMEGA
from co_lambda._prelude import SELF_APPLY, SUCC, Y, ZERO
from co_lambda._render import render
from co_lambda._shape import (
    LamShape,
    ReductionBudgetExceeded,
    head_normalize,
    reduction_budget,
    weak_head_normalize,
)
from co_lambda._sugar import cons

# lambda x. Omega : the term on which the two readings disagree (Omega is unused under the lambda).
LAM_OMEGA = build(lam(lambda _x: app(SELF_APPLY, SELF_APPLY)))

# The non-rational stream of all naturals: 0, 1, 2, ... every cell distinct.
NATS = build(app(app(Y, lam(lambda self_: lam(lambda n: cons(n, app(self_, app(SUCC, n)))))), ZERO))


def _weak(node) -> str:
    return render(node, normalize=weak_head_normalize)


def _head(node) -> str:
    return render(node, normalize=head_normalize)


# --- Claim 1: the semantics differ ----------------------------------------------------------------


def test_structure_map_differs_on_lambda_omega() -> None:
    # Weak head exposes the lambda; head normalization sees no head normal form under it.
    assert isinstance(weak_head_normalize(LAM_OMEGA), LamShape)
    assert head_normalize(LAM_OMEGA) is BOTTOM


def test_readout_differs_on_lambda_omega() -> None:
    # Levy-Longo keeps the lambda over a bottom body; Boehm bottoms the whole term.
    assert _weak(LAM_OMEGA) == "(λ ⊥)"
    assert _head(LAM_OMEGA) == "⊥"


def test_readings_agree_where_every_subterm_has_a_head_normal_form() -> None:
    # With a head normal form at every level, the two trees coincide.
    for term in [IDENTITY_TERM, build(church(3)), build(app(SUCC, church(2))), CYCLIC_ZEROS]:
        assert _weak(term) == _head(term)


def test_both_bottom_omega() -> None:
    # Omega has no weak head normal form either, so both readings are bottom.
    assert _weak(OMEGA) == "⊥"
    assert _head(OMEGA) == "⊥"


# --- Claim 2: convergence coincides ---------------------------------------------------------------

_CONVERGENT = [IDENTITY_TERM, build(church(3)), CYCLIC_ZEROS, OMEGA, LAM_OMEGA]


@pytest.mark.parametrize("term", _CONVERGENT)
def test_convergence_coincides_on_terminating_terms(term) -> None:
    # Both structure maps make render terminate on each term (the value may differ).
    assert isinstance(_weak(term), str)
    assert isinstance(_head(term), str)


def test_convergence_coincides_on_a_diverging_term() -> None:
    # The non-rational stream terminates under neither reading: both exhaust the reduction budget
    # (or Python's stack first); both are RuntimeError subclasses.
    with reduction_budget(20_000):
        with pytest.raises((ReductionBudgetExceeded, RecursionError)):
            _weak(NATS)
    with reduction_budget(20_000):
        with pytest.raises((ReductionBudgetExceeded, RecursionError)):
            _head(NATS)
