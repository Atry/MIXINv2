"""Core interpreter behaviour under the lfp(T_P) reading: folding, the empty knob.

With hash-consed positions, structurally-equal positions are the same object, so a cyclic
structure has finitely many positions and the shape fixpoint folds it (the IC lfp(T_P), the
more-defined fixpoint lambda-calculus). Unproductive cycles (Omega, letrec x=x) stabilize at
EMPTY; productive cycles (r=cons 0 r, Y (cons 0)) fold to finite rational trees. This is
strictly more defined than beta-reduction (which would diverge on all of these), per the IC
convergence hierarchy.
"""

from __future__ import annotations

from syrupy.assertion import SnapshotAssertion

from first_order_lambda._ast import EMPTY
from first_order_lambda._dsl import app, build
from first_order_lambda._prelude import (
    CYCLIC_ZEROS,
    FINITE_LIST,
    IDENTITY,
    IDENTITY_TERM,
    KESTREL,
    KESTREL_TERM,
    LOOP,
    OMEGA,
)
from first_order_lambda._readout import berarducci, render
from first_order_lambda._variants import least_model, operational


def test_identity_readout(snapshot: SnapshotAssertion) -> None:
    assert render(berarducci(IDENTITY_TERM, operational)) == snapshot(name="identity")


def test_kestrel_readout(snapshot: SnapshotAssertion) -> None:
    assert render(berarducci(KESTREL_TERM, operational)) == snapshot(name="kestrel")


def test_finite_list_readout(snapshot: SnapshotAssertion) -> None:
    assert render(berarducci(FINITE_LIST, operational)) == snapshot(name="finite_list")


def test_readings_agree_on_pure_acyclic_terms() -> None:
    for term in (IDENTITY_TERM, KESTREL_TERM, FINITE_LIST):
        assert render(berarducci(term, operational)) == render(
            berarducci(term, least_model)
        )


def test_beta_redex_fires() -> None:
    applied = build(app(IDENTITY, KESTREL))
    assert render(berarducci(applied, operational)) == render(
        berarducci(KESTREL_TERM, operational)
    )


def test_cyclic_zeros_folds_to_rational_tree(snapshot: SnapshotAssertion) -> None:
    # The cyclic stream is written Y (cons 0) (no recursion binder); interning folds the
    # structurally-repeating cell into a finite rational tree.
    folded = render(berarducci(CYCLIC_ZEROS, least_model))
    assert folded == snapshot(name="cyclic_zeros")


def test_unproductive_cycles_are_empty(snapshot: SnapshotAssertion) -> None:
    # Omega and letrec x=x are both unproductive cycles, so the shape stabilizes at EMPTY.
    assert OMEGA.shape is EMPTY
    assert LOOP.shape is EMPTY
    # The empty knob: operational reads EMPTY as bottom, least_model as the empty leaf.
    assert render(berarducci(OMEGA, operational)) == snapshot(name="omega_operational")
    assert render(berarducci(OMEGA, least_model)) == snapshot(name="omega_least_model")
    assert render(berarducci(LOOP, operational)) == render(
        berarducci(OMEGA, operational)
    )
    assert render(berarducci(LOOP, least_model)) == render(
        berarducci(OMEGA, least_model)
    )
