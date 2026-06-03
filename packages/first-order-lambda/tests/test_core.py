"""Core interpreter behaviour: the Berarducci tree as a least fixpoint over interned positions.

Interned positions make a cyclic structure a finite set of positions, so the least-fixpoint
readout folds it into a finite rational tree where head reduction would unfold forever.
Unproductive cycles (Omega, Y (lambda x. x)) have no weak-head shape, so they read out as the
bottom leaf. The readout is single-valued: there is no set, and the empty/bottom value is
just bottom.
"""

from __future__ import annotations

from syrupy.assertion import SnapshotAssertion

from first_order_lambda._ast import BOTTOM
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


def test_identity_readout(snapshot: SnapshotAssertion) -> None:
    assert render(berarducci(IDENTITY_TERM)) == snapshot(name="identity")


def test_kestrel_readout(snapshot: SnapshotAssertion) -> None:
    assert render(berarducci(KESTREL_TERM)) == snapshot(name="kestrel")


def test_finite_list_readout(snapshot: SnapshotAssertion) -> None:
    assert render(berarducci(FINITE_LIST)) == snapshot(name="finite_list")


def test_beta_redex_fires() -> None:
    applied = build(app(IDENTITY, KESTREL))
    assert render(berarducci(applied)) == render(berarducci(KESTREL_TERM))


def test_cyclic_zeros_folds_to_rational_tree(snapshot: SnapshotAssertion) -> None:
    # The cyclic stream is written Y (cons 0) (no recursion binder); interning folds the
    # structurally-repeating cell into a finite rational tree.
    assert render(berarducci(CYCLIC_ZEROS)) == snapshot(name="cyclic_zeros")


def test_unproductive_cycles_are_bottom() -> None:
    # Omega and Y (lambda x. x) (i.e. letrec x = x) are unproductive cycles: no weak-head
    # shape, so the least fixpoint stabilizes at BOTTOM and the readout is the bottom leaf.
    assert OMEGA.shape is BOTTOM
    assert LOOP.shape is BOTTOM
    assert render(berarducci(OMEGA)) == "⊥"
    assert render(berarducci(LOOP)) == "⊥"


def test_first_approximation_versus_lfp() -> None:
    # T up 1 (fold_cycles=False) cuts a guarded cycle to bottom: a finite, back-reference-free
    # tree with a bottom leaf. lfp (fold_cycles=True) folds it: a cyclic tree with a
    # back-reference and no bottom. T up 1 is the less defined; both terminate.
    approx = render(berarducci(CYCLIC_ZEROS, fold_cycles=False))
    fixpoint = render(berarducci(CYCLIC_ZEROS, fold_cycles=True))
    assert "⊥" in approx and "#" not in approx
    assert "#" in fixpoint and "⊥" not in fixpoint
    # On an acyclic term the two coincide (no re-entry to fold or cut).
    assert render(berarducci(IDENTITY_TERM, fold_cycles=False)) == render(
        berarducci(IDENTITY_TERM, fold_cycles=True)
    )
