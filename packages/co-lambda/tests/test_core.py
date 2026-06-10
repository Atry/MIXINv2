"""Core interpreter behaviour: the graph as the reachable sub-coalgebra of weak head normalization.

Interned nodes make a cyclic structure a finite set of nodes, so tabling ``weak_head_normalize`` folds
it into a finite cyclic graph where head reduction would unfold forever. Unproductive cycles
(Omega, Y (lambda x. x)) have no weak head normal form, so they render as the bottom leaf. Head
normalization is single-valued: there is no set, and the empty value is just bottom.
"""

from __future__ import annotations

from syrupy.assertion import SnapshotAssertion

from co_lambda._ast import BOTTOM
from co_lambda._dsl import app, build
from co_lambda._prelude import (
    CYCLIC_ZEROS,
    FINITE_LIST,
    IDENTITY,
    IDENTITY_TERM,
    KESTREL,
    KESTREL_TERM,
    LOOP,
    OMEGA,
    SELF_APPLY,
    ZERO,
    cons,
)
from co_lambda._render import render


def test_identity_readout(snapshot: SnapshotAssertion) -> None:
    assert render(IDENTITY_TERM) == snapshot(name="identity")


def test_kestrel_readout(snapshot: SnapshotAssertion) -> None:
    assert render(KESTREL_TERM) == snapshot(name="kestrel")


def test_finite_list_readout(snapshot: SnapshotAssertion) -> None:
    assert render(FINITE_LIST) == snapshot(name="finite_list")


def test_beta_redex_fires() -> None:
    applied = build(app(IDENTITY, KESTREL))
    assert render(applied) == render(KESTREL_TERM)


def test_cyclic_zeros_folds_to_rational_tree(snapshot: SnapshotAssertion) -> None:
    # The cyclic stream is written Y (cons 0) (no recursion binder); interning folds the
    # structurally-repeating cell into a finite cyclic graph.
    assert render(CYCLIC_ZEROS) == snapshot(name="cyclic_zeros")


def test_unproductive_cycles_are_bottom() -> None:
    # Omega and Y (lambda x. x) (i.e. letrec x = x) are unproductive cycles: no head normal
    # form, so the least fixpoint stabilizes at BOTTOM and the graph is the bottom leaf.
    assert OMEGA.weak_head_normal_form is BOTTOM
    assert LOOP.weak_head_normal_form is BOTTOM
    assert render(OMEGA) == "⊥"
    assert render(LOOP) == "⊥"


def test_first_approximation_versus_lfp() -> None:
    # T up 1 (fold_cycles=False) cuts a guarded cycle to the guarded-cut leaf: a finite,
    # back-reference-free tree with a single dummy cut leaf and no bottom (the cycle is
    # productive, not unproductive). lfp (fold_cycles=True) folds it: a cyclic graph with a
    # back-reference and no cut. T up 1 is the less defined; both terminate.
    approx = render(CYCLIC_ZEROS, fold_cycles=False)
    fixpoint = render(CYCLIC_ZEROS, fold_cycles=True)
    assert "∅" in approx and "#" not in approx and "⊥" not in approx
    assert "#" in fixpoint and "∅" not in fixpoint and "⊥" not in fixpoint
    # On an acyclic term the two coincide (no re-entry to fold or cut).
    assert render(IDENTITY_TERM, fold_cycles=False) == render(IDENTITY_TERM, fold_cycles=True)


def test_repr_of_cyclic_node_is_bounded() -> None:
    # A node graph is shared and may be cyclic (Y), so a structural repr would unfold the sharing
    # exponentially or loop forever; repr must be bounded (it identifies the node, not its tree).
    # This guards error messages that interpolate a node, which would otherwise hang.
    text = repr(CYCLIC_ZEROS)
    assert text.startswith("<") and "0x" in text and len(text) < 80


def test_guarded_cut_distinct_from_unproductive() -> None:
    # The first-iteration reading keeps the guarded cut (the productive cycle the finite budget
    # stops) distinct from the unproductive meaningless leaf. Y (cons 0) is a productive cycle,
    # cut to the dummy cut leaf; cons 0 Omega stops at the unproductive Omega, a bottom. They no
    # longer collapse onto one symbol, so a context can no longer conflate them.
    guarded = render(CYCLIC_ZEROS, fold_cycles=False)
    cons_zero_omega = build(cons(ZERO, app(SELF_APPLY, SELF_APPLY)))  # cons 0 Omega
    unproductive = render(cons_zero_omega, fold_cycles=False)
    assert "∅" in guarded and "⊥" not in guarded
    assert "⊥" in unproductive and "∅" not in unproductive
