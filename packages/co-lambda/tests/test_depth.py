"""Depth-bounded reduction: the one-layer-beta variant and the approximation it indexes.

``normalize_to_depth`` fires at most ``depth`` beta contractions per application position, leaving the
redex unfired (a guarded let-stub) once spent. ``depth == 1`` is the one-layer-beta structure map, a
variant distinct from weak head (Levy-Longo) and head (Boehm) normalization; growing ``depth``
climbs the approximation order up to the weak head reading. Because firings are bounded, every head
reduction halts; the caller (``render``) folds the readout's cycles, so a rational behaviour whose
cycle closes within the depth reads as a finite cyclic graph (the per-layer tabling guarantee), while
an unproductive cycle reads as its unfired redex rather than folding to bottom.
"""

from __future__ import annotations

from syrupy.assertion import SnapshotAssertion

from co_lambda._dsl import app, build, lam
from co_lambda._prelude import CYCLIC_ZEROS, IDENTITY, OMEGA
from co_lambda._render import render
from co_lambda._shape import head_normalize, normalize_to_depth, one_layer_normalize


def _render_to_depth(node, depth: int) -> str:
    return render(node, normalize=lambda current: normalize_to_depth(current, depth))


# lam x. I (I x): the head needs two contractions, so the readout climbs with depth.
_NESTED = build(lam(lambda x: app(IDENTITY, app(IDENTITY, x))))


def test_one_layer_distinct_from_weak_head_and_head(snapshot: SnapshotAssertion) -> None:
    one_layer = render(_NESTED, normalize=one_layer_normalize)
    weak_head = render(_NESTED)
    head = render(_NESTED, normalize=head_normalize)
    # The one-layer reading leaves the inner redex unfired where weak head and head fire it through.
    assert one_layer != weak_head
    assert one_layer != head
    assert one_layer == snapshot(name="one_layer")
    assert weak_head == snapshot(name="weak_head")


def test_depth_climbs_to_the_weak_head_reading(snapshot: SnapshotAssertion) -> None:
    # depth 0 reads the term raw (no contraction); each step fires one more layer; depth 2 reaches
    # the weak head normal form and stabilizes.
    assert _render_to_depth(_NESTED, 0) == snapshot(name="depth_0")
    assert _render_to_depth(_NESTED, 1) == snapshot(name="depth_1")
    assert _render_to_depth(_NESTED, 2) == render(_NESTED)
    assert _render_to_depth(_NESTED, 5) == render(_NESTED)


def test_unproductive_cycle_reads_as_its_unfired_redex(snapshot: SnapshotAssertion) -> None:
    # Bounded reduction halts on Omega by leaving the self-application unfired, where the unbounded
    # least fixpoint folds it to bottom. The bounded reading is the variant that does not fold.
    bounded = _render_to_depth(OMEGA, 1)
    assert "⊥" not in bounded
    assert bounded == snapshot(name="omega_bounded")
    assert render(OMEGA) == "⊥"


def test_rational_cycle_folds_within_the_depth(snapshot: SnapshotAssertion) -> None:
    # The cyclic stream Y (cons 0) is rational; its cycle closes within a finite depth, so bounded
    # reduction folds it (a back-reference) and halts, and a large enough depth equals the unbounded
    # reading. This is the per-layer tabling guarantee: identical interned nodes fold at each layer.
    assert "#" in _render_to_depth(CYCLIC_ZEROS, 6)
    assert _render_to_depth(CYCLIC_ZEROS, 6) == render(CYCLIC_ZEROS)
    assert _render_to_depth(CYCLIC_ZEROS, 2) == snapshot(name="cyclic_zeros_depth_2")
