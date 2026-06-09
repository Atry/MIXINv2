"""``sum`` over three lists that all denote the stream ``[0, 0, 0, ...]``: cyclic, closure-counter,
trampoline-counter.

All three lists denote the SAME stream (every element is ``0``), so ``sum`` of each has the same value:
the divergent sum ``0 + 0 + 0 + ...``, which over the bottom-completed order is ``⊥``. What differs is
whether ``sum`` HALTS, and that is governed by the structure of the states, not by the value.

``sum`` folds over the list, and its fold-states are exactly the list's tails: ``sum`` re-enters a state
precisely when it reaches a tail it has already seen. So ``sum`` halts iff the list has finitely many
distinct tails, that is, iff the list's behaviour is rational. The reachable graph of the list under the
structure map ``out`` (what ``render`` walks, folding a closed node re-entered during its own descent to a
back-reference ``#N``) makes this visible:

- ``Y (cons 0)`` is a single cyclic node: its tail is itself, so the graph folds to a finite cyclic graph,
  ``sum``'s fold re-enters that one state, and ``sum`` halts, reducing to the finite value ``(λ (λ ⊥))``.
- the closure-counter list carries a dead counter ``n`` that increments at every step (every element is
  still ``0``), so every tail is a structurally DISTINCT state; the graph never folds, ``sum``'s fold never
  re-enters a state, and ``sum`` diverges.
- hiding the counter behind a trampoline step ``(λ u. s (succ u)) n`` does not change this: the counter is
  still part of the state, every tail is still distinct, and ``sum`` still diverges.

This is the operational form of the rem:tworationalities point: halting follows structural recurrence of
the states, not the value (which is the same ``⊥`` for all three). We walk the list's graph under a node
budget so a non-rational (never-folding) spine is observed as a truncation rather than looping forever; the
halting case ``sum (Y (cons 0))`` is then evaluated to its actual finite value.
"""

from __future__ import annotations

from syrupy.assertion import SnapshotAssertion

from first_order_lambda._dsl import Builder, app, build, lam
from first_order_lambda._prelude import PLUS, SCOTT_CONS, SUCC, Y, ZERO, cons
from first_order_lambda._render import render

# sum l = l (λ h. λ t. add h (sum t)) 0   -- a Scott-list fold, tied with Y.
SUM: Builder = app(Y, lam(lambda self_sum: lam(lambda source: app(
    app(source, lam(lambda head: lam(lambda tail: app(app(PLUS, head), app(self_sum, tail))))),
    ZERO,
))))

# r = cons 0 r : the cyclic stream of zeros, a single structural node (its tail is itself).
CYCLIC: Builder = app(Y, app(SCOTT_CONS, ZERO))
# cons 0 (s (succ n)) : every element 0, but the dead counter n increments, so every tail is distinct.
CLOSURE_COUNTER: Builder = app(app(Y, lam(lambda s: lam(lambda n: cons(ZERO, app(s, app(SUCC, n)))))), ZERO)
# the same counter, but the tail is bounced through a trampoline step (λ u. s (succ u)) n.
TRAMPOLINE_COUNTER: Builder = app(
    app(Y, lam(lambda s: lam(lambda n: cons(ZERO, app(lam(lambda u: app(s, app(SUCC, u))), n))))),
    ZERO,
)

# A node budget for walking the list's graph: the cyclic spine folds well within it, while a non-rational
# spine never folds and is truncated here rather than descended forever.
_SPINE_DEPTH = 30
_SPINE_NODES = 120


def _sum_outcome(list_term: Builder) -> dict[str, str]:
    """Classify ``sum list`` by walking the list's reachable graph (its fold-state set).

    A rational list (its spine re-enters a closed node, so ``render`` folds it to a ``#N`` back-reference
    with no truncation) makes ``sum``'s fold-state set finite, so ``sum`` halts and is evaluated to its
    finite value. A non-rational list (the spine is truncated at the budget with a ``…`` leaf, never
    folding) makes the fold-state set infinite, so ``sum`` diverges and is reported, not evaluated.
    """
    behaviour = render(build(list_term), fold_cycles=True, budget=_SPINE_DEPTH, max_nodes=_SPINE_NODES)
    folds = "…" not in behaviour
    if folds:
        assert "#" in behaviour, "a folded rational spine must carry a cycle back-reference"
        sum_value = render(build(app(SUM, list_term)))  # halts: the fold-state set is finite
        return {
            "list_behaviour": behaviour,
            "sum": f"HALTS: sum folds over a finite state set and reduces to {sum_value}",
        }
    return {
        "list_behaviour": behaviour[:48] + " …(truncated at budget; the spine never folds)",
        "sum": "DIVERGES: every tail is a distinct state, so the fold never re-enters and never terminates",
    }


def test_sum_cyclic_halts_but_counters_diverge(snapshot: SnapshotAssertion) -> None:
    results = {
        "cyclic_Y_cons_0": _sum_outcome(CYCLIC),
        "closure_counter": _sum_outcome(CLOSURE_COUNTER),
        "trampoline_counter": _sum_outcome(TRAMPOLINE_COUNTER),
    }
    assert results == snapshot(name="sum_over_three_zero_streams")
