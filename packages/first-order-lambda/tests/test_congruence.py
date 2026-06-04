"""The position congruence is a pluggable parameter (Definition ``def:congruence``).

Syntactic-identity interning is the FINEST instance and the default, so the readout under
``IdentityCongruence`` is bit-for-bit the pure-interning readout. A coarser sound congruence
folds more: ``EGraphCongruence`` is a union-find with congruence closure, the inductive
(least-fixpoint) family. The caller asserts sound (tree-equal) merges; closure propagates them
through ``App``/``Lam`` parents, and the readout then shares the merged positions where interning
kept them distinct.

These tests pin the mechanism: identity is behaviour-preserving, a merge of tree-equal positions
folds them and propagates by congruence, the readout shares a merged subtree, and a merge never
rescues an unproductive cycle (``Omega`` stays the bottom leaf).
"""

from __future__ import annotations

import pytest

from first_order_lambda._ast import App, Node
from first_order_lambda._congruence import (
    DeadSubtermCongruence,
    EGraphCongruence,
    IdentityCongruence,
    PositionEGraphCongruence,
    RecursionArgumentRule,
    UnusedParameterRule,
)
from first_order_lambda._dsl import app, build, lam
from first_order_lambda._prelude import (
    CYCLIC_ZEROS,
    IDENTITY,
    KESTREL,
    OMEGA,
    SCOTT_NIL,
    SUCC,
    Y,
    ZERO,
    cons,
)
from first_order_lambda._readout import AppTree, LamTree, TreeNode, readout, render
from first_order_lambda._shape import (
    LamShape,
    ReductionBudgetExceeded,
    reduction_budget,
    shape_of,
)

# Two syntactically distinct but tree-equal CLOSED positions: ``cons 0 nil`` and
# ``id (cons 0 nil)`` (a redex that reduces to it). Interning keeps them distinct objects (the
# second is an ``App``), yet both read out to the same tree, so merging them is sound.
LIST_CELL = build(cons(ZERO, SCOTT_NIL))
REDUCIBLE_LIST_CELL = build(app(IDENTITY, cons(ZERO, SCOTT_NIL)))


def test_list_cells_are_distinct_positions_but_tree_equal() -> None:
    assert LIST_CELL is not REDUCIBLE_LIST_CELL
    assert render(readout(LIST_CELL)) == render(readout(REDUCIBLE_LIST_CELL))


def test_identity_congruence_reproduces_the_default() -> None:
    # The finest instance is the default: passing it explicitly changes nothing.
    assert render(readout(CYCLIC_ZEROS, congruence=IdentityCongruence())) == render(
        readout(CYCLIC_ZEROS)
    )


def test_egraph_without_merges_is_the_finest_instance() -> None:
    # With no asserted equalities every position is its own class, so the e-graph folds exactly
    # what interning folds.
    assert render(readout(CYCLIC_ZEROS, congruence=EGraphCongruence())) == render(
        readout(CYCLIC_ZEROS)
    )


def test_merge_folds_tree_equal_positions() -> None:
    egraph = EGraphCongruence()
    assert egraph.key(LIST_CELL) != egraph.key(REDUCIBLE_LIST_CELL)
    egraph.merge(LIST_CELL, REDUCIBLE_LIST_CELL)
    assert egraph.key(LIST_CELL) == egraph.key(REDUCIBLE_LIST_CELL)


def test_merge_propagates_to_parents_by_congruence() -> None:
    # K (cons 0 nil) and K (id (cons 0 nil)) differ only in the merged child, so congruence
    # closure must merge the parents too.
    parent_over_cell = build(app(KESTREL, cons(ZERO, SCOTT_NIL)))
    parent_over_redex = build(app(KESTREL, app(IDENTITY, cons(ZERO, SCOTT_NIL))))
    egraph = EGraphCongruence()
    egraph.merge(LIST_CELL, REDUCIBLE_LIST_CELL)
    # Register both parents, then the closure has both signatures available.
    _ = egraph.key(parent_over_cell)
    _ = egraph.key(parent_over_redex)
    assert egraph.key(parent_over_cell) == egraph.key(parent_over_redex)


def _list_elements(tree: TreeNode) -> tuple[TreeNode, TreeNode]:
    # ``cons h t`` reads out as ``(lambda (lambda ((c h) t))))``; recover the two elements ``h``
    # and ``t`` so we can compare them by object identity.
    assert isinstance(tree, LamTree)
    inner = tree.body
    assert isinstance(inner, LamTree)
    application = inner.body
    assert isinstance(application, AppTree)
    head_application = application.function
    assert isinstance(head_application, AppTree)
    return head_application.argument, application.argument


def test_readout_shares_a_merged_subtree() -> None:
    # The list [id (cons 0 nil), cons 0 nil]: two distinct-but-tree-equal cells.
    pair = build(
        cons(app(IDENTITY, cons(ZERO, SCOTT_NIL)), cons(ZERO, SCOTT_NIL))
    )

    head_element, tail_element = _list_elements(readout(pair))
    assert head_element is not tail_element  # interning reads the two cells separately
    assert render(head_element) == render(tail_element)

    egraph = EGraphCongruence()
    egraph.merge(LIST_CELL, REDUCIBLE_LIST_CELL)
    merged_head, merged_tail = _list_elements(readout(pair, congruence=egraph))
    assert merged_head is merged_tail  # the e-graph folds them onto one shared subtree


def test_merge_does_not_rescue_an_unproductive_cycle() -> None:
    # A congruence folds productive re-entries; it adds no constructor, so Omega stays bottom.
    egraph = EGraphCongruence()
    egraph.merge(LIST_CELL, REDUCIBLE_LIST_CELL)
    assert render(readout(OMEGA, congruence=egraph)) == "⊥"


# The Y F 0 witness (paper Theorem termination): F has a CONSTANT 0 head and threads the index n
# through a dead argument slot, so every tail position Y F (succ^k 0) is syntactically distinct
# yet they all denote the one constant-0 stream. Interning (the finest congruence) sees infinitely
# many positions and diverges, even though the tree is rational.
WITNESS = build(
    app(app(Y, lam(lambda self_: lam(lambda n: cons(ZERO, app(self_, app(SUCC, n)))))), ZERO)
)


def test_position_egraph_folds_a_rational_cycle() -> None:
    # The position e-graph keys on the rational shape tree, so a guarded cycle folds with NO
    # asserted merge (unlike the structural EGraphCongruence).
    assert "#" in render(readout(CYCLIC_ZEROS, congruence=PositionEGraphCongruence()))


def test_position_egraph_auto_folds_tree_equal_positions() -> None:
    # A redex and its reduct share a shape tree, so the position e-graph folds them on sight,
    # with no merge call. In the pair [id (cons 0 nil), cons 0 nil] the two elements become one
    # shared subtree; under interning they stay distinct.
    pair = build(cons(app(IDENTITY, cons(ZERO, SCOTT_NIL)), cons(ZERO, SCOTT_NIL)))
    head_element, tail_element = _list_elements(readout(pair))
    assert head_element is not tail_element

    folded_head, folded_tail = _list_elements(
        readout(pair, congruence=PositionEGraphCongruence())
    )
    assert folded_head is folded_tail


def test_position_egraph_still_diverges_on_the_dead_argument_witness() -> None:
    # The honest boundary: bisimulation cannot finitize an infinitely-presented shape graph. The
    # witness's dead argument keeps every tail position distinct, so the shape descent never
    # re-enters a position and the key diverges, exactly as interning does. Folding it needs the
    # dead argument erased (a tree-preserving map), which no congruence closure provides.
    with reduction_budget(2_000):
        with pytest.raises((ReductionBudgetExceeded, RecursionError)):
            readout(WITNESS, congruence=PositionEGraphCongruence())
    # And interning diverges on it too, for the same reason.
    with reduction_budget(2_000):
        with pytest.raises((ReductionBudgetExceeded, RecursionError)):
            readout(WITNESS)


# A live-argument recursion: cons n (self (succ n)) inspects n in the stream HEAD, so n is live
# and the stream is genuinely non-rational (the stream of all naturals). The dead-argument rule
# must NOT fire here.
NATURALS = build(
    app(app(Y, lam(lambda self_: lam(lambda n: cons(n, app(self_, app(SUCC, n)))))), ZERO)
)


def _dead_subterm_congruence() -> DeadSubtermCongruence:
    # The library holds one enabled rule: erase a constant-headed recursion's dead argument. The
    # caller chooses which rules to enable.
    return DeadSubtermCongruence(rules=(RecursionArgumentRule(),))


def test_dead_subterm_congruence_folds_the_witness() -> None:
    # Method B: erasing the dead index makes the tail positions one canonical form, so the readout
    # folds the witness to a finite rational tree where interning and both e-graphs diverge.
    rendered = render(readout(WITNESS, congruence=_dead_subterm_congruence()))
    assert "#" in rendered and "⊥" not in rendered and "∅" not in rendered


def test_dead_subterm_fold_has_constant_zero_heads() -> None:
    # Soundness signal: the witness denotes the constant-0 stream, so every stream head is the
    # Church numeral 0, rendered "(λ (λ v0))" (= ZERO). The fold must keep that head, not corrupt
    # it. (The folded GRAPH may carry a one-cell unfolding prefix relative to Y (cons 0), since
    # the original Y F position and its reduced tail are syntactically distinct, so the render
    # string is not identical to the cyclic-zero stream; the denotation is the same tree.)
    rendered = render(readout(WITNESS, congruence=_dead_subterm_congruence()))
    assert "(λ (λ v0))" in rendered
    assert "#" in rendered


def _stream_tail(node: Node) -> Node:
    # shape(cell) = (lambda c. lambda n. (c head) tail); recover the tail position.
    cell_shape = shape_of(node)
    assert isinstance(cell_shape, LamShape)
    inner = shape_of(cell_shape.body)
    assert isinstance(inner, LamShape)
    application = inner.body
    assert isinstance(application, App)
    return application.argument


def test_dead_subterm_rule_does_not_fire_on_a_live_argument() -> None:
    # Soundness, checked directly: at a reduced recursion tail of the naturals stream the index is
    # demanded in the head, so the rule must NOT report the argument dead.
    rule = RecursionArgumentRule()
    naturals_tail = _stream_tail(NATURALS)
    assert rule.is_dead(naturals_tail) is False
    # End to end: the genuinely non-rational stream still diverges (a small budget suffices, since
    # nothing folds it).
    with reduction_budget(150):
        with pytest.raises((ReductionBudgetExceeded, RecursionError)):
            readout(NATURALS, congruence=_dead_subterm_congruence())


def test_dead_subterm_congruence_keeps_omega_bottom() -> None:
    assert render(readout(OMEGA, congruence=_dead_subterm_congruence())) == "⊥"


def test_unused_parameter_rule_erases_a_discarded_argument() -> None:
    # K 0 x = 0 ignores x, so the second argument is dead. The library rule keys K 0 a and K 0 b
    # the same regardless of the discarded argument (and a live argument is left intact).
    congruence = DeadSubtermCongruence(rules=(UnusedParameterRule(),))
    discards_identity = build(app(app(KESTREL, ZERO), IDENTITY))
    discards_kestrel = build(app(app(KESTREL, ZERO), KESTREL))
    assert congruence.key(discards_identity) == congruence.key(discards_kestrel)
    # With no rule enabled the two stay distinct (the finest reading keeps the argument).
    bare = DeadSubtermCongruence(rules=())
    assert bare.key(discards_identity) != bare.key(discards_kestrel)
