"""Dynamic programming with a tree as the state space: memoisation for free.

A tree DP is an ordinary ``Y``-recursion whose subproblems are the subtrees of the input. The
input ``shared_false_tree(depth)`` is a perfect binary tree built by sharing both children at
every level, so interning collapses it to a DAG of ``depth + 1`` distinct nodes that unfolds to
``2 ** depth`` leaves. Because identical subtrees are one interned node, the DP ``tree_any``
computes each distinct subtree once: the result is read in time linear in ``depth`` where the
naive (unshared) tree recursion would visit ``2 ** depth`` leaves. The depth below is far past
what an unshared recursion could finish, so termination is itself the witness that overlapping
subproblems are memoised. No memo table is written; tabling on first-order state identity is the
memoisation, which the pure lambda-calculus cannot do without a decidable identity on subproblems.
"""

from __future__ import annotations

from co_lambda._dsl import build
from co_lambda._prelude import FALSE, TRUE, any_false_dp, tree_any, tree_leaf, tree_node
from co_lambda._render import render

_TRUE = render(build(TRUE))
_FALSE = render(build(FALSE))


def test_small_tree_dp() -> None:
    # A two-level tree with one TRUE leaf: tree_any is TRUE; all-false is FALSE.
    all_false = tree_node(tree_leaf(FALSE), tree_leaf(FALSE))
    has_true = tree_node(tree_leaf(FALSE), tree_leaf(TRUE))
    assert render(build(tree_any(all_false))) == _FALSE
    assert render(build(tree_any(has_true))) == _TRUE


def test_memoisation_makes_exponential_dp_terminate() -> None:
    # depth 30 unfolds to 2 ** 30 (about a billion) leaves; an unshared recursion cannot finish. It returns FALSE in
    # time linear in the depth only because each shared subtree is one interned node and so is
    # computed once: tabling on first-order state identity is the memoisation.
    depth = 30
    assert render(any_false_dp(depth)) == _FALSE
