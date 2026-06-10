"""Minimax / AND-OR game search with a transposition table for free.

A position is a MAX node (the mover maximises: OR over moves), a MIN node (the opponent: AND), or a
terminal LEAF Boolean. A transposition is the same position reached by a different move order; under
interning it is a single node, so its value is computed once. Interning is the transposition table,
with no table written by hand.
"""

from __future__ import annotations

from co_lambda._dsl import build
from co_lambda._prelude import (
    FALSE,
    TRUE,
    game_leaf,
    game_max,
    game_min,
    minimax,
)
from co_lambda._render import render

_TRUE = render(build(TRUE))
_FALSE = render(build(FALSE))
_T = build(TRUE)
_F = build(FALSE)


def test_minimax_value_with_a_transposition() -> None:
    # The position T is reached both as a move from A and as a move from B (a transposition).
    #   T    = MIN(leaf T, leaf F)            = AND(T, F) = F
    #   A    = MAX(T, leaf T)                 = OR(F, T)  = T
    #   B    = MAX(leaf F, T)                 = OR(F, F)  = F
    #   root = MIN(A, B)                      = AND(T, F) = F
    transposed = game_min(game_leaf(_T), game_leaf(_F))
    a = game_max(transposed, game_leaf(_T))
    b = game_max(game_leaf(_F), transposed)
    root = game_min(a, b)
    assert render(minimax(root)) == _FALSE


def test_transposition_is_a_single_interned_node() -> None:
    # The same position, however it is reached, is one interned node: that pointer identity is the
    # transposition-table key on which the value is shared. Two independent constructions coincide.
    one_way = game_min(game_leaf(_T), game_leaf(_F))
    other_way = game_min(game_leaf(_T), game_leaf(_F))
    assert one_way is other_way
