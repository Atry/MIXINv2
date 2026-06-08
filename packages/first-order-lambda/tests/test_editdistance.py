"""Edit distance as a pure lambda term, memoized for free by the interpreter.

The Levenshtein recursion is written directly (no memoization table) and run by the interpreter. Its
subproblems are pairs of suffixes of the two inputs, which are shared interned sub-nodes, so a repeated
subproblem is the same ``App`` node and the interpreter computes it once. These tests cross-check the
result against a textbook dynamic-programming reference, and check that a moderate input is handled
quickly, which an unmemoized exponential recursion could not be.
"""

from __future__ import annotations

import time

import pytest

from first_order_lambda._editdistance import edit_distance


def _reference(left: str, right: str) -> int:
    """The textbook O(mn) edit-distance table, the reference the lambda term must agree with."""
    rows, columns = len(left), len(right)
    table = [[0] * (columns + 1) for _ in range(rows + 1)]
    for row in range(rows + 1):
        table[row][0] = row
    for column in range(columns + 1):
        table[0][column] = column
    for row in range(1, rows + 1):
        for column in range(1, columns + 1):
            table[row][column] = min(
                table[row - 1][column] + 1,
                table[row][column - 1] + 1,
                table[row - 1][column - 1] + (0 if left[row - 1] == right[column - 1] else 1),
            )
    return table[rows][columns]


_CASES = [
    ("", ""),
    ("a", ""),
    ("", "abc"),
    ("ab", "ba"),
    ("cat", "cot"),
    ("flaw", "lawn"),
    ("abcd", "abcd"),
    ("kitten", "sitting"),
    ("sunday", "saturday"),
    ("intention", "execution"),
]


@pytest.mark.parametrize("left, right", _CASES)
def test_edit_distance_matches_reference(left: str, right: str) -> None:
    assert edit_distance(left, right) == _reference(left, right)


def test_moderate_input_is_fast_because_subproblems_are_tabled() -> None:
    # The naive recursion is exponential; the interpreter tables the shared suffix-pair subproblems, so
    # this returns quickly. A generous bound that an unmemoized recursion on these lengths would blow.
    left, right = "intention", "execution"
    start = time.time()
    assert edit_distance(left, right) == _reference(left, right)
    assert time.time() - start < 10.0
