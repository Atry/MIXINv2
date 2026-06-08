"""Edit distance: a hard dynamic program that is trivial in this framework.

The Levenshtein distance between two strings is the textbook example of a problem whose naive
recursion is exponential and whose efficient solution needs a memoization table. Here the recursion is
written directly as a pure lambda term and the table is *free*: the interpreter identifies a state
with its behaviour by node identity (interning), and the subproblems of edit distance are pairs of
*suffixes* of the two inputs, which are shared sub-nodes of the input lists. So ``ed tailA tailB`` for
a given suffix pair is literally the same ``App`` node every time it arises, and the interpreter
computes its weak head normal form once and caches it. The exponential call tree collapses to the
``(m+1)(n+1)`` distinct suffix pairs, the classic O(mn) table, with no memoization code written.

Costs are BinNats (``_binnat``), so the arithmetic (successor, three-way minimum) is logarithmic in
the distance rather than unary. A string is a Scott list of BinNat character codes; characters are
compared with ``BIN_EQUAL``.
"""

from __future__ import annotations

import sys

from first_order_lambda._ast import Node
from first_order_lambda._binnat import (
    BIN_EQUAL,
    BIN_MIN,
    BIN_SUCC,
    BIN_ZERO,
    binnat_to_int,
    int_to_binnat,
)
from first_order_lambda._dsl import Builder, app, build, lam
from first_order_lambda._prelude import SCOTT_NIL, Y, cons

# length l: the length of a Scott list, as a BinNat.
LENGTH: Builder = app(Y, lam(lambda length: lam(lambda items: app(
    app(items, lam(lambda head: lam(lambda tail: app(BIN_SUCC, app(length, tail))))),
    BIN_ZERO,
))))


def _min3(first: Builder, second: Builder, third: Builder) -> Builder:
    return app(app(BIN_MIN, first), app(app(BIN_MIN, second), third))


# edit_distance a b: the Levenshtein distance, as a BinNat. When a head matches, recurse on both tails
# at no cost; otherwise pay one and take the best of a deletion, an insertion, and a substitution. An
# empty side costs the other side's length. The three recursive calls on shared suffixes are the same
# interned nodes across the whole call tree, so the interpreter tables them: O(mn) distinct subproblems.
EDIT_DISTANCE: Builder = app(Y, lam(lambda edit: lam(lambda a: lam(lambda b: app(
    app(a, lam(lambda head_a: lam(lambda tail_a: app(
        app(b, lam(lambda head_b: lam(lambda tail_b: app(
            app(
                app(app(BIN_EQUAL, head_a), head_b),
                app(app(edit, tail_a), tail_b),  # heads equal: recurse on both tails, no cost
            ),
            app(BIN_SUCC, _min3(  # heads differ: one plus the best of three edits
                app(app(edit, tail_a), tail_b),  # substitution
                app(app(edit, tail_a), b),       # deletion
                app(app(edit, a), tail_b),       # insertion
            )),
        )))),
        app(LENGTH, a),  # b empty: delete all of a
    )))),
    app(LENGTH, b),  # a empty: insert all of b
)))))


def _string_to_list(text: str, alphabet: "dict[str, int]") -> Builder:
    """A string as a Scott list of BinNat character codes, codes drawn from ``alphabet``."""
    result: Builder = SCOTT_NIL
    for character in reversed(text):
        result = cons(int_to_binnat(alphabet[character]), result)
    return result


def edit_distance_term(left: str, right: str) -> Node:
    """Build the lambda term computing the edit distance of ``left`` and ``right``, then interpret it."""
    alphabet = {character: index for index, character in enumerate(sorted(set(left + right)))}
    return build(app(app(EDIT_DISTANCE, _string_to_list(left, alphabet)), _string_to_list(right, alphabet)))


# The interpreter normalizes by recursive substitution, so a deep computation needs Python stack: the
# dependency chain of the edit-distance subproblems is the O(m + n) diagonal, plus the BinNat
# arithmetic at each step. Raise the limit for the computation and restore it after (as the reduction
# budget does for its context), so the work stays polynomial (the interning tables the subproblems) and
# the raised limit does not leak into unrelated code that relies on the default.
_RECURSION_LIMIT = 100_000


def edit_distance(left: str, right: str) -> int:
    """The Levenshtein distance of two strings, computed by interpreting the pure lambda term."""
    previous_limit = sys.getrecursionlimit()
    sys.setrecursionlimit(max(previous_limit, _RECURSION_LIMIT))
    try:
        return binnat_to_int(edit_distance_term(left, right))
    finally:
        sys.setrecursionlimit(previous_limit)
