"""Tests for twoHop(X,W) via concat + Join type class.

Graph: a -> b -> c -> a (3-cycle)

Facts:
  edge(a,b).
  edge(b,c).
  edge(c,a).

Step 1 -- Cartesian product:
  concat(X,Y,Z,W) :- edge(X,Y), edge(Z,W).

Step 2 -- Join checks Y==Z via DiagonalSelect + Replacement:
  twoHop(X,W) := concat(X,Y,Y,W).

Join performs VALUE-level equality on Y==Z, producing correct
Datalog semantics.

Expected twoHop (Datalog-correct, 3 pairs):
  {(a,c), (b,a), (c,b)}

Uses the RepeatedVisitor encoding with TailMap navigation.
"""

import pytest

from mixinv2._runtime import Scope, evaluate

import mixinv2_examples
import mixinv2_library


@pytest.fixture
def two_hop_via_concat_scope() -> Scope:
    """Load RelationalTwoHopViaConcat: edge(a,b), edge(b,c), edge(c,a)."""
    root = evaluate(mixinv2_library, mixinv2_examples, modules_public=True)
    result = root.RelationalTwoHopViaConcat
    assert isinstance(result, Scope)
    return result


CONSTANTS = ("a", "b", "c")


def _collect_pairs(relation: Scope) -> set[tuple[str, str]]:
    """Enumerate all (first, second) pairs present in a TailMap relation trie."""
    pairs: set[tuple[str, str]] = set()
    for first in CONSTANTS:
        for second in CONSTANTS:
            try:
                tail1 = getattr(relation.TailMap, first)
                getattr(tail1.TailMap, second)
                pairs.add((first, second))
            except AttributeError:
                pass
    return pairs


def _collect_quads(
    relation: Scope,
) -> set[tuple[str, str, str, str]]:
    """Enumerate all (X,Y,Z,W) 4-tuples present in a 4-column TailMap relation trie."""
    quads: set[tuple[str, str, str, str]] = set()
    for first in CONSTANTS:
        for second in CONSTANTS:
            for third in CONSTANTS:
                for fourth in CONSTANTS:
                    try:
                        tail1 = getattr(relation.TailMap, first)
                        tail2 = getattr(tail1.TailMap, second)
                        tail3 = getattr(tail2.TailMap, third)
                        getattr(tail3.TailMap, fourth)
                        quads.add((first, second, third, fourth))
                    except AttributeError:
                        pass
    return quads


class TestTwoHopViaConcatEdgeFacts:
    """Verify 3-cycle edge facts."""

    def test_edge_a_b(self, two_hop_via_concat_scope: Scope) -> None:
        assert isinstance(two_hop_via_concat_scope.edge.TailMap.a.TailMap.b, Scope)

    def test_edge_b_c(self, two_hop_via_concat_scope: Scope) -> None:
        assert isinstance(two_hop_via_concat_scope.edge.TailMap.b.TailMap.c, Scope)

    def test_edge_c_a(self, two_hop_via_concat_scope: Scope) -> None:
        assert isinstance(two_hop_via_concat_scope.edge.TailMap.c.TailMap.a, Scope)


class TestTwoHopViaConcatConcat:
    """Verify concat intermediate result (9 quads from 3-cycle x 3-cycle)."""

    def test_concat_all_9_quads(self, two_hop_via_concat_scope: Scope) -> None:
        """3-cycle x 3-cycle = 9 4-tuples."""
        quads = _collect_quads(two_hop_via_concat_scope.concat)
        expected = {
            (first, second, third, fourth)
            for first in CONSTANTS
            for second in CONSTANTS
            for third in CONSTANTS
            for fourth in CONSTANTS
            if (first, second) in {("a", "b"), ("b", "c"), ("c", "a")}
            and (third, fourth) in {("a", "b"), ("b", "c"), ("c", "a")}
        }
        assert quads == expected


class TestTwoHopViaConcatResult:
    """Verify twoHop = Datalog-correct result (3 pairs).

    Join performs value-level Y==Z equality:
      Y=b, Z=b: edge(a,b), edge(b,c) -> twoHop(a,c)
      Y=c, Z=c: edge(b,c), edge(c,a) -> twoHop(b,a)
      Y=a, Z=a: edge(c,a), edge(a,b) -> twoHop(c,b)
    """

    def test_two_hop_datalog_correct(
        self, two_hop_via_concat_scope: Scope
    ) -> None:
        """Exactly 3 pairs matching Datalog semantics."""
        pairs = _collect_pairs(two_hop_via_concat_scope.twoHop)
        expected = {("a", "c"), ("b", "a"), ("c", "b")}
        assert pairs == expected

    def test_two_hop_a_c(self, two_hop_via_concat_scope: Scope) -> None:
        """edge(a,b), edge(b,c) -> twoHop(a,c)."""
        assert isinstance(two_hop_via_concat_scope.twoHop.TailMap.a.TailMap.c, Scope)

    def test_two_hop_b_a(self, two_hop_via_concat_scope: Scope) -> None:
        """edge(b,c), edge(c,a) -> twoHop(b,a)."""
        assert isinstance(two_hop_via_concat_scope.twoHop.TailMap.b.TailMap.a, Scope)

    def test_two_hop_c_b(self, two_hop_via_concat_scope: Scope) -> None:
        """edge(c,a), edge(a,b) -> twoHop(c,b)."""
        assert isinstance(two_hop_via_concat_scope.twoHop.TailMap.c.TailMap.b, Scope)

    def test_two_hop_no_self_loops(
        self, two_hop_via_concat_scope: Scope
    ) -> None:
        """No self-loops in Datalog-correct result."""
        with pytest.raises(AttributeError):
            two_hop_via_concat_scope.twoHop.TailMap.a.TailMap.a
        with pytest.raises(AttributeError):
            two_hop_via_concat_scope.twoHop.TailMap.b.TailMap.b
        with pytest.raises(AttributeError):
            two_hop_via_concat_scope.twoHop.TailMap.c.TailMap.c
