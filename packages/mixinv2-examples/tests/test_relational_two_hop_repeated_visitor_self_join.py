"""Tests for RelationalTwoHopRepeatedVisitorSelfJoin.mixin.yaml.

Self-join counterexample: edge = {(a,b), (b,a)}

Datalog: twoHop(X,Z) := edge(X,Y), edge(Y,Z).
  Y=b: edge(a,b), edge(b,a) -> twoHop(a,a)
  Y=a: edge(b,a), edge(a,b) -> twoHop(b,b)
  Datalog result: {(a,a), (b,b)} -- 2 pairs

The old VisitorMapFactory approach over-approximated to 4 pairs.
This test verifies whether the repeated Visitor approach is exact.
"""

import pytest

from mixinv2._runtime import Scope, evaluate

import mixinv2_examples
import mixinv2_library


CONSTANTS = ("a", "b")


@pytest.fixture
def self_join_scope() -> Scope:
    """Load RelationalTwoHopRepeatedVisitorSelfJoin."""
    root = evaluate(mixinv2_library, mixinv2_examples, modules_public=True)
    result = root.RelationalTwoHopRepeatedVisitorSelfJoin
    assert isinstance(result, Scope)
    return result


def _collect_pairs(relation: Scope) -> set[tuple[str, str]]:
    """Enumerate all (first, second) pairs in a binary relation trie."""
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


class TestSelfJoinEdgeFacts:
    """Verify edge facts: {(a,b), (b,a)}."""

    def test_edge_a_b(self, self_join_scope: Scope) -> None:
        assert isinstance(self_join_scope.edge.TailMap.a.TailMap.b, Scope)

    def test_edge_b_a(self, self_join_scope: Scope) -> None:
        assert isinstance(self_join_scope.edge.TailMap.b.TailMap.a, Scope)

    def test_edge_exactly_2_pairs(self, self_join_scope: Scope) -> None:
        pairs = _collect_pairs(self_join_scope.edge)
        expected = {("a", "b"), ("b", "a")}
        assert pairs == expected


class TestSelfJoinTwoHopResult:
    """Verify twoHop with self-join.

    Datalog-correct result: {(a,a), (b,b)}

    The old VisitorMapFactory approach produced 4 pairs (over-approximation).
    The repeated Visitor approach should produce exactly 2 pairs.
    """

    def test_two_hop_is_scope(self, self_join_scope: Scope) -> None:
        assert isinstance(self_join_scope.twoHop, Scope)

    def test_two_hop_a_a(self, self_join_scope: Scope) -> None:
        """edge(a,b), edge(b,a) -> twoHop(a,a)."""
        assert isinstance(
            self_join_scope.twoHop.TailMap.a.TailMap.a, Scope
        )

    def test_two_hop_b_b(self, self_join_scope: Scope) -> None:
        """edge(b,a), edge(a,b) -> twoHop(b,b)."""
        assert isinstance(
            self_join_scope.twoHop.TailMap.b.TailMap.b, Scope
        )

    def test_two_hop_datalog_correct(self, self_join_scope: Scope) -> None:
        """Exactly 2 pairs matching Datalog semantics."""
        pairs = _collect_pairs(self_join_scope.twoHop)
        datalog_expected = {("a", "a"), ("b", "b")}
        assert pairs == datalog_expected

    def test_two_hop_no_extra_a_b(self, self_join_scope: Scope) -> None:
        """twoHop(a,b) should NOT exist in Datalog.

        edge(a,Y) gives Y=b, then edge(b,Z) gives Z=a, not b.
        """
        with pytest.raises(AttributeError):
            self_join_scope.twoHop.TailMap.a.TailMap.b

    def test_two_hop_no_extra_b_a(self, self_join_scope: Scope) -> None:
        """twoHop(b,a) should NOT exist in Datalog.

        edge(b,Y) gives Y=a, then edge(a,Z) gives Z=b, not a.
        """
        with pytest.raises(AttributeError):
            self_join_scope.twoHop.TailMap.b.TailMap.a
