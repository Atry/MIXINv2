"""Tests for RelationalTwoHopRepeatedVisitor.mixin.yaml.

Graph: a -> b -> c -> a (3-cycle)

Facts:
  edge(a,b).
  edge(b,c).
  edge(c,a).

Rule:
  twoHop(X,Z) := edge(X,Y), edge(Y,Z).

This encoding uses repeated Acceptance/Visitor pattern to perform
value-level join on Y, avoiding the over-approximation problem of
the simpler VisitorMapFactory approach.

Expected twoHop (Datalog-correct, 3 pairs):
  {(a,c), (b,a), (c,b)}
"""

import pytest

from mixinv2._runtime import Scope, evaluate

import mixinv2_examples
import mixinv2_library


CONSTANTS = ("a", "b", "c")


@pytest.fixture
def repeated_visitor_scope() -> Scope:
    """Load RelationalTwoHopRepeatedVisitor: edge(a,b), edge(b,c), edge(c,a)."""
    root = evaluate(mixinv2_library, mixinv2_examples, modules_public=True)
    result = root.RelationalTwoHopRepeatedVisitor
    assert isinstance(result, Scope)
    return result


def _get_tail_map_entry(scope: Scope, entity: str) -> Scope:
    """Navigate TailMap.<entity> on a scope."""
    return getattr(scope.TailMap, entity)


def _collect_pairs(relation: Scope) -> set[tuple[str, str]]:
    """Enumerate all (first, second) pairs present in a binary relation trie.

    Navigates via TailMap.<entity> for each column.
    """
    pairs: set[tuple[str, str]] = set()
    for first in CONSTANTS:
        for second in CONSTANTS:
            try:
                tail1 = _get_tail_map_entry(relation, first)
                _get_tail_map_entry(tail1, second)
                pairs.add((first, second))
            except AttributeError:
                pass
    return pairs


# =============================================================================
# Evaluation: the mixin.yaml must load without errors
# =============================================================================


class TestEvaluation:
    """Test that RelationalTwoHopRepeatedVisitor evaluates without errors.

    Currently fails with:
      ValueError: Cannot navigate path ('VisitorMap', 'a', 'Visited'):
      ('RelationalTwoHopRepeatedVisitor', 'a', 'Acceptance', 'VisitorMap')
      (unexpected kind CONFLICT) has no child 'a'

    The root cause is in constant 'a' Acceptance definition (lines 49-54):
    the VisitorMap uses list syntax (- a: [Visitor]) creating a CONFLICT
    with the VisitorMap inherited from Relation, while constants 'b' and 'c'
    use plain mapping syntax (VisitorMap: b: [Visitor]) which works correctly.
    """

    def test_scope_loads_without_error(
        self, repeated_visitor_scope: Scope
    ) -> None:
        """The mixin.yaml should evaluate to a valid Scope."""
        assert isinstance(repeated_visitor_scope, Scope)


# =============================================================================
# Edge facts: {(a,b), (b,c), (c,a)}
# =============================================================================


class TestEdgeFacts:
    """Verify the 3-cycle edge facts are correctly encoded."""

    def test_edge_is_scope(self, repeated_visitor_scope: Scope) -> None:
        assert isinstance(repeated_visitor_scope.edge, Scope)

    def test_edge_a_b(self, repeated_visitor_scope: Scope) -> None:
        """edge(a,b) exists."""
        assert isinstance(
            repeated_visitor_scope.edge.TailMap.a.TailMap.b, Scope
        )

    def test_edge_b_c(self, repeated_visitor_scope: Scope) -> None:
        """edge(b,c) exists."""
        assert isinstance(
            repeated_visitor_scope.edge.TailMap.b.TailMap.c, Scope
        )

    def test_edge_c_a(self, repeated_visitor_scope: Scope) -> None:
        """edge(c,a) exists."""
        assert isinstance(
            repeated_visitor_scope.edge.TailMap.c.TailMap.a, Scope
        )

    def test_edge_exactly_3_pairs(self, repeated_visitor_scope: Scope) -> None:
        """edge contains exactly {(a,b), (b,c), (c,a)}."""
        pairs = _collect_pairs(repeated_visitor_scope.edge)
        expected = {("a", "b"), ("b", "c"), ("c", "a")}
        assert pairs == expected


# =============================================================================
# Relation infrastructure
# =============================================================================


class TestRelationInfrastructure:
    """Test that Relation, Cons, Nil, and constants are defined."""

    def test_relation_is_scope(self, repeated_visitor_scope: Scope) -> None:
        assert isinstance(repeated_visitor_scope.Relation, Scope)

    def test_nil_is_scope(self, repeated_visitor_scope: Scope) -> None:
        assert isinstance(repeated_visitor_scope.Nil, Scope)

    def test_cons_is_scope(self, repeated_visitor_scope: Scope) -> None:
        assert isinstance(repeated_visitor_scope.Cons, Scope)

    def test_constant_a_is_scope(self, repeated_visitor_scope: Scope) -> None:
        assert isinstance(repeated_visitor_scope.a, Scope)

    def test_constant_b_is_scope(self, repeated_visitor_scope: Scope) -> None:
        assert isinstance(repeated_visitor_scope.b, Scope)

    def test_constant_c_is_scope(self, repeated_visitor_scope: Scope) -> None:
        assert isinstance(repeated_visitor_scope.c, Scope)


# =============================================================================
# Acceptance/Visitor pattern on constants
# =============================================================================


class TestConstantAcceptance:
    """Test that each constant has a working Acceptance/Visitor."""

    def test_a_has_acceptance(self, repeated_visitor_scope: Scope) -> None:
        assert isinstance(repeated_visitor_scope.a.Acceptance, Scope)
        assert isinstance(repeated_visitor_scope.a.Acceptance.Accepted, Scope)

    def test_b_has_acceptance(self, repeated_visitor_scope: Scope) -> None:
        assert isinstance(repeated_visitor_scope.b.Acceptance, Scope)
        assert isinstance(repeated_visitor_scope.b.Acceptance.Accepted, Scope)

    def test_c_has_acceptance(self, repeated_visitor_scope: Scope) -> None:
        assert isinstance(repeated_visitor_scope.c.Acceptance, Scope)
        assert isinstance(repeated_visitor_scope.c.Acceptance.Accepted, Scope)

    def test_nil_has_acceptance(self, repeated_visitor_scope: Scope) -> None:
        assert isinstance(repeated_visitor_scope.Nil.Acceptance, Scope)
        assert isinstance(
            repeated_visitor_scope.Nil.Acceptance.Accepted, Scope
        )


# =============================================================================
# twoHop result: Datalog-correct {(a,c), (b,a), (c,b)}
# =============================================================================


class TestTwoHopResult:
    """Verify twoHop computes the Datalog-correct two-hop result.

    twoHop(X,Z) := edge(X,Y), edge(Y,Z).

    With the 3-cycle edge(a,b), edge(b,c), edge(c,a):
      Y=b: edge(a,b), edge(b,c) -> twoHop(a,c)
      Y=c: edge(b,c), edge(c,a) -> twoHop(b,a)
      Y=a: edge(c,a), edge(a,b) -> twoHop(c,b)
    """

    def test_two_hop_is_scope(self, repeated_visitor_scope: Scope) -> None:
        assert isinstance(repeated_visitor_scope.twoHop, Scope)

    def test_two_hop_a_c(self, repeated_visitor_scope: Scope) -> None:
        """edge(a,b), edge(b,c) -> twoHop(a,c)."""
        assert isinstance(
            repeated_visitor_scope.twoHop.TailMap.a.TailMap.c, Scope
        )

    def test_two_hop_b_a(self, repeated_visitor_scope: Scope) -> None:
        """edge(b,c), edge(c,a) -> twoHop(b,a)."""
        assert isinstance(
            repeated_visitor_scope.twoHop.TailMap.b.TailMap.a, Scope
        )

    def test_two_hop_c_b(self, repeated_visitor_scope: Scope) -> None:
        """edge(c,a), edge(a,b) -> twoHop(c,b)."""
        assert isinstance(
            repeated_visitor_scope.twoHop.TailMap.c.TailMap.b, Scope
        )

    def test_two_hop_datalog_correct(
        self, repeated_visitor_scope: Scope
    ) -> None:
        """Exactly 3 pairs matching Datalog semantics."""
        pairs = _collect_pairs(repeated_visitor_scope.twoHop)
        expected = {("a", "c"), ("b", "a"), ("c", "b")}
        assert pairs == expected

    def test_two_hop_no_self_loops(
        self, repeated_visitor_scope: Scope
    ) -> None:
        """No self-loops: twoHop(a,a), twoHop(b,b), twoHop(c,c) should not exist."""
        with pytest.raises(AttributeError):
            repeated_visitor_scope.twoHop.TailMap.a.TailMap.a
        with pytest.raises(AttributeError):
            repeated_visitor_scope.twoHop.TailMap.b.TailMap.b
        with pytest.raises(AttributeError):
            repeated_visitor_scope.twoHop.TailMap.c.TailMap.c

    def test_two_hop_no_identity_pairs(
        self, repeated_visitor_scope: Scope
    ) -> None:
        """No identity-edge pairs: twoHop(a,b), twoHop(b,c), twoHop(c,a) should not exist.

        These would be the original edges, not two-hop paths.
        """
        with pytest.raises(AttributeError):
            repeated_visitor_scope.twoHop.TailMap.a.TailMap.b
        with pytest.raises(AttributeError):
            repeated_visitor_scope.twoHop.TailMap.b.TailMap.c
        with pytest.raises(AttributeError):
            repeated_visitor_scope.twoHop.TailMap.c.TailMap.a


# =============================================================================
# Intermediate computation scopes
# =============================================================================


class TestIntermediateScopes:
    """Test that intermediate computation scopes are valid."""

    def test_x_acceptance_is_scope(
        self, repeated_visitor_scope: Scope
    ) -> None:
        assert isinstance(repeated_visitor_scope._XAcceptance, Scope)

    def test_x_acceptance_has_accepted(
        self, repeated_visitor_scope: Scope
    ) -> None:
        assert isinstance(
            repeated_visitor_scope._XAcceptance.Accepted, Scope
        )
