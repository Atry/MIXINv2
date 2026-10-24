"""Tests for RelationalTwoHopRepeatedVisitor.mixin.yaml.

Graph: a -> b -> c -> a (3-cycle)

Facts:
  edge(a,b).
  edge(b,c).
  edge(c,a).

Rule:
  twoHop(X,Z) := edge(X,Y), edge(Y,Z).

This encoding uses repeated __Acceptance/__Visitor pattern to perform
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
    """Navigate __TailMap.<entity> on a scope."""
    return getattr(scope["__TailMap"], entity)


def _collect_pairs(relation: Scope) -> set[tuple[str, str]]:
    """Enumerate all (first, second) pairs present in a binary relation trie.

    Navigates via __TailMap.<entity> for each column.
    """
    pairs: set[tuple[str, str]] = set()
    for first in CONSTANTS:
        for second in CONSTANTS:
            try:
                tail1 = _get_tail_map_entry(relation, first)
                _get_tail_map_entry(tail1, second)
                pairs.add((first, second))
            except (AttributeError, KeyError):
                pass
    return pairs


# =============================================================================
# Evaluation: the mixin.yaml must load without errors
# =============================================================================


class TestEvaluation:
    """Test that RelationalTwoHopRepeatedVisitor evaluates without errors.

    Currently fails with:
      ValueError: Cannot navigate path ('__VisitorMap', 'a', '__Visited'):
      ('RelationalTwoHopRepeatedVisitor', 'a', '__Acceptance', '__VisitorMap')
      (unexpected kind CONFLICT) has no child 'a'

    The root cause is in constant 'a' __Acceptance definition (lines 49-54):
    the __VisitorMap uses list syntax (- a: [__Visitor]) creating a CONFLICT
    with the __VisitorMap inherited from __Relation, while constants 'b' and 'c'
    use plain mapping syntax (__VisitorMap: b: [__Visitor]) which works correctly.
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
            repeated_visitor_scope.edge["__TailMap"].a["__TailMap"].b, Scope
        )

    def test_edge_b_c(self, repeated_visitor_scope: Scope) -> None:
        """edge(b,c) exists."""
        assert isinstance(
            repeated_visitor_scope.edge["__TailMap"].b["__TailMap"].c, Scope
        )

    def test_edge_c_a(self, repeated_visitor_scope: Scope) -> None:
        """edge(c,a) exists."""
        assert isinstance(
            repeated_visitor_scope.edge["__TailMap"].c["__TailMap"].a, Scope
        )

    def test_edge_exactly_3_pairs(self, repeated_visitor_scope: Scope) -> None:
        """edge contains exactly {(a,b), (b,c), (c,a)}."""
        pairs = _collect_pairs(repeated_visitor_scope.edge)
        expected = {("a", "b"), ("b", "c"), ("c", "a")}
        assert pairs == expected


# =============================================================================
# __Relation infrastructure
# =============================================================================


class TestRelationInfrastructure:
    """Test that __Relation, __Cons, __Nil, and constants are defined."""

    def test_relation_is_scope(self, repeated_visitor_scope: Scope) -> None:
        assert isinstance(repeated_visitor_scope["__Relation"], Scope)

    def test_nil_is_scope(self, repeated_visitor_scope: Scope) -> None:
        assert isinstance(repeated_visitor_scope["__Nil"], Scope)

    def test_cons_is_scope(self, repeated_visitor_scope: Scope) -> None:
        assert isinstance(repeated_visitor_scope["__Cons"], Scope)

    def test_constant_a_is_scope(self, repeated_visitor_scope: Scope) -> None:
        assert isinstance(repeated_visitor_scope.a, Scope)

    def test_constant_b_is_scope(self, repeated_visitor_scope: Scope) -> None:
        assert isinstance(repeated_visitor_scope.b, Scope)

    def test_constant_c_is_scope(self, repeated_visitor_scope: Scope) -> None:
        assert isinstance(repeated_visitor_scope.c, Scope)


# =============================================================================
# __Acceptance/__Visitor pattern on constants
# =============================================================================


class TestConstantAcceptance:
    """Test that each constant has a working __Acceptance/__Visitor."""

    def test_a_has_acceptance(self, repeated_visitor_scope: Scope) -> None:
        assert isinstance(repeated_visitor_scope.a["__Acceptance"], Scope)
        assert isinstance(repeated_visitor_scope.a["__Acceptance"]["__Accepted"], Scope)

    def test_b_has_acceptance(self, repeated_visitor_scope: Scope) -> None:
        assert isinstance(repeated_visitor_scope.b["__Acceptance"], Scope)
        assert isinstance(repeated_visitor_scope.b["__Acceptance"]["__Accepted"], Scope)

    def test_c_has_acceptance(self, repeated_visitor_scope: Scope) -> None:
        assert isinstance(repeated_visitor_scope.c["__Acceptance"], Scope)
        assert isinstance(repeated_visitor_scope.c["__Acceptance"]["__Accepted"], Scope)

    def test_nil_has_acceptance(self, repeated_visitor_scope: Scope) -> None:
        assert isinstance(repeated_visitor_scope["__Nil"]["__Acceptance"], Scope)
        assert isinstance(
            repeated_visitor_scope["__Nil"]["__Acceptance"]["__Accepted"], Scope
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
            repeated_visitor_scope.twoHop["__TailMap"].a["__TailMap"].c, Scope
        )

    def test_two_hop_b_a(self, repeated_visitor_scope: Scope) -> None:
        """edge(b,c), edge(c,a) -> twoHop(b,a)."""
        assert isinstance(
            repeated_visitor_scope.twoHop["__TailMap"].b["__TailMap"].a, Scope
        )

    def test_two_hop_c_b(self, repeated_visitor_scope: Scope) -> None:
        """edge(c,a), edge(a,b) -> twoHop(c,b)."""
        assert isinstance(
            repeated_visitor_scope.twoHop["__TailMap"].c["__TailMap"].b, Scope
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
        with pytest.raises((AttributeError, KeyError)):
            repeated_visitor_scope.twoHop["__TailMap"].a["__TailMap"].a
        with pytest.raises((AttributeError, KeyError)):
            repeated_visitor_scope.twoHop["__TailMap"].b["__TailMap"].b
        with pytest.raises((AttributeError, KeyError)):
            repeated_visitor_scope.twoHop["__TailMap"].c["__TailMap"].c

    def test_two_hop_no_identity_pairs(
        self, repeated_visitor_scope: Scope
    ) -> None:
        """No identity-edge pairs: twoHop(a,b), twoHop(b,c), twoHop(c,a) should not exist.

        These would be the original edges, not two-hop paths.
        """
        with pytest.raises((AttributeError, KeyError)):
            repeated_visitor_scope.twoHop["__TailMap"].a["__TailMap"].b
        with pytest.raises((AttributeError, KeyError)):
            repeated_visitor_scope.twoHop["__TailMap"].b["__TailMap"].c
        with pytest.raises((AttributeError, KeyError)):
            repeated_visitor_scope.twoHop["__TailMap"].c["__TailMap"].a


# =============================================================================
# Intermediate computation scopes
# =============================================================================


class TestIntermediateScopes:
    """Test that intermediate computation scopes are valid."""

    def test_x_acceptance_is_scope(
        self, repeated_visitor_scope: Scope
    ) -> None:
        assert isinstance(repeated_visitor_scope["__XAcceptance"], Scope)

    def test_x_acceptance_has_accepted(
        self, repeated_visitor_scope: Scope
    ) -> None:
        assert isinstance(
            repeated_visitor_scope["__XAcceptance"]["__Accepted"], Scope
        )
