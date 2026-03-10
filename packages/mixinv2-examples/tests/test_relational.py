"""Tests for relational algebra example.

Tests the Relational.mixin.yaml which implements Datalog-style relational algebra
using the RepeatedVisitor encoding (TailMap-based navigation):
- edge(a,b) and edge(b,c) as base facts
- path(X,Y) :- edge(X,Y)  (base case: every edge is a path)
- path(X,Y) :- edge(X,Z), path(Z,Y)  (recursive: transitive closure)

Verifies that path correctly computes the transitive closure of edge,
producing path(a,b), path(b,c), and the derived path(a,c).
"""

import pytest

from mixinv2._runtime import Scope, evaluate

import mixinv2_examples
import mixinv2_library


# =============================================================================
# Fixtures
# =============================================================================


@pytest.fixture
def relational_scope() -> Scope:
    """Load and evaluate the Relational example."""
    root = evaluate(mixinv2_library, mixinv2_examples, modules_public=True)
    result = root.Relational
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


# =============================================================================
# Edge relation: {(a,b), (b,c)}
# =============================================================================


class TestEdgeStructure:
    """Test the structural properties of the edge relation."""

    def test_edge_is_scope(self, relational_scope: Scope) -> None:
        assert isinstance(relational_scope.edge, Scope)

    def test_edge_has_tail(self, relational_scope: Scope) -> None:
        """edge.Tail is the union of second columns across all rows."""
        assert isinstance(relational_scope.edge.Tail, Scope)

    def test_edge_has_acceptance(self, relational_scope: Scope) -> None:
        edge = relational_scope.edge
        assert isinstance(edge.Acceptance, Scope)
        assert isinstance(edge.Acceptance.Accepted, Scope)


class TestEdgeColumns:
    """Test that edge contains exactly the expected column branches.

    edge = {(a,b), (b,c)}, so:
    - First column: {a, b}
    - No c in first column (c is only a second-column value)
    """

    def test_edge_has_a_branch(self, relational_scope: Scope) -> None:
        """edge(a,...) exists."""
        assert isinstance(relational_scope.edge.TailMap.a, Scope)

    def test_edge_has_b_branch(self, relational_scope: Scope) -> None:
        """edge(b,...) exists."""
        assert isinstance(relational_scope.edge.TailMap.b, Scope)

    def test_edge_has_no_c_first_column(self, relational_scope: Scope) -> None:
        """No edge(c,...) exists."""
        with pytest.raises(AttributeError):
            relational_scope.edge.TailMap.c

    def test_edge_a_b(self, relational_scope: Scope) -> None:
        """edge(a, b) exists."""
        assert isinstance(relational_scope.edge.TailMap.a.TailMap.b, Scope)

    def test_edge_a_not_c(self, relational_scope: Scope) -> None:
        """edge(a, c) does not exist."""
        with pytest.raises(AttributeError):
            relational_scope.edge.TailMap.a.TailMap.c

    def test_edge_b_c(self, relational_scope: Scope) -> None:
        """edge(b, c) exists."""
        assert isinstance(relational_scope.edge.TailMap.b.TailMap.c, Scope)

    def test_edge_complete_set(self, relational_scope: Scope) -> None:
        """edge contains exactly {(a,b), (b,c)}."""
        pairs = _collect_pairs(relational_scope.edge)
        assert pairs == {("a", "b"), ("b", "c")}


# =============================================================================
# Path relation: transitive closure = {(a,b), (b,c), (a,c)}
# =============================================================================


class TestPathStructure:
    """Test the structural properties of the path relation."""

    def test_path_is_scope(self, relational_scope: Scope) -> None:
        assert isinstance(relational_scope.path, Scope)

    def test_path_has_acceptance(self, relational_scope: Scope) -> None:
        path = relational_scope.path
        assert isinstance(path.Acceptance, Scope)
        assert isinstance(path.Acceptance.Accepted, Scope)


class TestPathColumns:
    """Test that path contains the transitive closure columns.

    path = {(a,b), (b,c), (a,c)}, so:
    - First column: {a, b} (same as edge — no new first-column values)
    - No c in first column (c is only a sink vertex)
    - a-branch second column: {b, c} (both path(a,b) and path(a,c))
    - b-branch second column: {c} (only path(b,c))
    """

    def test_path_has_a_branch(self, relational_scope: Scope) -> None:
        """path(a,...) exists."""
        assert isinstance(relational_scope.path.TailMap.a, Scope)

    def test_path_has_b_branch(self, relational_scope: Scope) -> None:
        """path(b,...) exists."""
        assert isinstance(relational_scope.path.TailMap.b, Scope)

    def test_path_has_no_c_first_column(self, relational_scope: Scope) -> None:
        """No path(c,...) exists — c is a sink vertex."""
        with pytest.raises(AttributeError):
            relational_scope.path.TailMap.c

    def test_path_a_b(self, relational_scope: Scope) -> None:
        """path(a, b) exists — from base edge."""
        assert isinstance(relational_scope.path.TailMap.a.TailMap.b, Scope)

    def test_path_a_c(self, relational_scope: Scope) -> None:
        """path(a, c) exists via transitive closure.

        This is the KEY test for transitive closure correctness:
        edge only has (a,b) and (b,c), so path(a,c) is derived from
        edge(a,b) + path(b,c) → path(a,c).
        """
        assert isinstance(relational_scope.path.TailMap.a.TailMap.c, Scope)

    def test_path_b_c(self, relational_scope: Scope) -> None:
        """path(b, c) exists — from base edge."""
        assert isinstance(relational_scope.path.TailMap.b.TailMap.c, Scope)

    def test_path_complete_set(self, relational_scope: Scope) -> None:
        """path contains exactly {(a,b), (b,c), (a,c)}."""
        pairs = _collect_pairs(relational_scope.path)
        assert pairs == {("a", "b"), ("b", "c"), ("a", "c")}


class TestTransitiveClosureCompleteness:
    """Verify the transitive closure adds path(a,c) which is absent from edge.

    This is the core correctness property: path = edge + derived tuples.
    The only derived tuple in this example is (a,c), obtained from
    edge(a,b) + path(b,c) → path(a,c).
    """

    def test_edge_a_lacks_c(self, relational_scope: Scope) -> None:
        """edge does NOT have (a,c) — no direct edge from a to c."""
        with pytest.raises(AttributeError):
            relational_scope.edge.TailMap.a.TailMap.c

    def test_path_a_has_c(self, relational_scope: Scope) -> None:
        """path DOES have (a,c) — derived via transitive closure."""
        assert isinstance(relational_scope.path.TailMap.a.TailMap.c, Scope)


# =============================================================================
# Intermediate computation scopes
# =============================================================================


class TestIntermediateScopes:
    """Test that intermediate computation scopes used by path rules are valid.

    These scopes are implementation details of the Datalog rules but are
    accessible when modules_public=True is used for evaluation.
    """

    def test_base_x_acceptance_is_scope(self, relational_scope: Scope) -> None:
        """_BaseXAcceptance implements path(X,Y) :- edge(X,Y)."""
        assert isinstance(relational_scope._BaseXAcceptance, Scope)

    def test_recursive_x_acceptance_is_scope(
        self, relational_scope: Scope
    ) -> None:
        """_RecursiveXAcceptance implements path(X,Y) :- edge(X,Z), path(Z,Y)."""
        assert isinstance(relational_scope._RecursiveXAcceptance, Scope)
