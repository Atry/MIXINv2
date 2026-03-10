"""Tests for Pure Datalog corner cases in relational algebra examples.

Each example uses the same Datalog transitive closure program:
  path(X,Y) :- edge(X,Y).
  path(X,Y) :- edge(X,Z), path(Z,Y).

applied to different graph topologies that exercise specific Datalog
fixpoint behaviours:

- RelationalDiamond: convergent paths (DAG, no cycles)
- RelationalSelfLoop: self-referential edge (trivial cycle)
- RelationalBidirectional: 2-cycle deriving self-loops
- RelationalCycle: 3-cycle producing the complete graph
"""

import pytest

from mixinv2._runtime import Scope, evaluate

import mixinv2_examples
import mixinv2_library


# =============================================================================
# Fixtures
# =============================================================================


@pytest.fixture
def diamond_scope() -> Scope:
    """Load RelationalDiamond: edge(a,b), edge(a,c), edge(b,c)."""
    root = evaluate(mixinv2_library, mixinv2_examples, modules_public=True)
    result = root.RelationalDiamond
    assert isinstance(result, Scope)
    return result


@pytest.fixture
def self_loop_scope() -> Scope:
    """Load RelationalSelfLoop: edge(a,a)."""
    root = evaluate(mixinv2_library, mixinv2_examples, modules_public=True)
    result = root.RelationalSelfLoop
    assert isinstance(result, Scope)
    return result


@pytest.fixture
def bidirectional_scope() -> Scope:
    """Load RelationalBidirectional: edge(a,b), edge(b,a)."""
    root = evaluate(mixinv2_library, mixinv2_examples, modules_public=True)
    result = root.RelationalBidirectional
    assert isinstance(result, Scope)
    return result


@pytest.fixture
def cycle_scope() -> Scope:
    """Load RelationalCycle: edge(a,b), edge(b,c), edge(c,a)."""
    root = evaluate(mixinv2_library, mixinv2_examples, modules_public=True)
    result = root.RelationalCycle
    assert isinstance(result, Scope)
    return result


# =============================================================================
# Diamond: edge(a,b), edge(a,c), edge(b,c)
# Expected path: {(a,b), (a,c), (b,c)}
# =============================================================================


class TestDiamondEdge:
    """Test edge structure for diamond graph."""

    def test_edge_is_scope(self, diamond_scope: Scope) -> None:
        assert isinstance(diamond_scope.edge, Scope)

    def test_edge_a_branch_has_b(self, diamond_scope: Scope) -> None:
        """edge(a,b) — a-branch Tail contains b."""
        assert isinstance(diamond_scope.edge.TailMap.a.TailMap.b, Scope)

    def test_edge_a_branch_has_c(self, diamond_scope: Scope) -> None:
        """edge(a,c) — a-branch Tail also contains c (two edges from a)."""
        assert isinstance(diamond_scope.edge.TailMap.a.TailMap.c, Scope)

    def test_edge_b_branch_has_c(self, diamond_scope: Scope) -> None:
        """edge(b,c) — b-branch Tail contains c."""
        assert isinstance(diamond_scope.edge.TailMap.b.TailMap.c, Scope)

    def test_edge_has_no_c_first_column(self, diamond_scope: Scope) -> None:
        """No edge(c,...) — c is only a sink vertex."""
        with pytest.raises(AttributeError):
            diamond_scope.edge.TailMap.c


class TestDiamondPath:
    """Test path for diamond graph.

    path = {(a,b), (a,c), (b,c)}.
    path(a,c) has two derivations: direct edge AND edge(a,b)+path(b,c).
    The trie naturally deduplicates, producing the same result.
    """

    def test_path_is_scope(self, diamond_scope: Scope) -> None:
        assert isinstance(diamond_scope.path, Scope)

    def test_path_a_branch_has_b(self, diamond_scope: Scope) -> None:
        """path(a,b) exists."""
        assert isinstance(diamond_scope.path.TailMap.a.TailMap.b, Scope)

    def test_path_a_branch_has_c(self, diamond_scope: Scope) -> None:
        """path(a,c) exists — from both direct edge and transitive derivation."""
        assert isinstance(diamond_scope.path.TailMap.a.TailMap.c, Scope)

    def test_path_b_branch_has_c(self, diamond_scope: Scope) -> None:
        """path(b,c) exists."""
        assert isinstance(diamond_scope.path.TailMap.b.TailMap.c, Scope)

    def test_path_has_no_c_first_column(self, diamond_scope: Scope) -> None:
        """No path(c,...) — c is a sink with no outgoing edges."""
        with pytest.raises(AttributeError):
            diamond_scope.path.TailMap.c

    def test_path_equals_edge_for_diamond(self, diamond_scope: Scope) -> None:
        """For this DAG, path = edge (no new tuples beyond base edges).

        The transitive derivation edge(a,b)+path(b,c)→path(a,c) produces
        a tuple already present via the direct edge(a,c).
        """
        edge = diamond_scope.edge
        path = diamond_scope.path
        assert isinstance(edge.TailMap.a.TailMap.b, Scope)
        assert isinstance(edge.TailMap.a.TailMap.c, Scope)
        assert isinstance(edge.TailMap.b.TailMap.c, Scope)
        assert isinstance(path.TailMap.a.TailMap.b, Scope)
        assert isinstance(path.TailMap.a.TailMap.c, Scope)
        assert isinstance(path.TailMap.b.TailMap.c, Scope)


# =============================================================================
# Self-loop: edge(a,a)
# Expected path: {(a,a)}
# =============================================================================


class TestSelfLoopEdge:
    """Test edge structure for self-loop graph."""

    def test_edge_is_scope(self, self_loop_scope: Scope) -> None:
        assert isinstance(self_loop_scope.edge, Scope)

    def test_edge_a_branch_has_a(self, self_loop_scope: Scope) -> None:
        """edge(a,a) — a-branch Tail contains a (self-loop)."""
        assert isinstance(self_loop_scope.edge.TailMap.a.TailMap.a, Scope)

    def test_edge_has_no_b_first_column(self, self_loop_scope: Scope) -> None:
        """No edge(b,...) — only a has an edge."""
        with pytest.raises(AttributeError):
            self_loop_scope.edge.TailMap.b

    def test_edge_has_no_c_first_column(self, self_loop_scope: Scope) -> None:
        """No edge(c,...) — only a has an edge."""
        with pytest.raises(AttributeError):
            self_loop_scope.edge.TailMap.c


class TestSelfLoopPath:
    """Test path for self-loop graph.

    path = {(a,a)}.
    The recursive rule produces path(a,a) :- edge(a,a), path(a,a),
    which is the same as the base case — trivial fixpoint.
    """

    def test_path_is_scope(self, self_loop_scope: Scope) -> None:
        assert isinstance(self_loop_scope.path, Scope)

    def test_path_a_branch_has_a(self, self_loop_scope: Scope) -> None:
        """path(a,a) exists — the self-loop is reachable."""
        assert isinstance(self_loop_scope.path.TailMap.a.TailMap.a, Scope)

    def test_path_has_no_b_first_column(self, self_loop_scope: Scope) -> None:
        """No path(b,...) — b is unreachable."""
        with pytest.raises(AttributeError):
            self_loop_scope.path.TailMap.b

    def test_path_has_no_c_first_column(self, self_loop_scope: Scope) -> None:
        """No path(c,...) — c is unreachable."""
        with pytest.raises(AttributeError):
            self_loop_scope.path.TailMap.c

    def test_path_a_a_terminates_with_nil(self, self_loop_scope: Scope) -> None:
        """path(a, a, Nil) — the self-loop tuple terminates correctly."""
        path_a_a_tail = self_loop_scope.path.TailMap.a.TailMap.a
        assert isinstance(path_a_a_tail.Acceptance, Scope)
        assert isinstance(path_a_a_tail.Acceptance.Accepted, Scope)


# =============================================================================
# Bidirectional: edge(a,b), edge(b,a)
# Expected path: {(a,b), (b,a), (a,a), (b,b)}
# =============================================================================


class TestBidirectionalEdge:
    """Test edge structure for bidirectional graph."""

    def test_edge_is_scope(self, bidirectional_scope: Scope) -> None:
        assert isinstance(bidirectional_scope.edge, Scope)

    def test_edge_a_branch_has_b(self, bidirectional_scope: Scope) -> None:
        """edge(a,b) exists."""
        assert isinstance(bidirectional_scope.edge.TailMap.a.TailMap.b, Scope)

    def test_edge_b_branch_has_a(self, bidirectional_scope: Scope) -> None:
        """edge(b,a) exists."""
        assert isinstance(bidirectional_scope.edge.TailMap.b.TailMap.a, Scope)

    def test_edge_a_branch_lacks_a(self, bidirectional_scope: Scope) -> None:
        """No edge(a,a) — no direct self-loop on a."""
        with pytest.raises(AttributeError):
            bidirectional_scope.edge.TailMap.a.TailMap.a

    def test_edge_b_branch_lacks_b(self, bidirectional_scope: Scope) -> None:
        """No edge(b,b) — no direct self-loop on b."""
        with pytest.raises(AttributeError):
            bidirectional_scope.edge.TailMap.b.TailMap.b


class TestBidirectionalPath:
    """Test path for bidirectional graph.

    path = {(a,b), (b,a), (a,a), (b,b)}.
    Self-loops are derived transitively:
      path(a,a) :- edge(a,b), path(b,a).
      path(b,b) :- edge(b,a), path(a,b).
    """

    def test_path_is_scope(self, bidirectional_scope: Scope) -> None:
        assert isinstance(bidirectional_scope.path, Scope)

    def test_path_a_branch_has_b(self, bidirectional_scope: Scope) -> None:
        """path(a,b) exists — from base edge."""
        assert isinstance(bidirectional_scope.path.TailMap.a.TailMap.b, Scope)

    def test_path_b_branch_has_a(self, bidirectional_scope: Scope) -> None:
        """path(b,a) exists — from base edge."""
        assert isinstance(bidirectional_scope.path.TailMap.b.TailMap.a, Scope)

    def test_path_a_branch_has_a(self, bidirectional_scope: Scope) -> None:
        """path(a,a) exists — derived from edge(a,b) + path(b,a).

        This is the KEY test: self-loops are absent from edge but
        present in path, derived via the 2-cycle.
        """
        assert isinstance(bidirectional_scope.path.TailMap.a.TailMap.a, Scope)

    def test_path_b_branch_has_b(self, bidirectional_scope: Scope) -> None:
        """path(b,b) exists — derived from edge(b,a) + path(a,b).

        Symmetric to path(a,a): the other self-loop from the 2-cycle.
        """
        assert isinstance(bidirectional_scope.path.TailMap.b.TailMap.b, Scope)

    def test_path_has_no_c(self, bidirectional_scope: Scope) -> None:
        """No path involving c — c is disconnected."""
        with pytest.raises(AttributeError):
            bidirectional_scope.path.TailMap.c


class TestBidirectionalTransitiveClosure:
    """Verify bidirectional edges derive self-loops absent from edge."""

    def test_edge_lacks_self_loop_a(self, bidirectional_scope: Scope) -> None:
        """edge does NOT have (a,a)."""
        with pytest.raises(AttributeError):
            bidirectional_scope.edge.TailMap.a.TailMap.a

    def test_path_has_self_loop_a(self, bidirectional_scope: Scope) -> None:
        """path DOES have (a,a) — derived via 2-cycle."""
        assert isinstance(bidirectional_scope.path.TailMap.a.TailMap.a, Scope)

    def test_edge_lacks_self_loop_b(self, bidirectional_scope: Scope) -> None:
        """edge does NOT have (b,b)."""
        with pytest.raises(AttributeError):
            bidirectional_scope.edge.TailMap.b.TailMap.b

    def test_path_has_self_loop_b(self, bidirectional_scope: Scope) -> None:
        """path DOES have (b,b) — derived via 2-cycle."""
        assert isinstance(bidirectional_scope.path.TailMap.b.TailMap.b, Scope)


# =============================================================================
# Cycle: edge(a,b), edge(b,c), edge(c,a)
# Expected path: all 9 pairs (complete graph including self-loops)
# =============================================================================


class TestCycleEdge:
    """Test edge structure for 3-cycle graph."""

    def test_edge_is_scope(self, cycle_scope: Scope) -> None:
        assert isinstance(cycle_scope.edge, Scope)

    def test_edge_a_to_b(self, cycle_scope: Scope) -> None:
        """edge(a,b) exists."""
        assert isinstance(cycle_scope.edge.TailMap.a.TailMap.b, Scope)

    def test_edge_b_to_c(self, cycle_scope: Scope) -> None:
        """edge(b,c) exists."""
        assert isinstance(cycle_scope.edge.TailMap.b.TailMap.c, Scope)

    def test_edge_c_to_a(self, cycle_scope: Scope) -> None:
        """edge(c,a) exists."""
        assert isinstance(cycle_scope.edge.TailMap.c.TailMap.a, Scope)

    def test_edge_a_lacks_c(self, cycle_scope: Scope) -> None:
        """No direct edge(a,c)."""
        with pytest.raises(AttributeError):
            cycle_scope.edge.TailMap.a.TailMap.c

    def test_edge_b_lacks_a(self, cycle_scope: Scope) -> None:
        """No direct edge(b,a)."""
        with pytest.raises(AttributeError):
            cycle_scope.edge.TailMap.b.TailMap.a

    def test_edge_c_lacks_b(self, cycle_scope: Scope) -> None:
        """No direct edge(c,b)."""
        with pytest.raises(AttributeError):
            cycle_scope.edge.TailMap.c.TailMap.b


class TestCyclePath:
    """Test path for 3-cycle graph.

    The transitive closure of a 3-cycle is the complete directed graph
    on {a, b, c}, including all 9 pairs (with self-loops):
      {(a,a), (a,b), (a,c), (b,a), (b,b), (b,c), (c,a), (c,b), (c,c)}

    Derivation of non-edge pairs:
      path(a,c) :- edge(a,b), path(b,c).
      path(b,a) :- edge(b,c), path(c,a).
      path(c,b) :- edge(c,a), path(a,b).
      path(a,a) :- edge(a,b), path(b,a).  (requires two recursive steps)
      path(b,b) :- edge(b,c), path(c,b).  (requires two recursive steps)
      path(c,c) :- edge(c,a), path(a,c).  (requires two recursive steps)
    """

    def test_path_is_scope(self, cycle_scope: Scope) -> None:
        assert isinstance(cycle_scope.path, Scope)

    # --- a-branch: path(a, {a, b, c}) ---

    def test_path_a_to_a(self, cycle_scope: Scope) -> None:
        """path(a,a) — self-loop derived via a→b→c→a."""
        assert isinstance(cycle_scope.path.TailMap.a.TailMap.a, Scope)

    def test_path_a_to_b(self, cycle_scope: Scope) -> None:
        """path(a,b) — from base edge."""
        assert isinstance(cycle_scope.path.TailMap.a.TailMap.b, Scope)

    def test_path_a_to_c(self, cycle_scope: Scope) -> None:
        """path(a,c) — derived from edge(a,b) + path(b,c)."""
        assert isinstance(cycle_scope.path.TailMap.a.TailMap.c, Scope)

    # --- b-branch: path(b, {a, b, c}) ---

    def test_path_b_to_a(self, cycle_scope: Scope) -> None:
        """path(b,a) — derived from edge(b,c) + path(c,a)."""
        assert isinstance(cycle_scope.path.TailMap.b.TailMap.a, Scope)

    def test_path_b_to_b(self, cycle_scope: Scope) -> None:
        """path(b,b) — self-loop derived via b→c→a→b."""
        assert isinstance(cycle_scope.path.TailMap.b.TailMap.b, Scope)

    def test_path_b_to_c(self, cycle_scope: Scope) -> None:
        """path(b,c) — from base edge."""
        assert isinstance(cycle_scope.path.TailMap.b.TailMap.c, Scope)

    # --- c-branch: path(c, {a, b, c}) ---

    def test_path_c_to_a(self, cycle_scope: Scope) -> None:
        """path(c,a) — from base edge."""
        assert isinstance(cycle_scope.path.TailMap.c.TailMap.a, Scope)

    def test_path_c_to_b(self, cycle_scope: Scope) -> None:
        """path(c,b) — derived from edge(c,a) + path(a,b)."""
        assert isinstance(cycle_scope.path.TailMap.c.TailMap.b, Scope)

    def test_path_c_to_c(self, cycle_scope: Scope) -> None:
        """path(c,c) — self-loop derived via c→a→b→c."""
        assert isinstance(cycle_scope.path.TailMap.c.TailMap.c, Scope)


class TestCycleTransitiveClosure:
    """Verify the 3-cycle derives pairs absent from edge."""

    def test_edge_lacks_a_to_c(self, cycle_scope: Scope) -> None:
        """No direct edge(a,c)."""
        with pytest.raises(AttributeError):
            cycle_scope.edge.TailMap.a.TailMap.c

    def test_path_has_a_to_c(self, cycle_scope: Scope) -> None:
        """path(a,c) derived transitively."""
        assert isinstance(cycle_scope.path.TailMap.a.TailMap.c, Scope)

    def test_edge_lacks_self_loops(self, cycle_scope: Scope) -> None:
        """No self-loops in edge."""
        with pytest.raises(AttributeError):
            cycle_scope.edge.TailMap.a.TailMap.a
        with pytest.raises(AttributeError):
            cycle_scope.edge.TailMap.b.TailMap.b
        with pytest.raises(AttributeError):
            cycle_scope.edge.TailMap.c.TailMap.c

    def test_path_has_all_self_loops(self, cycle_scope: Scope) -> None:
        """All self-loops present in path — derived via the 3-cycle."""
        assert isinstance(cycle_scope.path.TailMap.a.TailMap.a, Scope)
        assert isinstance(cycle_scope.path.TailMap.b.TailMap.b, Scope)
        assert isinstance(cycle_scope.path.TailMap.c.TailMap.c, Scope)
