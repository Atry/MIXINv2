"""Tests for extended Datalog rule patterns in relational algebra examples.

Tests four patterns not covered by existing test suites:

- RelationalThreeWayJoin: 3-body rule with chained joins
  chain(X,W) :- alpha(X,Y), beta(Y,Z), gamma(Z,W)

- RelationalConstant: rule with constant matches and variables
  viaB(X,Z) :- edge(X,b), edge(b,Z)

- RelationalConstantJoin: 3-body rule mixing constant matches and variable joins
  constJoin(X,W) :- edge(X,Y), edge(Y,b), edge(b,W)

- RelationalMultiVariableJoin: join on multiple variables simultaneously
  multiJoin(X,Y) :- r(X,Y), s(X,Y)

All files use the RepeatedVisitor encoding with TailMap navigation.
"""

import pytest

from mixinv2._runtime import Scope, evaluate

import mixinv2_examples
import mixinv2_library


# =============================================================================
# Fixtures
# =============================================================================


@pytest.fixture
def three_way_join_scope() -> Scope:
    """Load RelationalThreeWayJoin.

    alpha(a,b), alpha(c,b), beta(b,a), beta(b,c), gamma(a,b), gamma(c,a).
    """
    root = evaluate(mixinv2_library, mixinv2_examples, modules_public=True)
    result = root.RelationalThreeWayJoin
    assert isinstance(result, Scope)
    return result


@pytest.fixture
def constant_scope() -> Scope:
    """Load RelationalConstant.

    edge(a,b), edge(b,c).
    """
    root = evaluate(mixinv2_library, mixinv2_examples, modules_public=True)
    result = root.RelationalConstant
    assert isinstance(result, Scope)
    return result


@pytest.fixture
def constant_join_scope() -> Scope:
    """Load RelationalConstantJoin.

    edge(a,b), edge(b,c), edge(c,a).
    """
    root = evaluate(mixinv2_library, mixinv2_examples, modules_public=True)
    result = root.RelationalConstantJoin
    assert isinstance(result, Scope)
    return result


@pytest.fixture
def multi_variable_join_scope() -> Scope:
    """Load RelationalMultiVariableJoin.

    r(a,b), r(b,c), s(a,c), s(b,a).
    """
    root = evaluate(mixinv2_library, mixinv2_examples, modules_public=True)
    result = root.RelationalMultiVariableJoin
    assert isinstance(result, Scope)
    return result


# =============================================================================
# Helpers
# =============================================================================


def _collect_pairs_tailmap(relation: Scope) -> set[tuple[str, str]]:
    """Enumerate all (first, second) pairs in a TailMap-encoded relation."""
    pairs: set[tuple[str, str]] = set()
    for first in ("a", "b", "c"):
        for second in ("a", "b", "c"):
            try:
                tail1 = getattr(relation.TailMap, first)
                getattr(tail1.TailMap, second)
                pairs.add((first, second))
            except AttributeError:
                pass
    return pairs


# =============================================================================
# Three-Way Join: chain(X,W) :- alpha(X,Y), beta(Y,Z), gamma(Z,W).
#
# alpha = {(a,b), (c,b)}, beta = {(b,a), (b,c)}, gamma = {(a,b), (c,a)}
#
# Datalog-correct derivation:
#   alpha(a,b) + beta(b,a) + gamma(a,b) → chain(a,b)
#   alpha(a,b) + beta(b,c) + gamma(c,a) → chain(a,a)
#   alpha(c,b) + beta(b,a) + gamma(a,b) → chain(c,b)
#   alpha(c,b) + beta(b,c) + gamma(c,a) → chain(c,a)
#   Result: {(a,a), (a,b), (c,a), (c,b)}
# =============================================================================


class TestThreeWayJoinAlpha:
    """Verify alpha relation facts."""

    def test_alpha_a_b(self, three_way_join_scope: Scope) -> None:
        assert isinstance(three_way_join_scope.alpha.TailMap.a.TailMap.b, Scope)

    def test_alpha_c_b(self, three_way_join_scope: Scope) -> None:
        assert isinstance(three_way_join_scope.alpha.TailMap.c.TailMap.b, Scope)

    def test_alpha_lacks_b_first_column(self, three_way_join_scope: Scope) -> None:
        """No alpha(b,...) — b is not a first-column entity in alpha."""
        with pytest.raises(AttributeError):
            three_way_join_scope.alpha.TailMap.b


class TestThreeWayJoinBeta:
    """Verify beta relation facts."""

    def test_beta_b_a(self, three_way_join_scope: Scope) -> None:
        assert isinstance(three_way_join_scope.beta.TailMap.b.TailMap.a, Scope)

    def test_beta_b_c(self, three_way_join_scope: Scope) -> None:
        assert isinstance(three_way_join_scope.beta.TailMap.b.TailMap.c, Scope)

    def test_beta_lacks_a_first_column(self, three_way_join_scope: Scope) -> None:
        """No beta(a,...) — only b is a first-column entity in beta."""
        with pytest.raises(AttributeError):
            three_way_join_scope.beta.TailMap.a


class TestThreeWayJoinGamma:
    """Verify gamma relation facts."""

    def test_gamma_a_b(self, three_way_join_scope: Scope) -> None:
        assert isinstance(three_way_join_scope.gamma.TailMap.a.TailMap.b, Scope)

    def test_gamma_c_a(self, three_way_join_scope: Scope) -> None:
        assert isinstance(three_way_join_scope.gamma.TailMap.c.TailMap.a, Scope)

    def test_gamma_lacks_b_first_column(self, three_way_join_scope: Scope) -> None:
        """No gamma(b,...) — b is not a first-column entity in gamma."""
        with pytest.raises(AttributeError):
            three_way_join_scope.gamma.TailMap.b


class TestThreeWayJoinChain:
    """Verify chain (Datalog-correct) = {(a,a), (a,b), (c,a), (c,b)}.

    The three-way join chains two value-level acceptances:
      1. Y join: alpha's second col against beta's first col
      2. Z join: beta's second col against gamma's first col
    On both matches, output (alpha_X, gamma_W).
    """

    def test_chain_complete_set(self, three_way_join_scope: Scope) -> None:
        """chain contains exactly 4 pairs."""
        pairs = _collect_pairs_tailmap(three_way_join_scope.chain)
        expected = {("a", "a"), ("a", "b"), ("c", "a"), ("c", "b")}
        assert pairs == expected

    def test_chain_a_a(self, three_way_join_scope: Scope) -> None:
        """alpha(a,b) + beta(b,c) + gamma(c,a) → chain(a,a)."""
        assert isinstance(three_way_join_scope.chain.TailMap.a.TailMap.a, Scope)

    def test_chain_a_b(self, three_way_join_scope: Scope) -> None:
        """alpha(a,b) + beta(b,a) + gamma(a,b) → chain(a,b)."""
        assert isinstance(three_way_join_scope.chain.TailMap.a.TailMap.b, Scope)

    def test_chain_c_a(self, three_way_join_scope: Scope) -> None:
        """alpha(c,b) + beta(b,c) + gamma(c,a) → chain(c,a)."""
        assert isinstance(three_way_join_scope.chain.TailMap.c.TailMap.a, Scope)

    def test_chain_c_b(self, three_way_join_scope: Scope) -> None:
        """alpha(c,b) + beta(b,a) + gamma(a,b) → chain(c,b)."""
        assert isinstance(three_way_join_scope.chain.TailMap.c.TailMap.b, Scope)

    def test_chain_lacks_b_first_column(self, three_way_join_scope: Scope) -> None:
        """No chain(b,...) — b is not in alpha's first column."""
        with pytest.raises(AttributeError):
            three_way_join_scope.chain.TailMap.b

    def test_chain_lacks_c_second_column(self, three_way_join_scope: Scope) -> None:
        """No chain(a,c) — c is not in gamma's second column."""
        with pytest.raises(AttributeError):
            three_way_join_scope.chain.TailMap.a.TailMap.c


# =============================================================================
# Constant Rule: viaB(X,Z) :- edge(X,b), edge(b,Z).
#
# edge = {(a,b), (b,c)}
#
# Datalog-correct derivation:
#   edge(X,b): only edge(a,b) has b in second col → X=a
#   edge(b,Z): edge(b,c) → Z=c
#   Result: {(a,c)}
#
# This encoding uses RepeatedVisitor (value-level join, Datalog-correct).
# =============================================================================


class TestConstantEdge:
    """Verify edge facts for constant rule example."""

    def test_edge_a_b(self, constant_scope: Scope) -> None:
        assert isinstance(constant_scope.edge.TailMap.a.TailMap.b, Scope)

    def test_edge_b_c(self, constant_scope: Scope) -> None:
        assert isinstance(constant_scope.edge.TailMap.b.TailMap.c, Scope)

    def test_edge_lacks_c_first_column(self, constant_scope: Scope) -> None:
        """No edge(c,...) — c is not a first-column entity."""
        with pytest.raises(AttributeError):
            constant_scope.edge.TailMap.c


class TestConstantViaB:
    """Verify viaB = {(a,c)} (Datalog-correct).

    Value-level join ensures only tuples where Y is actually b match.
    """

    def test_via_b_complete_set(self, constant_scope: Scope) -> None:
        """viaB contains exactly 1 pair (Datalog-correct)."""
        pairs = _collect_pairs_tailmap(constant_scope.viaB)
        expected = {("a", "c")}
        assert pairs == expected

    def test_via_b_a_c(self, constant_scope: Scope) -> None:
        """edge(a,b) + edge(b,c) → viaB(a,c)."""
        assert isinstance(constant_scope.viaB.TailMap.a.TailMap.c, Scope)

    def test_via_b_lacks_b_first_column(self, constant_scope: Scope) -> None:
        """No viaB(b,...) — b is not in edge(X,b)'s X when Y=b is required."""
        with pytest.raises(AttributeError):
            constant_scope.viaB.TailMap.b

    def test_via_b_lacks_c_first_column(self, constant_scope: Scope) -> None:
        """No viaB(c,...) — c not in edge's first column."""
        with pytest.raises(AttributeError):
            constant_scope.viaB.TailMap.c


# =============================================================================
# Constant Match + Join: constJoin(X,W) :- edge(X,Y), edge(Y,b), edge(b,W).
#
# edge = {(a,b), (b,c), (c,a)} (3-cycle)
#
# Datalog-correct derivation:
#   edge(Y,b) means Y's row has b in second col → only edge(a,b): Y=a
#   edge(X,Y=a): edge(c,a) → X=c
#   edge(b,W): edge(b,c) → W=c
#   Result: {(c,c)}
#
# This encoding uses RepeatedVisitor (value-level join, Datalog-correct).
# =============================================================================


class TestConstantJoinEdge:
    """Verify 3-cycle edge facts for constant join example."""

    def test_edge_a_b(self, constant_join_scope: Scope) -> None:
        assert isinstance(constant_join_scope.edge.TailMap.a.TailMap.b, Scope)

    def test_edge_b_c(self, constant_join_scope: Scope) -> None:
        assert isinstance(constant_join_scope.edge.TailMap.b.TailMap.c, Scope)

    def test_edge_c_a(self, constant_join_scope: Scope) -> None:
        assert isinstance(constant_join_scope.edge.TailMap.c.TailMap.a, Scope)


class TestConstantJoinResult:
    """Verify constJoin = {(c,c)} (Datalog-correct)."""

    def test_const_join_complete_set(self, constant_join_scope: Scope) -> None:
        pairs = _collect_pairs_tailmap(constant_join_scope.constJoin)
        expected = {("c", "c")}
        assert pairs == expected

    def test_const_join_c_c(self, constant_join_scope: Scope) -> None:
        assert isinstance(constant_join_scope.constJoin.TailMap.c.TailMap.c, Scope)

    def test_const_join_lacks_a_first_column(
        self, constant_join_scope: Scope
    ) -> None:
        """No constJoin(a,...) — edge(X,Y=a) requires edge(a,b),
        but edge(Y=a,b) means Y=a, and then edge(a,b) has b≠b check fails."""
        with pytest.raises(AttributeError):
            constant_join_scope.constJoin.TailMap.a

    def test_const_join_lacks_b_first_column(
        self, constant_join_scope: Scope
    ) -> None:
        """No constJoin(b,...) — no edge(X,Y) where edge(Y,b) holds and X=b."""
        with pytest.raises(AttributeError):
            constant_join_scope.constJoin.TailMap.b


class TestConstantJoinVsUnconstrained:
    """Verify the constant restricts output compared to unconstrained."""

    def test_const_join_lacks_non_c_pairs(self, constant_join_scope: Scope) -> None:
        """Only (c,c) should be present."""
        pairs = _collect_pairs_tailmap(constant_join_scope.constJoin)
        assert pairs == {("c", "c")}

    def test_const_join_w_restricted_to_c(self, constant_join_scope: Scope) -> None:
        """W is always c — edge(b,W) only has W=c."""
        with pytest.raises(AttributeError):
            constant_join_scope.constJoin.TailMap.c.TailMap.a
        with pytest.raises(AttributeError):
            constant_join_scope.constJoin.TailMap.c.TailMap.b


# =============================================================================
# Multi-Variable Join: multiJoin(X,Y) :- r(X,Y), s(X,Y).
#
# r = {(a,b), (b,c)}, s = {(a,c), (b,a)}
#
# Standard Datalog intersection r ∩ s = {} (no common tuples).
# Value-level join correctly produces empty result.
# =============================================================================


class TestMultiVariableJoinR:
    """Verify r relation facts."""

    def test_r_a_b(self, multi_variable_join_scope: Scope) -> None:
        assert isinstance(multi_variable_join_scope.r.TailMap.a.TailMap.b, Scope)

    def test_r_b_c(self, multi_variable_join_scope: Scope) -> None:
        assert isinstance(multi_variable_join_scope.r.TailMap.b.TailMap.c, Scope)

    def test_r_lacks_c_first_column(self, multi_variable_join_scope: Scope) -> None:
        with pytest.raises(AttributeError):
            multi_variable_join_scope.r.TailMap.c


class TestMultiVariableJoinS:
    """Verify s relation facts."""

    def test_s_a_c(self, multi_variable_join_scope: Scope) -> None:
        assert isinstance(multi_variable_join_scope.s.TailMap.a.TailMap.c, Scope)

    def test_s_b_a(self, multi_variable_join_scope: Scope) -> None:
        assert isinstance(multi_variable_join_scope.s.TailMap.b.TailMap.a, Scope)

    def test_s_lacks_c_first_column(self, multi_variable_join_scope: Scope) -> None:
        with pytest.raises(AttributeError):
            multi_variable_join_scope.s.TailMap.c


class TestMultiVariableJoinResult:
    """Verify multiJoin = {} (Datalog-correct intersection).

    Value-level join matches r and s on both X and Y simultaneously.
    r = {(a,b), (b,c)}, s = {(a,c), (b,a)}: no common tuples.
    Result is empty because no (X,Y) pair exists in both r and s.
    """

    def test_multi_join_empty(self, multi_variable_join_scope: Scope) -> None:
        """multiJoin is empty — no common tuples between r and s."""
        pairs = _collect_pairs_tailmap(multi_variable_join_scope.multiJoin)
        assert pairs == set()

    def test_multi_join_lacks_a_first_column(
        self, multi_variable_join_scope: Scope
    ) -> None:
        """No multiJoin(a,...) — r(a,b) and s(a,c) differ in Y."""
        with pytest.raises(AttributeError):
            multi_variable_join_scope.multiJoin.TailMap.a

    def test_multi_join_lacks_b_first_column(
        self, multi_variable_join_scope: Scope
    ) -> None:
        """No multiJoin(b,...) — r(b,c) and s(b,a) differ in Y."""
        with pytest.raises(AttributeError):
            multi_variable_join_scope.multiJoin.TailMap.b

    def test_multi_join_lacks_c_first_column(
        self, multi_variable_join_scope: Scope
    ) -> None:
        """No multiJoin(c,...) — c not in r's first column."""
        with pytest.raises(AttributeError):
            multi_variable_join_scope.multiJoin.TailMap.c


class TestMultiVariableJoinSemantics:
    """Verify multi-variable join Datalog-correct semantics.

    Value-level join correctly computes intersection: since r and s
    share no common (X,Y) tuples, the result is empty.
    """

    def test_no_common_tuples_empty_result(
        self, multi_variable_join_scope: Scope
    ) -> None:
        """r ∩ s = {} in standard Datalog, multiJoin correctly produces 0 pairs.

        r = {(a,b), (b,c)}, s = {(a,c), (b,a)}: no tuple is in both.
        Value-level join correctly returns empty set.
        """
        pairs = _collect_pairs_tailmap(multi_variable_join_scope.multiJoin)
        assert len(pairs) == 0
