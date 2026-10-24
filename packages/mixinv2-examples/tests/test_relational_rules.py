"""Tests for different Datalog rule patterns in relational algebra examples.

Each example uses a different Datalog rule structure, testing the
MIXINv2 trie-based evaluation beyond simple transitive closure:

- RelationalSymmetricClosure: column swap (sym(X,Y) :- edge(Y,X))
- RelationalComposition: two-relation join (composed(X,Z) :- alpha(X,Y), beta(Y,Z))
- RelationalSymmetricTransitiveClosure: chained rules (sym → reach)

RelationalSymmetricClosure and RelationalComposition use the RepeatedVisitor
encoding which produces Datalog-correct results (value-level joins).

All three use the RepeatedVisitor encoding with Datalog-correct results.
"""

import pytest

from mixinv2._runtime import Scope, evaluate

import mixinv2_examples
import mixinv2_library


# =============================================================================
# Fixtures
# =============================================================================


@pytest.fixture
def symmetric_closure_scope() -> Scope:
    """Load RelationalSymmetricClosure: edge(a,b), edge(b,c)."""
    root = evaluate(mixinv2_library, mixinv2_examples, modules_public=True)
    result = root.RelationalSymmetricClosure
    assert isinstance(result, Scope)
    return result


@pytest.fixture
def composition_scope() -> Scope:
    """Load RelationalComposition: alpha(a,b), alpha(c,b), beta(b,a), beta(b,c)."""
    root = evaluate(mixinv2_library, mixinv2_examples, modules_public=True)
    result = root.RelationalComposition
    assert isinstance(result, Scope)
    return result


@pytest.fixture
def symmetric_transitive_closure_scope() -> Scope:
    """Load RelationalSymmetricTransitiveClosure: edge(a,b), edge(b,c)."""
    root = evaluate(mixinv2_library, mixinv2_examples, modules_public=True)
    result = root.RelationalSymmetricTransitiveClosure
    assert isinstance(result, Scope)
    return result


# =============================================================================
# Helpers
# =============================================================================


def _collect_pairs_tailmap(relation: Scope) -> set[tuple[str, str]]:
    """Enumerate all (first, second) pairs in a __TailMap-encoded relation."""
    pairs: set[tuple[str, str]] = set()
    for first in ("a", "b", "c"):
        for second in ("a", "b", "c"):
            try:
                tail1 = getattr(relation["__TailMap"], first)
                getattr(tail1["__TailMap"], second)
                pairs.add((first, second))
            except (AttributeError, KeyError):
                pass
    return pairs



# =============================================================================
# Symmetric Closure: sym(X,Y) :- edge(X,Y). sym(X,Y) :- edge(Y,X).
#
# edge = {(a,b), (b,c)}
#
# Datalog-correct result:
#   direct: {(a,b), (b,c)}
#   swap:   {(b,a), (c,b)}
#   union:  {(a,b), (b,a), (b,c), (c,b)}
# =============================================================================


class TestSymmetricClosureEdge:
    """Verify edge facts for symmetric closure example."""

    def test_edge_a_b(self, symmetric_closure_scope: Scope) -> None:
        assert isinstance(symmetric_closure_scope.edge["__TailMap"].a["__TailMap"].b, Scope)

    def test_edge_b_c(self, symmetric_closure_scope: Scope) -> None:
        assert isinstance(symmetric_closure_scope.edge["__TailMap"].b["__TailMap"].c, Scope)

    def test_edge_has_only_a_and_b_first_columns(
        self, symmetric_closure_scope: Scope
    ) -> None:
        with pytest.raises((AttributeError, KeyError)):
            symmetric_closure_scope.edge["__TailMap"].c


class TestSymmetricClosureSym:
    """Verify sym = direct ∪ swap of edge (Datalog-correct).

    sym = {(a,b), (b,a), (b,c), (c,b)}
    """

    def test_sym_complete_set(self, symmetric_closure_scope: Scope) -> None:
        """sym contains exactly 4 pairs (Datalog-correct)."""
        pairs = _collect_pairs_tailmap(symmetric_closure_scope.sym)
        expected = {
            ("a", "b"),
            ("b", "a"),
            ("b", "c"),
            ("c", "b"),
        }
        assert pairs == expected

    def test_sym_lacks_a_a(self, symmetric_closure_scope: Scope) -> None:
        """(a,a) absent — no derivation produces it."""
        with pytest.raises((AttributeError, KeyError)):
            symmetric_closure_scope.sym["__TailMap"].a["__TailMap"].a

    def test_sym_lacks_c_c(self, symmetric_closure_scope: Scope) -> None:
        """(c,c) absent — no derivation produces it."""
        with pytest.raises((AttributeError, KeyError)):
            symmetric_closure_scope.sym["__TailMap"].c["__TailMap"].c

    def test_sym_has_reverse_a_b(self, symmetric_closure_scope: Scope) -> None:
        """(b,a) present from the swap rule."""
        assert isinstance(symmetric_closure_scope.sym["__TailMap"].b["__TailMap"].a, Scope)

    def test_sym_has_reverse_b_c(self, symmetric_closure_scope: Scope) -> None:
        """(c,b) present from the swap rule."""
        assert isinstance(symmetric_closure_scope.sym["__TailMap"].c["__TailMap"].b, Scope)

    def test_sym_lacks_a_c(self, symmetric_closure_scope: Scope) -> None:
        """(a,c) absent — not derivable in Datalog."""
        with pytest.raises((AttributeError, KeyError)):
            symmetric_closure_scope.sym["__TailMap"].a["__TailMap"].c

    def test_sym_lacks_b_b(self, symmetric_closure_scope: Scope) -> None:
        """(b,b) absent — not derivable in Datalog."""
        with pytest.raises((AttributeError, KeyError)):
            symmetric_closure_scope.sym["__TailMap"].b["__TailMap"].b


class TestSymmetricClosureDirectResult:
    """Verify the direct rule's result independently."""

    def test_direct_result(self, symmetric_closure_scope: Scope) -> None:
        """Direct rule: sym(X,Y) :- edge(X,Y) = {(a,b), (b,c)}."""
        direct_result = symmetric_closure_scope["__DirectXAcceptance"]["__Accepted"]
        pairs = _collect_pairs_tailmap(direct_result)
        expected = {("a", "b"), ("b", "c")}
        assert pairs == expected


class TestSymmetricClosureSwapResult:
    """Verify the swap rule's result independently."""

    def test_swap_result(self, symmetric_closure_scope: Scope) -> None:
        """Swap rule: sym(X,Y) :- edge(Y,X) = {(b,a), (c,b)}."""
        swap_result = symmetric_closure_scope["__SwapYAcceptance"]["__Accepted"]
        pairs = _collect_pairs_tailmap(swap_result)
        expected = {("b", "a"), ("c", "b")}
        assert pairs == expected


# =============================================================================
# Composition: composed(X,Z) :- alpha(X,Y), beta(Y,Z).
#
# alpha = {(a,b), (c,b)}, beta = {(b,a), (b,c)}
#
# Datalog-correct result:
#   Y=b: alpha(a,b) + beta(b,a) → composed(a,a)
#        alpha(a,b) + beta(b,c) → composed(a,c)
#        alpha(c,b) + beta(b,a) → composed(c,a)
#        alpha(c,b) + beta(b,c) → composed(c,c)
#   Result: {(a,a), (a,c), (c,a), (c,c)}
# =============================================================================


class TestCompositionAlpha:
    """Verify alpha relation facts."""

    def test_alpha_a_b(self, composition_scope: Scope) -> None:
        assert isinstance(composition_scope.alpha["__TailMap"].a["__TailMap"].b, Scope)

    def test_alpha_c_b(self, composition_scope: Scope) -> None:
        assert isinstance(composition_scope.alpha["__TailMap"].c["__TailMap"].b, Scope)


class TestCompositionBeta:
    """Verify beta relation facts."""

    def test_beta_b_a(self, composition_scope: Scope) -> None:
        assert isinstance(composition_scope.beta["__TailMap"].b["__TailMap"].a, Scope)

    def test_beta_b_c(self, composition_scope: Scope) -> None:
        assert isinstance(composition_scope.beta["__TailMap"].b["__TailMap"].c, Scope)


class TestCompositionResult:
    """Verify composed = Datalog-correct {(a,a), (a,c), (c,a), (c,c)}.

    All alpha entries share Y=b and all beta entries share Y=b,
    so the value-level join matches correctly.
    """

    def test_composed_complete_set(self, composition_scope: Scope) -> None:
        pairs = _collect_pairs_tailmap(composition_scope.composed)
        expected = {("a", "a"), ("a", "c"), ("c", "a"), ("c", "c")}
        assert pairs == expected

    def test_composed_a_a(self, composition_scope: Scope) -> None:
        """alpha(a,b) + beta(b,a) → composed(a,a)."""
        assert isinstance(composition_scope.composed["__TailMap"].a["__TailMap"].a, Scope)

    def test_composed_a_c(self, composition_scope: Scope) -> None:
        """alpha(a,b) + beta(b,c) → composed(a,c)."""
        assert isinstance(composition_scope.composed["__TailMap"].a["__TailMap"].c, Scope)

    def test_composed_c_a(self, composition_scope: Scope) -> None:
        """alpha(c,b) + beta(b,a) → composed(c,a)."""
        assert isinstance(composition_scope.composed["__TailMap"].c["__TailMap"].a, Scope)

    def test_composed_c_c(self, composition_scope: Scope) -> None:
        """alpha(c,b) + beta(b,c) → composed(c,c)."""
        assert isinstance(composition_scope.composed["__TailMap"].c["__TailMap"].c, Scope)

    def test_composed_lacks_b_tuples(self, composition_scope: Scope) -> None:
        """No composed(b,...) — b is not a first-column entity in alpha.

        __TailMap.b exists structurally (from __Cons definition) but has no
        nested __TailMap entries (no output tuples with b as first column).
        """
        with pytest.raises((AttributeError, KeyError)):
            composition_scope.composed["__TailMap"].b["__TailMap"]


# =============================================================================
# Symmetric Transitive Closure: sym → reach (chained rules)
#
# edge = {(a,b), (b,c)}
# sym (Datalog-correct) = {(a,b), (b,a), (b,c), (c,b)}  (4 pairs)
# reach = all 9 pairs (recursive rule fills remaining pairs)
# =============================================================================


class TestSymmetricTransitiveClosureSym:
    """Verify intermediate sym relation (Datalog-correct, same as RelationalSymmetricClosure).

    sym = {(a,b), (b,a), (b,c), (c,b)}
    """

    def test_sym_has_4_pairs(
        self, symmetric_transitive_closure_scope: Scope
    ) -> None:
        pairs = _collect_pairs_tailmap(symmetric_transitive_closure_scope.sym)
        expected = {
            ("a", "b"),
            ("b", "a"),
            ("b", "c"),
            ("c", "b"),
        }
        assert pairs == expected

    def test_sym_lacks_a_a(
        self, symmetric_transitive_closure_scope: Scope
    ) -> None:
        """(a,a) absent from sym — no derivation produces it."""
        with pytest.raises((AttributeError, KeyError)):
            symmetric_transitive_closure_scope.sym["__TailMap"].a["__TailMap"].a

    def test_sym_lacks_c_c(
        self, symmetric_transitive_closure_scope: Scope
    ) -> None:
        """(c,c) absent from sym — no derivation produces it."""
        with pytest.raises((AttributeError, KeyError)):
            symmetric_transitive_closure_scope.sym["__TailMap"].c["__TailMap"].c


class TestSymmetricTransitiveClosureReach:
    """Verify reach = complete graph on {a,b,c}.

    The recursive rule reach(X,Y) :- sym(X,Z), reach(Z,Y) fills in
    all remaining pairs beyond sym, yielding all 9 pairs.
    """

    def test_reach_complete_graph(
        self, symmetric_transitive_closure_scope: Scope
    ) -> None:
        """All 9 pairs present."""
        pairs = _collect_pairs_tailmap(symmetric_transitive_closure_scope.reach)
        expected = {
            (first, second) for first in ("a", "b", "c") for second in ("a", "b", "c")
        }
        assert pairs == expected

    def test_reach_has_a_a(
        self, symmetric_transitive_closure_scope: Scope
    ) -> None:
        """(a,a) present in reach but absent from sym."""
        assert isinstance(
            symmetric_transitive_closure_scope.reach["__TailMap"].a["__TailMap"].a, Scope
        )

    def test_reach_has_c_c(
        self, symmetric_transitive_closure_scope: Scope
    ) -> None:
        """(c,c) present in reach but absent from sym."""
        assert isinstance(
            symmetric_transitive_closure_scope.reach["__TailMap"].c["__TailMap"].c, Scope
        )

    def test_sym_lacks_a_a(
        self, symmetric_transitive_closure_scope: Scope
    ) -> None:
        """(a,a) absent from sym — only reach fills this gap."""
        with pytest.raises((AttributeError, KeyError)):
            symmetric_transitive_closure_scope.sym["__TailMap"].a["__TailMap"].a

    def test_sym_lacks_c_c(
        self, symmetric_transitive_closure_scope: Scope
    ) -> None:
        """(c,c) absent from sym — only reach fills this gap."""
        with pytest.raises((AttributeError, KeyError)):
            symmetric_transitive_closure_scope.sym["__TailMap"].c["__TailMap"].c


class TestChainedRuleDependency:
    """Verify that reach properly depends on sym as intermediate predicate."""

    def test_reach_superset_of_sym(
        self, symmetric_transitive_closure_scope: Scope
    ) -> None:
        """Every pair in sym is also in reach."""
        sym_pairs = _collect_pairs_tailmap(symmetric_transitive_closure_scope.sym)
        reach_pairs = _collect_pairs_tailmap(symmetric_transitive_closure_scope.reach)
        assert sym_pairs.issubset(reach_pairs)

    def test_reach_adds_pairs_beyond_sym(
        self, symmetric_transitive_closure_scope: Scope
    ) -> None:
        """reach has 5 pairs not in sym (recursive rule fills them in).

        sym = {(a,b), (b,a), (b,c), (c,b)} — 4 pairs
        reach = all 9 pairs
        extra = {(a,a), (a,c), (b,b), (c,a), (c,c)} — 5 pairs
        """
        sym_pairs = _collect_pairs_tailmap(symmetric_transitive_closure_scope.sym)
        reach_pairs = _collect_pairs_tailmap(symmetric_transitive_closure_scope.reach)
        extra = reach_pairs - sym_pairs
        assert extra == {("a", "a"), ("a", "c"), ("b", "b"), ("c", "a"), ("c", "c")}
