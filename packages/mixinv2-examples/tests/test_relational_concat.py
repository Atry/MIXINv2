"""Tests for concat(X,Y,W,Z) :- edge(X,Y), edge(W,Z).

edge = {(a,b), (b,c)} — no shared variable, pure Cartesian product.

Standard Datalog result (4 tuples):
  {(a,b,a,b), (a,b,b,c), (b,c,a,b), (b,c,b,c)}

Per-constant construction preserves column correlations and matches
Datalog semantics exactly.

Uses the RepeatedVisitor encoding with TailMap navigation.
"""

import pytest

from mixinv2._runtime import Scope, evaluate

import mixinv2_examples
import mixinv2_library


@pytest.fixture
def concat_scope() -> Scope:
    """Load RelationalConcat: edge(a,b), edge(b,c)."""
    root = evaluate(mixinv2_library, mixinv2_examples, modules_public=True)
    result = root.RelationalConcat
    assert isinstance(result, Scope)
    return result


CONSTANTS = ("a", "b", "c")


def _collect_quads(
    relation: Scope,
) -> set[tuple[str, str, str, str]]:
    """Enumerate all (X,Y,W,Z) 4-tuples present in a 4-column TailMap relation trie."""
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


class TestConcatEdgeFacts:
    """Verify base edge facts are present."""

    def test_edge_a_b(self, concat_scope: Scope) -> None:
        assert isinstance(concat_scope.edge.TailMap.a.TailMap.b, Scope)

    def test_edge_b_c(self, concat_scope: Scope) -> None:
        assert isinstance(concat_scope.edge.TailMap.b.TailMap.c, Scope)

    def test_edge_lacks_a_c(self, concat_scope: Scope) -> None:
        with pytest.raises(AttributeError):
            concat_scope.edge.TailMap.a.TailMap.c


class TestConcatResult:
    """Verify concat matches Datalog semantics exactly.

    Per-constant construction preserves X-Y and W-Z correlations:
    X=a always pairs with Y=b, X=b always pairs with Y=c.
    """

    def test_concat_exactly_4_tuples(self, concat_scope: Scope) -> None:
        """Exactly the 4 Datalog-correct tuples, no spurious ones."""
        quads = _collect_quads(concat_scope.concat)
        datalog_expected = {
            ("a", "b", "a", "b"),
            ("a", "b", "b", "c"),
            ("b", "c", "a", "b"),
            ("b", "c", "b", "c"),
        }
        assert quads == datalog_expected

    def test_concat_a_b_a_b(self, concat_scope: Scope) -> None:
        """edge(a,b) x edge(a,b)."""
        assert isinstance(
            concat_scope.concat.TailMap.a.TailMap.b.TailMap.a.TailMap.b, Scope
        )

    def test_concat_a_b_b_c(self, concat_scope: Scope) -> None:
        """edge(a,b) x edge(b,c)."""
        assert isinstance(
            concat_scope.concat.TailMap.a.TailMap.b.TailMap.b.TailMap.c, Scope
        )

    def test_concat_b_c_a_b(self, concat_scope: Scope) -> None:
        """edge(b,c) x edge(a,b)."""
        assert isinstance(
            concat_scope.concat.TailMap.b.TailMap.c.TailMap.a.TailMap.b, Scope
        )

    def test_concat_b_c_b_c(self, concat_scope: Scope) -> None:
        """edge(b,c) x edge(b,c)."""
        assert isinstance(
            concat_scope.concat.TailMap.b.TailMap.c.TailMap.b.TailMap.c, Scope
        )

    def test_concat_lacks_a_c(self, concat_scope: Scope) -> None:
        """(a,c,...) absent — a's Tail is only b, never c."""
        with pytest.raises(AttributeError):
            concat_scope.concat.TailMap.a.TailMap.c
