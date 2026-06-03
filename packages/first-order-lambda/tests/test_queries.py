"""The showcase: memoized properties on data cells terminate over cyclic data."""

from __future__ import annotations

from first_order_lambda._queries import (
    Cons,
    DecoratedCons,
    Nil,
    build_cyclic,
    decorate_succ,
    labelled_cons,
    plain_cons,
)


def test_reach_over_cyclic_terminates() -> None:
    cyclic = build_cyclic(0, make_cell=plain_cons)
    # r reaches itself; the reachable-cell set is finite (one cell).
    assert cyclic.reaches(cyclic)
    assert cyclic.reachable_cells == frozenset({cyclic})


def test_elements_over_cyclic_terminates() -> None:
    cyclic = build_cyclic(0, make_cell=plain_cons)
    assert cyclic.elements == frozenset({0})


def test_reaches_unreachable_is_false() -> None:
    cyclic = build_cyclic(0, make_cell=plain_cons)
    assert not cyclic.reaches(Nil())


def test_finite_list_queries() -> None:
    terminal = Nil()
    cell = Cons(head=0, tail=Cons(head=1, tail=terminal))
    assert cell.elements == frozenset({0, 1})
    assert cell.reaches(terminal)


def test_decorate_succ_ties_the_knot() -> None:
    cyclic = build_cyclic(0, make_cell=plain_cons)
    decorated = decorate_succ(cyclic, label="tag")
    assert isinstance(decorated, DecoratedCons)
    assert decorated.head == 1
    assert decorated.label == "tag"
    # The new structure is itself a finite cycle isomorphic to the input.
    assert decorated.tail is decorated
    assert decorated.elements == frozenset({1})


def test_extensibility_by_reconstruction() -> None:
    # Same one-cell-cycle template, two algebras (the polymorphic parameter).
    plain = build_cyclic(0, make_cell=plain_cons)
    labelled = build_cyclic(0, make_cell=labelled_cons("tag"))
    assert plain.elements == frozenset({0})
    assert labelled.elements == frozenset({0})
    assert isinstance(labelled, DecoratedCons)
    assert labelled.label == "tag"
