"""The showcase: memoized properties on data cells (the inheritance-calculus style move).

A recursive query over cyclic data is a least-fixpoint property keyed on the data cell's
node identity. For a genuinely shared cyclic stream (built with a back-edge), the cell set
is finite, so the property converges and terminates; Omega has no data cell, so this never
revives it (conservative). ``reach`` is the paper's reachability in this intrusive form
(the property lives on the cell). ``decorate_succ`` builds a new cyclic structure
isomorphic to the input, each new cell carrying a new property, by registering the image in
a memo before recursing (the knot-tying that must be lazy, not eager). ``build_cyclic``
shows extensibility by reconstruction: the constructor is a polymorphic parameter, so a new
query rebuilds the graph with its own cell type.
"""

from __future__ import annotations

from abc import ABC
from dataclasses import dataclass
from typing import Callable, cast, final

from fixpoints._core import fixpoint_cached_property


@dataclass(kw_only=True, eq=False)
class Stream(ABC):
    """A stream cell. Identity object; ``tail`` is mutable so cycles can be tied.

    Not slotted, so instances carry a ``__dict__`` for the ``fixpoint_cached_property``
    caches (``reachable_cells``, ``elements``).
    """

    @fixpoint_cached_property(bottom=lambda: frozenset())
    def reachable_cells(self) -> frozenset["Stream"]:
        """Least-fixpoint set of cells reachable from this one (terminates on cycles)."""
        match self:
            case Nil():
                return frozenset({self})
            case Cons(tail=tail) | DecoratedCons(tail=tail):
                return frozenset({self}) | cast(
                    "frozenset[Stream]", tail.reachable_cells
                )
            case _:
                raise TypeError(f"Unknown stream cell {self!r}")

    @fixpoint_cached_property(bottom=lambda: frozenset())
    def elements(self) -> frozenset[int]:
        """Least-fixpoint set of head values along the stream (terminates on cycles)."""
        match self:
            case Nil():
                return frozenset()
            case Cons(head=head, tail=tail) | DecoratedCons(head=head, tail=tail):
                return frozenset({head}) | cast("frozenset[int]", tail.elements)
            case _:
                raise TypeError(f"Unknown stream cell {self!r}")

    def reaches(self, target: "Stream") -> bool:
        """Whether ``target`` is reachable from this cell (reads out as present/absent)."""
        return target in cast("frozenset[Stream]", self.reachable_cells)


@final
@dataclass(kw_only=True, eq=False)
class Nil(Stream):
    pass


@final
@dataclass(kw_only=True, eq=False)
class Cons(Stream):
    head: int
    tail: Stream


@final
@dataclass(kw_only=True, eq=False)
class DecoratedCons(Stream):
    head: int
    tail: Stream
    label: str
    """A new property attached to each node of the reconstructed cycle."""


def decorate_succ(stream: Stream, *, label: str) -> Stream:
    """Map a stream to a new isomorphic structure with ``head + 1`` and a ``label``.

    Knot-tying: the image is registered in the memo BEFORE recursing into the tail, so a
    back-edge to an already-seen cell reuses its image (a finite cyclic result). Doing it
    eagerly (recurse first, register after) would loop.
    """
    return _decorate_succ(stream, label, {})


def _decorate_succ(stream: Stream, label: str, memo: dict[int, Stream]) -> Stream:
    stream_id = id(stream)
    existing = memo.get(stream_id)
    if existing is not None:
        return existing
    match stream:
        case Nil():
            image: Stream = Nil()
            memo[stream_id] = image
            return image
        case Cons(head=head, tail=tail) | DecoratedCons(head=head, tail=tail):
            decorated = DecoratedCons(head=head + 1, tail=Nil(), label=label)
            memo[stream_id] = decorated
            decorated.tail = _decorate_succ(tail, label, memo)
            return decorated
        case _:
            raise TypeError(f"Unknown stream cell {stream!r}")


def build_cyclic(value: int, *, make_cell: Callable[[int, Stream], Stream]) -> Stream:
    """Build a one-cell cyclic stream ``r = make_cell(value, r)`` (the abstract factory).

    ``make_cell`` is the polymorphic parameter; a new query reconstructs the graph with its
    own cell type.
    """
    cell = make_cell(value, Nil())
    assert isinstance(cell, (Cons, DecoratedCons)), "make_cell must build a cell with a tail"
    cell.tail = cell
    return cell


def plain_cons(head: int, tail: Stream) -> Stream:
    return Cons(head=head, tail=tail)


def labelled_cons(label: str) -> Callable[[int, Stream], Stream]:
    return lambda head, tail: DecoratedCons(head=head, tail=tail, label=label)
