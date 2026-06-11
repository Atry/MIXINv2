"""The ordinary singly-linked-list map, applied to a cyclic list.

``map`` is the textbook recursive map (``map f = Y (lambda self. lambda lst. lst (lambda h.
lambda t. cons (f h) (self t)) nil)``); nothing in it is cycle-aware. Building a cyclic list
in the pure calculus is already new: ``Y (cons 0)`` is the cyclic stream ``r = cons 0 r``,
and interning gives it a finite circular representation (a node pointing to itself) that the
standard infinite unfolding cannot. The recursion in ``map`` is guarded (a ``cons`` is exposed
before the recursive call), so over that cyclic list the recursive application re-enters the
same closed node and tabling folds the result into a finite circular structure, where head
reduction would map the infinite stream forever. On a finite list the same ``map`` behaves as
usual.
"""

from __future__ import annotations

from syrupy.assertion import SnapshotAssertion

from co_lambda._codec import church
from co_lambda._dsl import app, build
from co_lambda._examples import CYCLIC_ZEROS
from co_lambda._prelude import IDENTITY, SCOTT_CONS, SCOTT_NIL, SUCC, Y, ZERO
from co_lambda._render import render
from co_lambda._sugar import cons, map_list

# The cyclic singly-linked list r = cons 0 r, written with Y (no recursion binder).
_CYCLIC = app(Y, app(SCOTT_CONS, ZERO))


def test_map_over_cyclic_list_folds_and_terminates(snapshot: SnapshotAssertion) -> None:
    # map succ over the cyclic 0-stream folds to a finite circular structure (a back-reference
    # #0), terminating where head reduction would unfold the mapped stream forever.
    rendered = render(build(map_list(SUCC, _CYCLIC)))
    assert "#" in rendered and "⊥" not in rendered
    assert rendered == snapshot(name="map_succ_cyclic")


def test_map_identity_preserves_the_cyclic_structure() -> None:
    # map id is a no-op that still folds: the result is the source cyclic list itself.
    assert render(build(map_list(IDENTITY, _CYCLIC))) == render(CYCLIC_ZEROS)


def test_map_transforms_each_element() -> None:
    # map succ genuinely rewrites every element (0 becomes 1), so its folded result differs
    # from the source cyclic 0-stream.
    mapped = render(build(map_list(SUCC, _CYCLIC)))
    assert mapped != render(CYCLIC_ZEROS)


def test_same_map_on_a_finite_list_is_ordinary() -> None:
    # The very same map, on the finite list cons 0 nil, is the textbook map: it yields
    # cons (succ 0) nil = cons 1 nil and terminates with no fold.
    mapped = render(build(map_list(SUCC, cons(ZERO, SCOTT_NIL))))
    expected = render(build(cons(church(1), SCOTT_NIL)))
    assert "#" not in mapped
    assert mapped == expected
