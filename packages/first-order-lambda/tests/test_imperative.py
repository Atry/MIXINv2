"""Imperative stream specialization: a cyclic source compiles to a ``while`` loop, a finite one not.

``GEN`` is an ordinary productive recursion with nothing loop-aware in it. On a cyclic source the
interpreter folds its re-entrant recursion, so the compiled generator has a ``while`` loop; on a
finite source it is a finite, loopless generator. The loop is the interpreter's fold of the rational
behaviour made imperative.
"""

from __future__ import annotations

import itertools

from first_order_lambda._dsl import app
from first_order_lambda._imperative import compile_stream
from first_order_lambda._prelude import SCOTT_CONS, SCOTT_NIL, ZERO, Y, church, cons


def _first(source: str, count: int) -> list:
    namespace: dict = {}
    exec(source, namespace)
    return list(itertools.islice(namespace["stream"](), count))


def test_cyclic_source_compiles_to_a_loop() -> None:
    source = compile_stream(app(Y, app(SCOTT_CONS, ZERO)))  # Y (cons 0)
    assert "while True" in source
    assert _first(source, 5) == [0, 0, 0, 0, 0]


def test_finite_source_compiles_without_a_loop() -> None:
    source = compile_stream(cons(church(1), cons(church(2), SCOTT_NIL)))
    assert "while True" not in source
    namespace: dict = {}
    exec(source, namespace)
    assert list(namespace["stream"]()) == [1, 2]


def test_loop_value_tracks_the_source() -> None:
    source = compile_stream(app(Y, app(SCOTT_CONS, church(7))))  # Y (cons 7)
    assert "while True" in source
    assert _first(source, 4) == [7, 7, 7, 7]
