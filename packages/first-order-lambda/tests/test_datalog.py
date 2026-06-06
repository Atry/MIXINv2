"""Pure Datalog encoded into the pure lambda-calculus and read off by the interpreter.

A ground Datalog program (no function symbols, hence a finite Herbrand base) is compiled to its
immediate-consequence operator ``T_P`` over a Church tuple of booleans; the least Herbrand model is
``T_P`` iterated ``|HB|`` times from the all-false tuple (a bounded, total computation, no ``Y``).
A goal atom is a projection, which normalizes to the Church boolean TRUE or FALSE, so ``render`` of
the goal equals ``render`` of TRUE/FALSE exactly when the atom is/ is not in the least model.
"""

from __future__ import annotations

from first_order_lambda._dsl import build
from first_order_lambda._prelude import (
    DATALOG_CONJ_R,
    DATALOG_CONJ_T,
    DATALOG_REACH_C,
    DATALOG_REACH_D,
    FALSE,
    TRUE,
)
from first_order_lambda._render import render

_TRUE = render(build(TRUE))
_FALSE = render(build(FALSE))


def test_church_booleans_render_distinctly() -> None:
    assert _TRUE != _FALSE


def test_conjunction_and_disjunction() -> None:
    # t(a) holds: t(X):-q(X), q(X):-p(X), p(a). (the OR of t's two clauses, via the q branch).
    assert render(DATALOG_CONJ_T) == _TRUE
    # r(a) fails: r(X):-p(X),s(X) and s(a) has no fact, so the AND has a false conjunct.
    assert render(DATALOG_CONJ_R) == _FALSE


def test_recursive_reachability() -> None:
    # reach(c) via reach(b) via reach(a): the least fixpoint of a recursive rule.
    assert render(DATALOG_REACH_C) == _TRUE
    # reach(d): no edge into d, so it is not derivable.
    assert render(DATALOG_REACH_D) == _FALSE
