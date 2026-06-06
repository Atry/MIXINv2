"""Deciding equality of rational (cyclic) terms by their behaviour.

This is the decidable core shared by rational-tree unification and equirecursive (mu-) type
equality: two cyclic structures are equal exactly when their unfoldings coincide, decided by
cycle-detecting bisimulation. Here the behaviour read off the interpreter is that unfolding, so two
constructions of the same rational term render identically, and a different one renders differently,
regardless of how each term was written.
"""

from __future__ import annotations

from first_order_lambda._dsl import app, build, lam
from first_order_lambda._prelude import SCOTT_CONS, ZERO, Y, church, cons
from first_order_lambda._render import render


def test_equal_rational_terms_are_decided_equal() -> None:
    # Two constructions of the same rational term, the constant-0 stream (a recursive type mu X. 0,X):
    #   Y (cons 0)   and   Y (lambda s. cons 0 s)
    # have the same behaviour, so they are decided equal however each was built.
    one = build(app(Y, app(SCOTT_CONS, ZERO)))
    two = build(app(Y, lam(lambda stream: cons(ZERO, stream))))
    assert render(one) == render(two)


def test_distinct_rational_terms_are_decided_unequal() -> None:
    # A different rational term (the constant-1 stream) has a different behaviour.
    zeros = build(app(Y, app(SCOTT_CONS, ZERO)))
    ones = build(app(Y, app(SCOTT_CONS, church(1))))
    assert render(zeros) != render(ones)
