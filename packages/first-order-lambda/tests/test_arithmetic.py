"""Classic lambda-calculus computations: Church numerals, Peano arithmetic, factorial, Fibonacci.

Each is a normalizing pure-lambda term; the interpreter reduces it and the graph is the tree of
the normal form, so a computed numeral renders identically to the literal Church numeral it
equals.
"""

from __future__ import annotations

import pytest

from first_order_lambda._dsl import app, build
from first_order_lambda._prelude import (
    EXP,
    FACTORIAL,
    FIBONACCI,
    IS_ZERO,
    MULT,
    PLUS,
    PRED,
    SUCC,
    TRUE,
    church,
)
from first_order_lambda._render import render


def _reads_as(term, expected) -> bool:
    return render(build(term)) == render(build(expected))


def test_church_numeral_shape() -> None:
    # church 3 = lambda s. lambda z. s (s (s z)).
    assert render(build(church(3))) == "(λ (λ (v1 (v1 (v1 v0)))))"


@pytest.mark.parametrize("n", [0, 1, 2, 5])
def test_succ(n: int) -> None:
    assert _reads_as(app(SUCC, church(n)), church(n + 1))


@pytest.mark.parametrize(
    "m, n", [(0, 0), (0, 3), (2, 3), (4, 1)]
)
def test_plus(m: int, n: int) -> None:
    assert _reads_as(app(app(PLUS, church(m)), church(n)), church(m + n))


@pytest.mark.parametrize("m, n", [(0, 4), (2, 3), (3, 3)])
def test_mult(m: int, n: int) -> None:
    assert _reads_as(app(app(MULT, church(m)), church(n)), church(m * n))


# exp m n = n m. For n = 0 it gives lambda z. z (the identity I), which is eta-equal to
# church 1 but beta-distinct, and the tree is beta, not eta; so test n >= 2.
@pytest.mark.parametrize("m, n", [(2, 2), (2, 3), (3, 2)])
def test_exp(m: int, n: int) -> None:
    assert _reads_as(app(app(EXP, church(m)), church(n)), church(m**n))


@pytest.mark.parametrize("n", [1, 2, 5])
def test_pred(n: int) -> None:
    assert _reads_as(app(PRED, church(n)), church(n - 1))


def test_is_zero() -> None:
    assert _reads_as(app(IS_ZERO, church(0)), TRUE)
    assert render(build(app(IS_ZERO, church(3)))) == render(
        build(app(IS_ZERO, church(2)))
    )  # both False


@pytest.mark.parametrize("n", [0, 1, 2, 3, 4])
def test_factorial(n: int) -> None:
    import math

    assert _reads_as(app(FACTORIAL, church(n)), church(math.factorial(n)))


@pytest.mark.parametrize("n, fib", [(0, 0), (1, 1), (2, 1), (3, 2), (4, 3), (5, 5)])
def test_fibonacci(n: int, fib: int) -> None:
    assert _reads_as(app(FIBONACCI, church(n)), church(fib))
