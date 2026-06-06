"""Church-numeral arithmetic, run on both the interpreter and the compiler.

Each case observes a Church numeral as an int (or a Church boolean as a bool) through the
``backend`` fixture, so the same computation is checked on the interpreter and on the compiled
Python. The Y-free operations (successor, addition, multiplication, exponentiation, predecessor,
zero test) are strict-safe and run on both; factorial and Fibonacci use Y and a Church conditional
whose eager branches diverge in a strict host, so they run on the interpreter only.
"""

from __future__ import annotations

import math

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
    church,
)
from first_order_lambda._pyast import _church_to_int


@pytest.mark.parametrize("n", [0, 1, 3])
def test_church_numeral(backend, n: int) -> None:
    assert backend.church(church(n)) == n


@pytest.mark.parametrize("n", [0, 1, 2, 5])
def test_succ(backend, n: int) -> None:
    assert backend.church(app(SUCC, church(n))) == n + 1


@pytest.mark.parametrize("m, n", [(0, 0), (0, 3), (2, 3), (4, 1)])
def test_plus(backend, m: int, n: int) -> None:
    assert backend.church(app(app(PLUS, church(m)), church(n))) == m + n


@pytest.mark.parametrize("m, n", [(0, 4), (2, 3), (3, 3)])
def test_mult(backend, m: int, n: int) -> None:
    assert backend.church(app(app(MULT, church(m)), church(n))) == m * n


# exp m n = n m. For n = 0 it gives the identity, eta-equal to church 1 but beta-distinct; test n >= 2.
@pytest.mark.parametrize("m, n", [(2, 2), (2, 3), (3, 2)])
def test_exp(backend, m: int, n: int) -> None:
    assert backend.church(app(app(EXP, church(m)), church(n))) == m**n


@pytest.mark.parametrize("n", [1, 2, 5])
def test_pred(backend, n: int) -> None:
    assert backend.church(app(PRED, church(n))) == n - 1


def test_is_zero(backend) -> None:
    assert backend.boolean(app(IS_ZERO, church(0))) is True
    assert backend.boolean(app(IS_ZERO, church(3))) is False


# Factorial and Fibonacci use Y and a Church conditional; in a strict host the eager else branch
# diverges, so they are observed on the interpreter only.
@pytest.mark.parametrize("n", [0, 1, 2, 3, 4])
def test_factorial(n: int) -> None:
    assert _church_to_int(build(app(FACTORIAL, church(n)))) == math.factorial(n)


@pytest.mark.parametrize("n, fib", [(0, 0), (1, 1), (2, 1), (3, 2), (4, 3), (5, 5)])
def test_fibonacci(n: int, fib: int) -> None:
    assert _church_to_int(build(app(FIBONACCI, church(n)))) == fib
