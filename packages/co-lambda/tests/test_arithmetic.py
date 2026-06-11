"""Church-numeral arithmetic, run on both the interpreter and the compiler.

Each case observes a Church numeral as an int (or a Church boolean as a bool) through the
``backend`` fixture, so the same computation is checked on the interpreter and on the compiled
Python. The compiler backend uses the lazy (call-by-name) runtime, the faithful lambda semantics
matching the interpreter's weak-head reduction, so every normalizing term computes its value,
factorial and Fibonacci (Y recursion through a Church conditional) included.
"""

from __future__ import annotations

import math

import pytest

from co_lambda._codec import church
from co_lambda._dsl import app
from co_lambda._prelude import EXP, FACTORIAL, FIBONACCI, IS_ZERO, MULT, PLUS, PRED, SUCC


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


@pytest.mark.parametrize("n", [0, 1, 2, 3, 4])
def test_factorial(backend, n: int) -> None:
    assert backend.church(app(FACTORIAL, church(n))) == math.factorial(n)


@pytest.mark.parametrize("n, fib", [(0, 0), (1, 1), (2, 1), (3, 2), (4, 3), (5, 5)])
def test_fibonacci(backend, n: int, fib: int) -> None:
    assert backend.church(app(FIBONACCI, church(n))) == fib
