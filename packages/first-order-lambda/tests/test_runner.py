"""Compile once, run many: a lambda solution compiled to a reusable Python callable.

A solution written in the lambda-calculus is compiled ONCE by ``compile_solution``; the Python side
then feeds it many lambda-term inputs through ``solve``. The runtime is chosen automatically: EAGER
for a simply-typed (strongly normalizing) solution, LAZY otherwise (call-by-name converges on every
terminating application, reaching the unique fixpoint). This is the LeetCode-style use: write the
solver once, run it across a battery of test inputs.
"""

from __future__ import annotations

import math

import pytest

from first_order_lambda._compiler import Runtime, runtime_globals
from first_order_lambda._dsl import app, build, lam
from first_order_lambda._prelude import FACTORIAL, MULT, PLUS, church
from first_order_lambda._specialize import compile_solution, is_typable


def _decode_church(value: object, runtime: Runtime) -> int:
    """Observe a compiled Church numeral as an int under the runtime's calling convention."""
    if runtime is Runtime.EAGER:
        return value(lambda predecessor: predecessor + 1)(0)  # type: ignore[operator]
    globals_ = runtime_globals(runtime)
    thunk, force = globals_["Thunk"], globals_["force"]
    successor = lambda counted: force(counted) + 1
    return value(thunk(lambda: successor))(thunk(lambda: 0))  # type: ignore[operator]


def test_typable_solution_compiles_eager_and_runs_on_many_inputs() -> None:
    # square n = n * n is simply typed, so it compiles once to a strict (EAGER) Python function and
    # runs across many inputs.
    square = build(lam(lambda n: app(app(MULT, n), n)))
    assert is_typable(square) is True
    solve = compile_solution(square)  # compiled ONCE
    for n in range(7):
        assert _decode_church(solve(build(church(n))), Runtime.EAGER) == n * n


def test_recursive_solution_compiles_lazy_and_runs_on_many_inputs() -> None:
    # factorial uses Y, so it is not simply typed and compiles to the call-by-name (LAZY) runtime,
    # which converges on every terminating input. Compiled once, run across a battery of inputs.
    solve = compile_solution(build(FACTORIAL))  # compiled ONCE
    for n in range(5):
        assert _decode_church(solve(build(church(n))), Runtime.LAZY) == math.factorial(n)


def test_curried_solution_takes_several_lambda_term_inputs() -> None:
    # A multi-argument solution is fed several lambda-term inputs in turn.
    solve = compile_solution(build(PLUS))  # PLUS is typable -> EAGER
    for m, n in [(0, 0), (2, 3), (4, 1)]:
        result = solve(build(church(m)), build(church(n)))
        assert _decode_church(result, Runtime.EAGER) == m + n


@pytest.mark.parametrize(
    "node, expected_runtime",
    [
        (build(lam(lambda n: app(app(MULT, n), n))), Runtime.EAGER),  # typable
        (build(FACTORIAL), Runtime.LAZY),  # uses Y
    ],
)
def test_default_runtime_is_eager_when_typable_else_lazy(node, expected_runtime: Runtime) -> None:
    # The default never classes a reusable function FIXPOINT: the caller asserts it is a function to
    # apply, and LAZY converges on terminating applications.
    chosen = Runtime.EAGER if is_typable(node) else Runtime.LAZY
    assert chosen is expected_runtime
