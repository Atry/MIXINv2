"""The call-by-need target: explicit memoising thunks, emitted entirely by the COMPILE_NEED lambda term.

Every sub-term compiles to a sentinel-guarded memoising thunk (compute once, cache, return the cache),
a lambda to an inner ``def``, and a variable to a forced thunk looked up by de Bruijn index. The whole
module structure and every identifier (the AST path, as ``v_<seg>_<seg>...``) are built by the lambda
term; Python only decodes the Scott AST 1:1. These tests pin the emitted shape and check it runs.
"""

from __future__ import annotations

import pytest
from syrupy.assertion import SnapshotAssertion

from first_order_lambda._compiler import Runtime, call_by_need_globals, compile_to_source
from first_order_lambda._dsl import app, build
from first_order_lambda._prelude import (
    FACTORIAL,
    FIBONACCI,
    IDENTITY,
    KESTREL,
    MULT,
    PLUS,
    church,
)


def _run_church(term) -> int:
    """Compile to call-by-need, then observe the result Church numeral as an int.

    A value is a thunk (a nullary callable) whose forcing (calling it) yields a function of one thunk,
    matching the emitted protocol. The successor takes a thunk and returns a thunk computing +1.
    """
    source = compile_to_source(build(term), Runtime.CALL_BY_NEED)
    environment = call_by_need_globals()
    exec(source, environment)
    successor = lambda argument_thunk: (lambda: argument_thunk() + 1)
    return environment["program"]()(lambda: successor)()(lambda: 0)()


def test_call_by_need_emits_explicit_memoising_thunks(snapshot: SnapshotAssertion) -> None:
    emitted = {
        "identity": compile_to_source(build(IDENTITY), Runtime.CALL_BY_NEED),
        "constant_k": compile_to_source(build(KESTREL), Runtime.CALL_BY_NEED),
    }
    assert emitted == snapshot(name="call_by_need_source")


@pytest.mark.parametrize("n", [0, 1, 2, 3, 4, 5])
def test_call_by_need_computes_church_numerals(n: int) -> None:
    assert _run_church(church(n)) == n


def test_call_by_need_computes_arithmetic_and_recursion() -> None:
    # Y recursion runs under call-by-need (it terminates on normalizing terms), like call-by-name.
    assert _run_church(app(app(PLUS, church(2)), church(3))) == 5
    assert _run_church(app(app(MULT, church(3)), church(4))) == 12
    assert _run_church(app(FACTORIAL, church(4))) == 24
    assert _run_church(app(FIBONACCI, church(6))) == 8
