"""The three target runtimes of the compiler: EAGER, LAZY, and FIXPOINT.

EAGER is strict (call-by-value): a Y recursion through a Church conditional diverges. LAZY and
FIXPOINT share one thunk-based target and differ only in the thunk: LAZY recomputes on each force
(call-by-name), FIXPOINT memoises with ``fixpoint_cached_property`` (call-by-need), so a re-entrant
force folds to BOTTOM, the same least-fixpoint fold the interpreter performs, rather than looping.
"""

from __future__ import annotations

import pytest

from first_order_lambda._compiler import (
    BOTTOM,
    Runtime,
    _FixpointThunk,
    _LazyThunk,
    compile_to_source,
    force,
    runtime_globals,
)
from first_order_lambda._dsl import app, build
from first_order_lambda._prelude import FACTORIAL, PLUS, church


def _eager_church(term) -> int:
    return eval(compile_to_source(build(term), Runtime.EAGER))(lambda k: k + 1)(0)


def _thunk_church(term, runtime: Runtime) -> int:
    environment = runtime_globals(runtime)
    numeral = eval(compile_to_source(build(term), runtime), environment)
    thunk, force_fn = environment["Thunk"], environment["force"]
    successor = lambda t: force_fn(t) + 1
    return numeral(thunk(lambda: successor))(thunk(lambda: 0))


def test_all_runtimes_agree_on_a_normalizing_term() -> None:
    term = app(app(PLUS, church(2)), church(3))  # Y-free, so even EAGER runs it
    assert _eager_church(term) == 5
    assert _thunk_church(term, Runtime.LAZY) == 5
    assert _thunk_church(term, Runtime.FIXPOINT) == 5


def test_thunk_runtimes_run_y_recursion() -> None:
    fact = app(FACTORIAL, church(4))
    assert _thunk_church(fact, Runtime.LAZY) == 24
    assert _thunk_church(fact, Runtime.FIXPOINT) == 24


def test_eager_runtime_diverges_on_y_recursion() -> None:
    # Strict evaluation forces the conditional's recursive branch at the base case, so Y diverges.
    source = compile_to_source(build(app(FACTORIAL, church(3))), Runtime.EAGER)
    with pytest.raises(RecursionError):
        eval(source)


def test_fixpoint_thunk_folds_a_reentrant_force() -> None:
    # A self-referential thunk: forcing it forces itself. The fixpoint thunk folds to BOTTOM; the
    # lazy thunk, which recomputes, recurses without bound.
    fixpoint = _FixpointThunk(lambda: force(fixpoint))
    assert force(fixpoint) is BOTTOM
    lazy = _LazyThunk(lambda: force(lazy))
    with pytest.raises(RecursionError):
        force(lazy)
