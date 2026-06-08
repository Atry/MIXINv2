"""The two compiled target runtimes of the compiler: call-by-value and call-by-name.

Call-by-value is strict: a Y recursion through a Church conditional diverges. Call-by-name is the
thunk-based target: an argument is a ``Thunk`` recomputed on each ``force``, matching the
interpreter's weak-head reduction, so every normalizing term computes its value (and Y recursion runs).
The interpret target is not a compiled runtime: it means interpret (re-submit the term to the
interpreter), so it has no thunk class here.
"""

from __future__ import annotations

import pytest

from first_order_lambda._compiler import (
    Runtime,
    _LazyThunk,
    compile_to_source,
    force,
    runtime_globals,
)
from first_order_lambda._dsl import app, build
from first_order_lambda._prelude import FACTORIAL, PLUS, church


def _eager_church(term) -> int:
    return eval(compile_to_source(build(term), Runtime.CALL_BY_VALUE))(lambda k: k + 1)(0)


def _thunk_church(term, runtime: Runtime) -> int:
    environment = runtime_globals(runtime)
    numeral = eval(compile_to_source(build(term), runtime), environment)
    thunk, force_fn = environment["Thunk"], environment["force"]
    successor = lambda t: force_fn(t) + 1
    return numeral(thunk(lambda: successor))(thunk(lambda: 0))


def test_compiled_runtimes_agree_on_a_normalizing_term() -> None:
    term = app(app(PLUS, church(2)), church(3))  # Y-free, so even call-by-value runs it
    assert _eager_church(term) == 5
    assert _thunk_church(term, Runtime.CALL_BY_NAME) == 5


def test_lazy_runtime_runs_y_recursion() -> None:
    fact = app(FACTORIAL, church(4))
    assert _thunk_church(fact, Runtime.CALL_BY_NAME) == 24


def test_eager_runtime_diverges_on_y_recursion() -> None:
    # Strict evaluation forces the conditional's recursive branch at the base case, so Y diverges.
    source = compile_to_source(build(app(FACTORIAL, church(3))), Runtime.CALL_BY_VALUE)
    with pytest.raises(RecursionError):
        eval(source)


def test_lazy_thunk_recomputes_on_each_force() -> None:
    # The call-by-name thunk recomputes on every force, so a self-referential force recurses unbounded.
    lazy = _LazyThunk(lambda: force(lazy))
    with pytest.raises(RecursionError):
        force(lazy)
