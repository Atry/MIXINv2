"""A ``backend`` fixture parametrising tests over the interpreter and the compiler runtimes.

A backend observes a closed lambda term in a common domain: a Church numeral as an ``int`` and a
Church boolean as a ``bool``. The interpreter backend reads the behaviour directly (counting the
weak-head spine). The compiler backend compiles the term to Python for the call-by-name thunk-based
runtime and runs it, applying the Church numeral to a thunked successor and zero (or to
``True``/``False``). Call-by-name computes every normalizing term, matching the interpreter; the
strict call-by-value runtime, which diverges on Y recursion, is exercised in ``test_runtimes``
instead. The interpret target is the interpreter itself, so it is covered by the interpreter backend.
"""

from __future__ import annotations

import pytest

from first_order_lambda._ast import make_app, make_var
from first_order_lambda._compiler import Runtime, compile_to_source, runtime_globals
from first_order_lambda._dsl import Builder, build
from first_order_lambda._pyast import _church_to_int
from first_order_lambda._shape import VarShape

_TRUE_MARKER = 7_000_001
_FALSE_MARKER = 7_000_002


def _interpret_boolean(node) -> bool:
    applied = make_app(make_app(node, make_var(_TRUE_MARKER)), make_var(_FALSE_MARKER))
    shape = applied.weak_head_normal_form
    match shape:
        case VarShape(index=index) if index == _TRUE_MARKER:
            return True
        case VarShape(index=index) if index == _FALSE_MARKER:
            return False
        case _:
            raise ValueError(f"not a Church boolean: {shape!r}")


class _InterpreterBackend:
    name = "interpreter"

    def church(self, term: Builder) -> int:
        return _church_to_int(build(term))

    def boolean(self, term: Builder) -> bool:
        return _interpret_boolean(build(term))


class _CompilerBackend:
    def __init__(self, runtime: Runtime) -> None:
        self.runtime = runtime
        self.name = f"compiler-{runtime.name.lower()}"

    def _evaluate(self, term: Builder):
        environment = runtime_globals(self.runtime)
        return eval(compile_to_source(build(term), self.runtime), environment), environment

    def church(self, term: Builder) -> int:
        numeral, environment = self._evaluate(term)
        thunk, force = environment["Thunk"], environment["force"]
        successor = lambda t: force(t) + 1
        return numeral(thunk(lambda: successor))(thunk(lambda: 0))

    def boolean(self, term: Builder) -> bool:
        result, environment = self._evaluate(term)
        thunk = environment["Thunk"]
        return result(thunk(lambda: True))(thunk(lambda: False))


@pytest.fixture(
    params=[_InterpreterBackend(), _CompilerBackend(Runtime.CALL_BY_NAME)],
    ids=["interpreter", "compiler-lazy"],
)
def backend(request):
    return request.param
