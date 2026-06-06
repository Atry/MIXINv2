"""A ``backend`` fixture parametrising tests over the interpreter and the compiler.

A backend observes a closed lambda term in a common domain: a Church numeral as an ``int`` and a
Church boolean as a ``bool``. The interpreter backend reads the behaviour directly (counting the
weak-head spine); the compiler backend compiles the term to Python, runs it, and applies it to a
Python successor and zero (or to ``True``/``False``). A test written against ``backend`` therefore
runs on both, cross-checking the compiler against the interpreter on the same computation.
"""

from __future__ import annotations

import pytest

from first_order_lambda._ast import make_app, make_var
from first_order_lambda._compiler import compile_to_source_lazy
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
    # The compiler backend uses the lazy (call-by-name) runtime, under which every normalizing term
    # computes its value, matching the interpreter's lazy weak-head reduction. Arguments are thunks,
    # so a Church numeral is observed by applying it to a thunked successor and zero.
    name = "compiler"

    def church(self, term: Builder) -> int:
        numeral = eval(compile_to_source_lazy(build(term)))
        successor = lambda thunk: thunk() + 1
        return numeral(lambda: successor)(lambda: 0)

    def boolean(self, term: Builder) -> bool:
        return eval(compile_to_source_lazy(build(term)))(lambda: True)(lambda: False)


@pytest.fixture(params=[_InterpreterBackend(), _CompilerBackend()], ids=["interpreter", "compiler"])
def backend(request):
    return request.param
