"""Self-hosting bootstrap: the compiler compiles its own source, and the result is a working compiler.

``compiled_compiler()`` is COMPILE compiled to Python (by COMPILE itself) and evaluated as a Python
function. ``compile_with`` runs that self-compiled compiler on a host-encoded source term. The
bootstrap property is that the self-compiled compiler produces the same output as the original
compiler, and that its output runs.
"""

from __future__ import annotations

from first_order_lambda._compiler import compile_to_source, compile_with, compiled_compiler
from first_order_lambda._dsl import app, build
from first_order_lambda._prelude import IDENTITY, KESTREL, MULT, PLUS, church


def test_self_compiled_compiler_matches_the_original() -> None:
    compiler = compiled_compiler()
    terms = [
        IDENTITY,
        KESTREL,
        church(0),
        church(3),
        app(app(PLUS, church(1)), church(2)),
        app(app(MULT, church(2)), church(2)),
    ]
    for term in terms:
        node = build(term)
        assert compile_with(compiler, node) == compile_to_source(node)


def test_self_compiled_output_runs() -> None:
    compiler = compiled_compiler()
    successor = lambda k: k + 1
    source = compile_with(compiler, build(church(3)))
    assert eval(source)(successor)(0) == 3
