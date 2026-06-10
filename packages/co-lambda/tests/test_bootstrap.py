"""Self-hosting bootstrap: the compiler compiles its own source, and the result is a working compiler.

The compiler compiled in specialized mode is interpret-headed (CODEGEN is untypable), so the
self-hosted compiler is the CODEGEN node handed back to the interpreter. ``compiled_compiler()``
evaluates that interpret-headed source to the node, and ``compile_with_interpreted`` runs it as a
compiler, reifying the Scott Python-AST result through the same decoder the in-process compiler uses.
The bootstrap property is that the self-compiled compiler produces the same output as the original,
and that its output runs.
"""

from __future__ import annotations

from co_lambda._compiler import (
    codegen,
    compile_with_interpreted,
    compiled_compiler,
)
from co_lambda._dsl import app, build
from co_lambda._prelude import IDENTITY, KESTREL, MULT, PLUS, church


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
        assert compile_with_interpreted(compiler, node) == codegen(node)


def test_self_compiled_output_runs() -> None:
    compiler = compiled_compiler()
    successor = lambda k: k + 1
    source = compile_with_interpreted(compiler, build(church(3)))
    assert eval(source)(successor)(0) == 3
