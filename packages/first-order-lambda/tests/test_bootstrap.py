"""Self-hosting bootstrap: the compiler compiles its own source, and the result is a working compiler.

The compiler compiled in specialized mode is interpret-headed (COMPILE is untypable), so the
self-hosted compiler is the COMPILE node handed back to the interpreter. ``compiled_compiler()``
evaluates that interpret-headed source to the node, and ``compile_with_interpreted`` runs it as a
compiler, reifying the Scott Python-AST result through the same decoder the in-process compiler uses.
The bootstrap property is that the self-compiled compiler produces the same output as the original,
and that its output runs.
"""

from __future__ import annotations

import pytest

from first_order_lambda._compiler import (
    COMPILE,
    compile_to_source,
    compile_with_interpreted,
    compiled_compiler,
)
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
        assert compile_with_interpreted(compiler, node) == compile_to_source(node)


def test_self_compiled_output_runs() -> None:
    compiler = compiled_compiler()
    successor = lambda k: k + 1
    source = compile_with_interpreted(compiler, build(church(3)))
    assert eval(source)(successor)(0) == 3


@pytest.mark.xfail(
    reason="committed standalone self-host artifact reworked in the bootstrap stage: the committed "
    "_generated_compiler.py is the old PyExpr reconstruction (now decoded by the generic _pyast.decode) "
    "and the generic-encoding COMPILE's full reconstruction exceeds CPython's parser nesting cap, so "
    "the artifact needs a scalable (ANF) regeneration there",
    strict=False,
)
def test_interpreter_and_committed_compiler_agree_on_self() -> None:
    # The compiler run on the interpreter and the committed self-compiled compiler (the generated
    # interpret-headed Python) compile the compiler ITSELF to the same Python.
    from first_order_lambda._generated_compiler import compiled_compiler as committed_compiler

    interpreter_output = compile_to_source(build(COMPILE))
    committed_output = compile_with_interpreted(committed_compiler, build(COMPILE))
    assert committed_output == interpreter_output
