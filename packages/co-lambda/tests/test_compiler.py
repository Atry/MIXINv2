"""A lambda-to-Python compiler written in the lambda-calculus, checked semantically.

``codegen`` quotes an interpreter lambda term, runs the pure-lambda ``CODEGEN`` on it, and
decodes the resulting Scott Python expression to real Python source. The compiled Python is executed
and checked to compute what the source lambda term computes, so the compiler is verified end to end.
"""

from __future__ import annotations

from co_lambda._compiler import codegen
from co_lambda._dsl import app, build
from co_lambda._prelude import IDENTITY, KESTREL, MULT, PLUS, church


def test_compiles_identity_and_kestrel() -> None:
    # A binder at de Bruijn level k is named "v" followed by k copies of "x" (built by the lambda
    # term over the level), so identity is "lambda v: v" and K names its two binders "v" and "vx".
    assert codegen(build(IDENTITY)) == "lambda v: v"
    assert eval(codegen(build(IDENTITY)))(7) == 7
    kestrel = eval(codegen(build(KESTREL)))
    assert kestrel("a")("b") == "a"


def test_compiles_church_numerals_preserving_meaning() -> None:
    successor = lambda k: k + 1
    for n in range(6):
        compiled = eval(codegen(build(church(n))))
        assert compiled(successor)(0) == n


def test_compiles_applications_preserving_meaning() -> None:
    successor = lambda k: k + 1
    plus = eval(codegen(build(app(app(PLUS, church(2)), church(3)))))
    assert plus(successor)(0) == 5
    times = eval(codegen(build(app(app(MULT, church(2)), church(4)))))
    assert times(successor)(0) == 8
