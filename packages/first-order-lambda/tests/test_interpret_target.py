"""The interpret-emitting target: the compiler always returns Python, interpret-headed when uncertified.

``compile_specialized`` returns Python whose head is non-interpreter code when the whole graph carries
the by-value certificate (closed and simply typable), and an ``interpret(...)`` call otherwise. The
``interpret(...)`` argument reconstructs the term with ``make_var``/``make_lam``/``make_app``, so the
source is self-contained given ``interpret_globals``; ``interpret`` hands the node back to the
interpreter, which computes the value when it is observed. These tests check both heads and that the
interpret-headed source, run, agrees with interpreting the term directly.
"""

from __future__ import annotations

from first_order_lambda._compiler import (
    COMPILE,
    Runtime,
    compile_to_source,
    compile_with_interpreted,
    interpret_globals,
)
from first_order_lambda._dsl import app, build
from first_order_lambda._prelude import FACTORIAL, IDENTITY, IS_ZERO, KESTREL, MULT, PLUS, SUCC, church
from first_order_lambda._pyast import _church_to_int
from first_order_lambda._specialize import church_numeral_islands, compile_specialized


def _eval_interpreted(source: str):
    return eval(source, interpret_globals())  # noqa: S307 - evaluating our own generated source


def test_typable_whole_graph_compiles_to_inline_call_by_value() -> None:
    # plus 2 3 is closed and simply typable, so it carries the by-value certificate and compiles inline
    # (no interpret head); it runs as strict Python.
    source = compile_specialized(build(app(app(PLUS, church(2)), church(3))))
    assert not source.startswith("interpret(")
    assert eval(source)(lambda predecessor: predecessor + 1)(0) == 5  # noqa: S307


def test_untypable_term_is_interpret_headed_and_agrees_with_the_interpreter() -> None:
    # factorial 3 is untypable (its Y self-applies), so it is interpret-headed; the reconstructed node,
    # interpreted, computes the same value as the source term.
    node = build(app(FACTORIAL, church(3)))
    source = compile_specialized(node)
    assert source.startswith("interpret(make_app(")
    assert _church_to_int(_eval_interpreted(source)) == _church_to_int(node) == 6


def test_interpret_headed_source_is_self_contained() -> None:
    # The interpret-headed source evaluates with only interpret_globals in scope: it is self-contained
    # text (the node constructors, interpret, and church_island), no NameError for an undefined free.
    source = compile_specialized(build(app(FACTORIAL, church(4))))
    assert eval(source, interpret_globals()) is not None  # noqa: S307


def test_church_data_islands_are_spliced_into_the_interpret_head() -> None:
    # factorial (2 * 3) is untypable as a whole, so it is interpret-headed; its closed church-producing
    # sub-terms (2 * 3 and the constants inside factorial) are spliced as compiled by-value islands, and
    # the spliced program agrees with pure interpretation.
    node = build(app(FACTORIAL, app(app(MULT, church(2)), church(3))))
    assert len(church_numeral_islands(node)) >= 1
    source = compile_specialized(node)
    assert source.startswith("interpret(")
    assert "church_island(" in source
    assert _church_to_int(_eval_interpreted(source)) == _church_to_int(node) == 720


def test_the_compiler_itself_is_interpret_headed() -> None:
    # COMPILE is untypable (its Z fixpoint self-applies), so the compiler compiles itself to
    # interpret-headed Python: the recursive skeleton is left to the interpreter.
    source = compile_specialized(build(COMPILE))
    assert source.startswith("interpret(make_lam(")


def test_typable_combinators_compile_inline() -> None:
    # The simply-typable prelude combinators all carry the by-value certificate (no interpret head).
    for builder in (SUCC, MULT, IS_ZERO, app(app(MULT, church(3)), church(4))):
        assert not compile_specialized(build(builder)).startswith("interpret(")


def test_interpret_headed_compiler_self_hosts() -> None:
    # The compiler compiled to interpret-headed Python, evaluated, is the COMPILE node handed back to
    # the interpreter. Run as a compiler, it compiles any program to the same source as the in-process
    # compiler: the bootstrap through the interpret target, reified by the existing _decode_pyast.
    compiler_node = _eval_interpreted(compile_specialized(build(COMPILE)))
    for builder in (IDENTITY, KESTREL, SUCC, MULT, app(app(PLUS, church(2)), church(3))):
        program = build(builder)
        assert compile_with_interpreted(compiler_node, program) == compile_to_source(
            program, Runtime.CALL_BY_VALUE
        )
