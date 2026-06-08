"""The specializing compiler is a lambda term; its output is interpret-headed when uncertified.

``compile_specialized`` is now produced entirely by the lambda term ``COMPILE_SPECIALIZED`` and
serialized to an A-normal-form module binding ``compiled_compiler`` (via the generic codec). A closed
simply-typable whole term binds a strict call-by-value value (no ``interpret`` head); otherwise it binds
``interpret(<reconstruction>)``, the term rebuilt with ``make_var``/``make_lam``/``make_app`` and its
closed, shallow, simply-typable sub-terms spliced as compiled by-value islands (``value_island``). The
module is self-contained given ``interpret_globals``; ``interpret`` hands the node back to the
interpreter. These tests check both shapes and that the interpret-headed module, run, agrees with the
interpreter.
"""

from __future__ import annotations

import os

import pytest

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
from first_order_lambda._specialize import compile_specialized


def _run(source: str):
    """Execute a specialized module and return its ``compiled_compiler`` binding."""
    namespace = dict(interpret_globals())
    exec(source, namespace)  # noqa: S102 - running our own generated source
    return namespace["compiled_compiler"]


def test_typable_whole_graph_compiles_to_inline_call_by_value() -> None:
    # plus 2 3 is closed and simply typable, so it carries the by-value certificate: the module binds a
    # strict call-by-value value (no interpret head), which runs as strict Python.
    source = compile_specialized(build(app(app(PLUS, church(2)), church(3))))
    assert "interpret(" not in source
    assert _run(source)(lambda predecessor: predecessor + 1)(0) == 5


def test_untypable_term_is_interpret_headed_and_agrees_with_the_interpreter() -> None:
    # factorial 3 is untypable (its Y self-applies), so it is interpret-headed; the reconstructed node,
    # interpreted, computes the same value as the source term.
    node = build(app(FACTORIAL, church(3)))
    source = compile_specialized(node)
    assert "interpret(" in source
    assert _church_to_int(_run(source)) == _church_to_int(node) == 6


def test_interpret_headed_source_is_self_contained() -> None:
    # The interpret-headed module runs with only interpret_globals in scope: self-contained text (the
    # node constructors, interpret, value_island), no NameError for an undefined free.
    source = compile_specialized(build(app(FACTORIAL, church(4))))
    assert _run(source) is not None


def test_church_data_islands_are_spliced_into_the_interpret_head() -> None:
    # factorial (2 * 3) is untypable as a whole, so it is interpret-headed; its closed, shallow,
    # simply-typable sub-terms are spliced as compiled by-value islands, and the spliced program agrees
    # with pure interpretation.
    node = build(app(FACTORIAL, app(app(MULT, church(2)), church(3))))
    source = compile_specialized(node)
    assert "interpret(" in source
    assert "value_island(" in source
    assert _church_to_int(_run(source)) == _church_to_int(node) == 720


@pytest.mark.skipif(
    os.environ.get("FOL_REGEN_HEAVY") != "1",
    reason="specializing the whole compiler peaks ~12 GB / minutes (needs FOL_INTERNER_RETAIN=inf); "
    "set FOL_REGEN_HEAVY=1 to run",
)
def test_the_compiler_itself_is_interpret_headed() -> None:
    # COMPILE is untypable (its Z fixpoint self-applies), so the compiler compiles itself to an
    # interpret-headed module with by-value islands spliced; the recursive skeleton is left to interpret.
    # With the island depth bound removed this specializes the large maximal islands, so it is heavy
    # (the no-GC interner retains every reduction); gated behind FOL_REGEN_HEAVY like test_generated.
    source = compile_specialized(build(COMPILE))
    assert "interpret(" in source
    assert "value_island(" in source


def test_typable_combinators_compile_inline() -> None:
    # The simply-typable prelude combinators all carry the by-value certificate (no interpret head).
    for builder in (SUCC, MULT, IS_ZERO, app(app(MULT, church(3)), church(4))):
        assert "interpret(" not in compile_specialized(build(builder))


def test_interpret_headed_compiler_self_hosts() -> None:
    # COMPILE is untypable, so the interpret target is the COMPILE node itself, handed back to the
    # interpreter. Run as a compiler at the node level, it compiles any program to the same generic
    # Scott Python AST the in-process compiler emits (decoded by the same _pyast.decode).
    compiler_node = build(COMPILE)
    for builder in (IDENTITY, KESTREL, SUCC, MULT, app(app(PLUS, church(2)), church(3))):
        program = build(builder)
        assert compile_with_interpreted(compiler_node, program) == compile_to_source(
            program, Runtime.CALL_BY_VALUE
        )
