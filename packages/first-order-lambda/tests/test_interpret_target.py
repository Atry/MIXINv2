"""The interpret-emitting target: the compiler always returns Python, interpret-headed when uncertified.

``compile_specialized`` returns Python whose head is non-interpreter code when the whole graph carries
the by-value certificate (closed and simply typable), and an ``interpret(...)`` call otherwise. The
``interpret(...)`` argument reconstructs the term with ``make_var``/``make_lam``/``make_app``, so the
source is self-contained given ``interpret_globals``; ``interpret`` hands the node back to the
interpreter, which computes the value when it is observed. These tests check both heads and that the
interpret-headed source, run, agrees with interpreting the term directly.
"""

from __future__ import annotations

from first_order_lambda._compiler import COMPILE, interpret_globals
from first_order_lambda._dsl import app, build
from first_order_lambda._prelude import FACTORIAL, IS_ZERO, MULT, PLUS, SUCC, church
from first_order_lambda._pyast import _church_to_int
from first_order_lambda._specialize import compile_specialized


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
    # The only free names the interpret-headed source uses are the four in interpret_globals.
    source = compile_specialized(build(app(FACTORIAL, church(4))))
    permitted = set(interpret_globals()) | {"interpret"}
    used = {token for token in __import__("re").findall(r"[A-Za-z_]\w*", source)}
    assert used <= permitted


def test_the_compiler_itself_is_interpret_headed() -> None:
    # COMPILE is untypable (its Z fixpoint self-applies), so the compiler compiles itself to
    # interpret-headed Python: the recursive skeleton is left to the interpreter.
    source = compile_specialized(build(COMPILE))
    assert source.startswith("interpret(make_lam(")


def test_typable_combinators_compile_inline() -> None:
    # The simply-typable prelude combinators all carry the by-value certificate (no interpret head).
    for builder in (SUCC, MULT, IS_ZERO, app(app(MULT, church(3)), church(4))):
        assert not compile_specialized(build(builder)).startswith("interpret(")
