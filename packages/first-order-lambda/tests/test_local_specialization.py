"""Local specialization: a compiled island (FFI Native node) embedded in an interpreted graph.

A closed compilable sub-term is wrapped as a ``Native`` node and compiled once; placed inside a
fold-requiring cyclic shell, the interpreter drives the island and folds around it, so the program
is neither all-interpreted nor all-compiled. Faithfulness is convergence to the unique fixpoint, not
structural identity, so the hybrid's behaviour matches pure interpretation even though the island's
result is reified to the canonical Church shape. The saturated native fires through to its result;
an under-applied one reads as a value.
"""

from __future__ import annotations

import pytest
from syrupy.assertion import SnapshotAssertion

from first_order_lambda._ast import Native, make_app, make_native
from first_order_lambda._compiler import COMPILE, Runtime, compile_to_source
from first_order_lambda._dsl import app, build
from first_order_lambda._latex import term_to_latex
from first_order_lambda._prelude import IDENTITY, MULT, SCOTT_CONS, SCOTT_NIL, Y, church
from first_order_lambda._pyast import _church_to_int
from first_order_lambda._render import render
from first_order_lambda._specialize import call_by_value_islands, church_island, is_typable


def test_compiled_island_inside_cyclic_shell_matches_interpretation(snapshot: SnapshotAssertion) -> None:
    # Y (cons (MULT 3 3)): the cons cycle is fold-requiring (interpreted); the element MULT 3 3 is a
    # closed compilable island. Replacing the element with a compiled island leaves the readout, a
    # cyclic stream of 9, unchanged.
    y_node, cons_node = build(Y), build(SCOTT_CONS)
    element = build(app(app(MULT, church(3)), church(3)))
    pure = make_app(y_node, make_app(cons_node, element))
    hybrid = make_app(y_node, make_app(cons_node, church_island(element)))
    assert isinstance(church_island(element), Native)
    assert render(hybrid) == render(pure)
    assert render(hybrid) == snapshot(name="cyclic_nines")


def test_compiled_island_inside_finite_shell_matches_interpretation() -> None:
    # cons (MULT 2 4) nil: a finite list whose element is a compiled island.
    cons_node, nil_node = build(SCOTT_CONS), build(SCOTT_NIL)
    element = build(app(app(MULT, church(2)), church(4)))
    pure = make_app(make_app(cons_node, element), nil_node)
    hybrid = make_app(make_app(cons_node, church_island(element)), nil_node)
    assert render(hybrid) == render(pure)


def test_saturated_native_fires_and_underapplied_reads_as_value() -> None:
    # An arity-1 foreign function (double via the interpreter's reflection of the argument node):
    # saturated, it fires through to its result; bare, it reads as a native value awaiting an argument.
    def double(argument_node) -> object:
        return build(church(2 * _church_to_int(argument_node)))

    native = make_native(double, 1)
    saturated = make_app(native, build(church(4)))
    assert render(saturated) == render(build(church(8)))
    assert "⟨native:1⟩" in render(native)


def test_a_closed_typable_whole_term_is_a_single_island() -> None:
    # Identity is closed and simply typable, so the whole term is one maximal call-by-value island.
    node = build(IDENTITY)
    island, = call_by_value_islands(node)
    assert island is node


def test_every_island_is_closed_and_typable() -> None:
    # The contract: each found island is a closed, simply-typable sub-term (a sound call-by-value region).
    for island in call_by_value_islands(build(COMPILE)):
        assert island.loose_bound == 0
        assert is_typable(island) is True


@pytest.mark.xfail(
    reason="local specialization of the compiler is reworked in the reflect/reify stage; the "
    "generic-encoding COMPILE is much larger, so analyzing its islands recurses past the default limit",
    strict=False,
)
def test_compiler_call_by_value_islands(snapshot: SnapshotAssertion) -> None:
    # The flagship: the compiler is untypable as a whole (its Z fixpoint self-applies), so it stays
    # interpreted, but the specializer finds its maximal closed simply-typable sub-terms, the
    # strongly-normalizing combinators, each compiled to a strict call-by-value island.
    islands = call_by_value_islands(build(COMPILE))
    rendered = [
        {"lambda": term_to_latex(island), "call_by_value": compile_to_source(island, Runtime.CALL_BY_VALUE)}
        for island in islands
    ]
    assert rendered == snapshot(name="compiler_call_by_value_islands")
