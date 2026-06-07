"""Analysis-driven specialization: the analysis classifies, and the chosen runtime agrees.

The specializer interprets by default and compiles to Python only when an analysis certifies the
result is unchanged: EAGER for a simply-typed (strongly normalizing) term, LAZY for a term whose
interpreted behaviour is a finite normal form, FIXPOINT (interpret) otherwise. These tests check the
two classifiers (``is_typable``, ``choose_runtime``) and that the specialized output, run, equals
the interpreter's value.
"""

from __future__ import annotations

import pytest

from first_order_lambda._compiler import Runtime, runtime_globals
from first_order_lambda._dsl import app, build
from first_order_lambda._prelude import (
    CYCLIC_ZEROS,
    EXP,
    FACTORIAL,
    FIBONACCI,
    IS_ZERO,
    MULT,
    OMEGA,
    PLUS,
    PRED,
    SUCC,
    Y,
    church,
)
from first_order_lambda._pyast import _church_to_int
from first_order_lambda._specialize import choose_runtime, is_typable, specialize

_TYPABLE = {
    "church(3)": build(church(3)),
    "succ": build(SUCC),
    "plus": build(PLUS),
    "mult": build(MULT),
    "exp": build(EXP),
    "pred": build(PRED),
    "is_zero": build(IS_ZERO),
    "plus 2 3": build(app(app(PLUS, church(2)), church(3))),
}

# Y/factorial/Fibonacci self-apply through the fixpoint combinator (x x), whose constraint
# alpha = alpha -> beta fails the occurs check, so they are not simply typable.
_UNTYPABLE = {
    "Y": build(Y),
    "OMEGA": OMEGA,
    "factorial": build(FACTORIAL),
    "fibonacci": build(FIBONACCI),
}


@pytest.mark.parametrize("name", sorted(_TYPABLE))
def test_typable_terms_are_simply_typed(name: str) -> None:
    assert is_typable(_TYPABLE[name]) is True


@pytest.mark.parametrize("name", sorted(_UNTYPABLE))
def test_recursive_terms_are_not_simply_typed(name: str) -> None:
    assert is_typable(_UNTYPABLE[name]) is False


@pytest.mark.parametrize("name", sorted(_TYPABLE))
def test_typable_terms_choose_eager(name: str) -> None:
    # Strong normalization is certified, so the strict runtime is safe.
    assert choose_runtime(_TYPABLE[name]) is Runtime.EAGER


@pytest.mark.parametrize(
    "name, node",
    [("factorial 4", build(app(FACTORIAL, church(4)))), ("fibonacci 5", build(app(FIBONACCI, church(5))))],
)
def test_normalizing_recursion_chooses_lazy(name: str, node) -> None:
    # Untypable but the interpreter reads a finite normal form (no fold), so call-by-name suffices.
    assert choose_runtime(node) is Runtime.LAZY


@pytest.mark.parametrize("name, node", [("Y (cons 0)", CYCLIC_ZEROS), ("OMEGA", OMEGA)])
def test_cyclic_behaviour_stays_interpreted(name: str, node) -> None:
    # The interpreter folded a cycle (or hit bottom), so only the fixpoint default is correct.
    assert choose_runtime(node) is Runtime.FIXPOINT


def _run_church(node) -> int:
    """Observe a specialized closed Church numeral as an ``int``, per the chosen runtime."""
    runtime, source = specialize(node)
    match runtime:
        case Runtime.FIXPOINT:
            assert source is None, "FIXPOINT means interpret: no compiled source"
            return _church_to_int(node)
        case Runtime.EAGER:
            assert source is not None
            numeral = eval(source)
            return numeral(lambda predecessor: predecessor + 1)(0)
        case Runtime.LAZY:
            assert source is not None
            environment = runtime_globals(runtime)
            numeral = eval(source, environment)
            thunk, force = environment["Thunk"], environment["force"]
            successor = lambda counted: force(counted) + 1
            return numeral(thunk(lambda: successor))(thunk(lambda: 0))
        case _:
            raise ValueError(f"unexpected runtime {runtime!r}")


@pytest.mark.parametrize(
    "node",
    [
        build(app(app(PLUS, church(2)), church(3))),  # EAGER
        build(app(app(MULT, church(3)), church(4))),  # EAGER
        build(app(FACTORIAL, church(4))),  # LAZY
        build(app(FIBONACCI, church(5))),  # LAZY
    ],
)
def test_specialized_output_matches_interpreter(node) -> None:
    assert _run_church(node) == _church_to_int(node)
