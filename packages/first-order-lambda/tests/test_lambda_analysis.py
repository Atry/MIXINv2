"""The specialization analysis is written in the lambda-calculus and drives local specialization.

``CLOSED`` is a pure lambda term run by the interpreter on the quoted program; ``is_closed`` reads
its Church-boolean verdict. The verdict is the certificate that selects a compilable island: a closed
sub-term can be compiled and embedded, so the analysis written in lambda decides what Stage-2 local
specialization compiles. This is the simplest certificate; the pipeline (lambda analysis to island
selection to a compiled-plus-interpreted residual) runs end to end and matches pure interpretation.
"""

from __future__ import annotations

import pytest

from first_order_lambda._analysis import is_closed
from first_order_lambda._ast import make_app, make_lam, make_var
from first_order_lambda._dsl import app, build, lam
from first_order_lambda._prelude import IDENTITY, MULT, SCOTT_CONS, Y, church
from first_order_lambda._render import render
from first_order_lambda._specialize import value_island


@pytest.mark.parametrize(
    "name, node, expected",
    [
        ("identity", build(IDENTITY), True),
        ("mult_3_3", build(app(app(MULT, church(3)), church(3))), True),
        ("church_2", build(church(2)), True),
        ("free_var", make_var(0), False),
        ("lambda_bound_var", make_lam(make_var(0)), True),
        ("lambda_free_var", make_lam(make_var(1)), False),
        ("open_application", make_app(make_var(0), make_lam(make_var(0))), False),
    ],
)
def test_lambda_analysis_classifies_closedness(name: str, node, expected: bool) -> None:
    assert is_closed(node) is expected


def test_lambda_verdict_drives_local_specialization() -> None:
    # The lambda analysis certifies the element closed, so it is compiled to an island; the cyclic
    # cons shell stays interpreted, and the hybrid's readout equals pure interpretation.
    element = build(app(app(MULT, church(3)), church(3)))
    assert is_closed(element) is True
    y_node, cons_node = build(Y), build(SCOTT_CONS)
    pure = make_app(y_node, make_app(cons_node, element))
    hybrid = make_app(y_node, make_app(cons_node, value_island(element)))
    assert render(hybrid) == render(pure)


def test_open_term_is_not_certified_for_islanding() -> None:
    # An open sub-term depends on its context, so the closedness certificate refuses it; island
    # selection would skip it and leave it interpreted.
    open_term = make_lam(make_var(1))
    assert is_closed(open_term) is False
