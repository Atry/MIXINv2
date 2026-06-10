"""Andersen-style points-to (alias) analysis as a monotone Datalog least fixpoint.

For the program ``a = new o1; b = a; c = b`` the copy chain propagates the points-to facts, so c
points to o1 (through b and a) but not to o2 (never allocated). This is the basis of alias analysis
in compilers, computed by the same bounded boolean fixpoint as Datalog.
"""

from __future__ import annotations

from co_lambda._dsl import build
from co_lambda._prelude import FALSE, POINTSTO_C_O1, POINTSTO_C_O2, TRUE
from co_lambda._render import render

_TRUE = render(build(TRUE))
_FALSE = render(build(FALSE))


def test_points_to_through_copy_chain() -> None:
    assert render(POINTSTO_C_O1) == _TRUE


def test_does_not_point_to_unallocated_object() -> None:
    assert render(POINTSTO_C_O2) == _FALSE
