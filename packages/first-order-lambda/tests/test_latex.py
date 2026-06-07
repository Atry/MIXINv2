"""The source-to-LaTeX printer renders a term with readable bound-variable names.

``term_to_latex`` names a binder by its de Bruijn level with a readable letter (``x``, ``y``, ...),
not the compiler's ``v{level}``, so the displayed lambda reads naturally. The snapshots pin the
rendered LaTeX; the structural test checks the lambda has the same number of binders as the Python
the compiler emits (the level-`k` binder is the Python parameter ``v{k}``).
"""

from __future__ import annotations

import re

import pytest
from syrupy.assertion import SnapshotAssertion

from first_order_lambda._compiler import Runtime, compile_to_source
from first_order_lambda._dsl import build
from first_order_lambda._latex import term_to_latex
from first_order_lambda._prelude import IDENTITY, IS_ZERO, KESTREL, MULT, PLUS, SUCC, church


@pytest.mark.parametrize(
    "name, builder",
    [("identity", IDENTITY), ("kestrel", KESTREL), ("church_2", church(2)), ("successor", SUCC)],
)
def test_term_to_latex(name: str, builder, snapshot: SnapshotAssertion) -> None:
    assert term_to_latex(build(builder)) == snapshot(name=name)


def test_term_to_latex_uses_readable_names() -> None:
    # No de Bruijn / v-style names in the rendered lambda; the first binders are x, y, z.
    rendered = term_to_latex(build(SUCC))
    assert "v_{" not in rendered and "v0" not in rendered
    assert rendered == "\\lambda x.\\, \\lambda y.\\, \\lambda z.\\, y\\, (x\\, y\\, z)"


@pytest.mark.parametrize(
    "builder",
    [IDENTITY, KESTREL, church(0), church(2), SUCC, PLUS, MULT, IS_ZERO],
)
def test_latex_has_same_binder_count_as_compiled_python(builder) -> None:
    node = build(builder)
    latex_binders = len(re.findall(r"\\lambda", term_to_latex(node)))
    python_binders = len(re.findall(r"\blambda\b", compile_to_source(node, Runtime.EAGER)))
    assert latex_binders == python_binders
