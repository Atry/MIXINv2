"""The source-to-LaTeX printer names variables exactly as the compiler does, so they line up.

``term_to_latex`` prints a source term with parameter names ``v_{level}`` matching the ``v{level}``
the compiler emits, so the displayed lambda and the generated Python read off against each other one
to one. The snapshots pin the rendered LaTeX; the name-match test checks the correspondence.
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


@pytest.mark.parametrize(
    "builder",
    [IDENTITY, KESTREL, church(0), church(2), SUCC, PLUS, MULT, IS_ZERO],
)
def test_latex_names_match_compiled_python(builder) -> None:
    node = build(builder)
    latex = term_to_latex(node)
    python = compile_to_source(node, Runtime.EAGER)
    latex_levels = sorted({int(level) for level in re.findall(r"v_\{(\d+)\}", latex)})
    python_levels = sorted({int(level) for level in re.findall(r"\bv(\d+)\b", python)})
    assert latex_levels == python_levels
