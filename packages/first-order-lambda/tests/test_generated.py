"""The committed generated artifacts must match what the generator produces now (no drift).

The compiler-example LaTeX fragment and the self-compiled compiler module are committed so the paper
build and the bootstrap test do not run Python generation. These tests assert each committed file is
exactly the current builder output, so a compiler change that is not regenerated fails here.
"""

from __future__ import annotations

from pathlib import Path

from first_order_lambda import _generate, _generated_compiler

_REPO_ROOT = Path(__file__).resolve().parents[3]
_LATEX_FRAGMENT = _REPO_ROOT / "first-order" / "generated" / "compiler-examples.tex"


def test_generated_compiler_module_is_current() -> None:
    committed = Path(_generated_compiler.__file__).read_text()
    assert committed == _generate.generated_compiler_module_text()


def test_generated_latex_fragment_is_current() -> None:
    assert _LATEX_FRAGMENT.read_text() == _generate.compiler_examples_fragment()
