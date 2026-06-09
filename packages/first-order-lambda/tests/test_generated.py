"""The committed generated LaTeX fragment must match what the generator produces now (no drift).

The compiler-example LaTeX fragment is committed so the paper build stays pure LaTeX. This test asserts
the committed file is exactly the current builder output, so a compiler change that is not regenerated
fails here. (The self-compiled compilers are the staged compilers in the package's
``_generated_stages`` directory, regenerated and checked by the multi-stage bootstrap, not here.)
"""

from __future__ import annotations

from pathlib import Path

from first_order_lambda import _generate

_REPO_ROOT = Path(__file__).resolve().parents[3]
_LATEX_FRAGMENT = _REPO_ROOT / "first-order" / "generated" / "compiler-examples.tex"


def test_generated_latex_fragment_is_current() -> None:
    assert _LATEX_FRAGMENT.read_text() == _generate.compiler_examples_fragment()
