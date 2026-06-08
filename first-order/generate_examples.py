#!/usr/bin/env python3
"""Write the generated artifacts: the compiler-example LaTeX fragment and the self-compiled compiler.

Run from the repo root with the package on the path, for example:

    PYTHONPATH=packages/first-order-lambda/src:packages/fixpoints/src \\
        python3 first-order/generate_examples.py

The outputs are committed; the paper build stays pure LaTeX. Tests assert the committed files match
these builders, so regenerating after a compiler change is mandatory (and idempotent otherwise).
"""

from __future__ import annotations

from pathlib import Path

from first_order_lambda._generate import (
    compiler_examples_fragment,
    generated_compiler_large_module_text,
    generated_compiler_module_text,
)

_REPO_ROOT = Path(__file__).resolve().parent.parent

_LATEX_OUTPUT = _REPO_ROOT / "first-order" / "generated" / "compiler-examples.tex"
_SRC = _REPO_ROOT / "packages" / "first-order-lambda" / "src" / "first_order_lambda"
_PYTHON_OUTPUT = _SRC / "_generated_compiler.py"
_PYTHON_LARGE_OUTPUT = _SRC / "_generated_compiler_large.py"


def main() -> None:
    _LATEX_OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    _LATEX_OUTPUT.write_text(compiler_examples_fragment())
    _PYTHON_OUTPUT.write_text(generated_compiler_module_text())
    _PYTHON_LARGE_OUTPUT.write_text(generated_compiler_large_module_text())
    print(f"wrote {_LATEX_OUTPUT}")
    print(f"wrote {_PYTHON_OUTPUT}")
    print(f"wrote {_PYTHON_LARGE_OUTPUT}")


if __name__ == "__main__":
    main()
