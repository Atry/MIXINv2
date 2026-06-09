"""Progressive multi-stage self-compilation: each stage is compiled by the previous, and faithful.

Stage 1 is the compiler run on the interpreter; stage ``k`` is produced by RUNNING stage ``k-1``'s
compiled compiler on the compiler's own source at a larger island depth. Each stage's compiler is a
faithful re-hosting: it compiles a program to the same Python as the in-process compiler. The bootstrap
self-compiles the compiler, so it peaks at gigabytes over minutes; it is gated behind ``FOL_REGEN_HEAVY``.
"""

from __future__ import annotations

import os

import pytest

from first_order_lambda._dsl import build
from first_order_lambda._multistage import _load, _run_compiler, multi_stage_compile
from first_order_lambda._prelude import IDENTITY, KESTREL, church
from first_order_lambda._specialize import SpecializedOption, compile


@pytest.mark.skipif(
    os.environ.get("FOL_REGEN_HEAVY") != "1",
    reason="multi-stage self-compilation peaks gigabytes over minutes; set FOL_REGEN_HEAVY=1 to run",
)
def test_each_stage_is_compiled_by_the_previous_and_is_faithful(tmp_path) -> None:
    results = multi_stage_compile((8, 32), out_dir=tmp_path)
    assert [result.stage for result in results] == [1, 2]
    assert all(result.path.exists() for result in results)
    # A larger island depth admits at least as many islands (the climb compiles more, not less).
    assert results[1].islands >= results[0].islands
    # Every stage's compiler compiles sample programs to exactly the in-process compiler's Python.
    for result in results:
        engine = _load(result.path.read_text())
        for term in (IDENTITY, KESTREL, church(3)):
            node = build(term)
            assert _run_compiler(engine, node, SpecializedOption(8)) == compile(node, SpecializedOption(8))
