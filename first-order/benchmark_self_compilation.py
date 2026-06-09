#!/usr/bin/env python3
"""Benchmark the progressive multi-stage climb expanded into a matrix.

The linear multi-stage bootstrap (``_multistage.multi_stage_compile``) yields a sequence of compiler
ENGINES: the interpreter, then the compiler self-compiled at island depth 8, 32, 128, ... The benchmark
expands that climb into the full MATRIX over (engine version) x (target island size): every engine
compiles the compiler's own source at every target depth, and each cell records wall time and peak
resident memory. The linear climb (interpreter -> island 8 -> island 32 -> ...) is the matrix's
near-diagonal; the off-diagonal shows whether a faster (larger-island) engine reaches a target depth the
interpreter cannot.

Each cell runs in a fresh subprocess so its peak memory is its own. Phase 1 produces the engine files
via the bootstrap (each engine compiled by the previous); phase 2 measures the matrix. The result is
committed as ``generated/self-compilation-benchmark.tex`` (time and memory tabulars) and ``\\input`` by
the paper. Counts are deterministic in the target depth; time and memory are a measured snapshot.

Run from the repo root with the package on the path:

    PYTHONPATH=packages/first-order-lambda/src:packages/fixpoints/src \\
        python3 first-order/benchmark_self_compilation.py
"""

from __future__ import annotations

import os
import resource
import subprocess
import sys
import time

from pathlib import Path

_REPO_ROOT = Path(__file__).resolve().parent.parent
_OUTPUT = _REPO_ROOT / "first-order" / "generated" / "self-compilation-benchmark.tex"

# Increasing island depths. Configurable via FOL_BENCH_SIZES (comma-separated); the default stays below
# the depth-188/191 monster combinators so the matrix is feasible to run end to end.
_SIZES = tuple(int(size) for size in os.environ.get("FOL_BENCH_SIZES", "8,32,128").split(","))
_CELL_TIMEOUT = int(os.environ.get("FOL_BENCH_TIMEOUT", "1800"))


def _build_source():
    from first_order_lambda._dsl import build
    from first_order_lambda._reduce import run_in_large_stack
    from first_order_lambda._specialize import COMPILE

    return run_in_large_stack(lambda: build(COMPILE))


def _cell(engine_spec: str, target: int, write_path: "str | None") -> None:
    """Run one cell: ``engine_spec`` (``INTERP`` or an engine module path) compiles the compiler at
    island depth ``target``. Optionally write the output to ``write_path`` (it is the next engine). Print
    ``<islands> <seconds> <peak_gb> <chars>``."""
    from first_order_lambda._multistage import _load, _run_compiler
    from first_order_lambda._specialize import SpecializedOption, compile

    source = _build_source()
    option = SpecializedOption(target)
    start = time.perf_counter()
    if engine_spec == "INTERP":
        output = compile(source, option)
    else:
        output = _run_compiler(_load(Path(engine_spec).read_text()), source, option)
    elapsed = time.perf_counter() - start
    peak_gb = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1e6
    if write_path is not None:
        Path(write_path).write_text(output)
    print(f"{output.count('value_island(')} {elapsed:.6f} {peak_gb:.6f} {len(output)}")


def _run_cell(engine_spec: str, target: int, write_path: "str | None" = None) -> "tuple[float, float] | None":
    """Spawn a worker for one cell; return (seconds, peak_gb) or None if it timed out / failed."""
    command = [sys.executable, str(Path(__file__).resolve()), "--cell", engine_spec, str(target)]
    if write_path is not None:
        command.append(write_path)
    try:
        done = subprocess.run(command, check=True, capture_output=True, text=True, timeout=_CELL_TIMEOUT)
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired):
        return None
    _islands, seconds, peak_gb, _chars = done.stdout.split()
    return float(seconds), float(peak_gb)


def _cell_text(measured: "tuple[float, float] | None", metric: int) -> str:
    if measured is None:
        return "\\textemdash"
    seconds, peak_gb = measured
    return f"{seconds:.1f}" if metric == 0 else f"{peak_gb:.2f}"


def _tabular(rows: "list[tuple[str, list[tuple[float, float] | None]]]", metric: int) -> str:
    columns = "l" + "r" * len(_SIZES)
    header = "Engine & " + " & ".join(f"island {size}" for size in _SIZES) + " \\\\"
    body = [
        "  " + name + " & " + " & ".join(_cell_text(cell, metric) for cell in cells) + " \\\\"
        for name, cells in rows
    ]
    return "\n".join([
        f"\\begin{{tabular}}{{{columns}}}", "\\hline", header, "\\hline", *body, "\\hline", "\\end{tabular}",
    ])


def main() -> None:
    out_dir = _OUTPUT.parent / "stages"
    out_dir.mkdir(parents=True, exist_ok=True)

    # Phase 1: the bootstrap climb -- produce each engine file from the previous engine.
    engines: "list[tuple[str, str]]" = [("interpreter", "INTERP")]
    previous = "INTERP"
    for size in _SIZES:
        engine_path = out_dir / f"_generated_compiler_island_{size}.py"
        _run_cell(previous, size, str(engine_path))
        engines.append((f"island {size}", str(engine_path)))
        previous = str(engine_path)

    # Phase 2: the matrix -- every engine compiles the compiler at every target depth.
    rows = [(name, [_run_cell(spec, target) for target in _SIZES]) for name, spec in engines]

    table = "\n".join([
        "% Generated by first-order/benchmark_self_compilation.py. Do not edit.",
        "% Time (s), rows = engine version, columns = target island size:",
        _tabular(rows, metric=0),
        "",
        "% Peak memory (GB), rows = engine version, columns = target island size:",
        _tabular(rows, metric=1),
        "",
    ])
    _OUTPUT.write_text(table)
    print(f"wrote {_OUTPUT}")


if __name__ == "__main__":
    if len(sys.argv) >= 4 and sys.argv[1] == "--cell":
        _cell(sys.argv[2], int(sys.argv[3]), sys.argv[4] if len(sys.argv) > 4 else None)
    else:
        main()
