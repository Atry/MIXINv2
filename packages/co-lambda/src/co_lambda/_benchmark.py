"""Benchmark the progressive multi-stage climb expanded into a matrix, doubled across lazy regimes.

The linear multi-stage bootstrap (``_multistage.multi_stage_compile``) yields a sequence of compiler
ENGINES: the interpreter, then the compiler self-compiled at island depth 8, 32, 128, ... The benchmark
expands that climb into the full MATRIX over (engine version) x (target island size): every engine
compiles the compiler's own source at every target depth, and each cell records wall time and peak
resident memory. The linear climb (interpreter -> island 8 -> island 32 -> ...) is the matrix's
near-diagonal; the off-diagonal shows whether a faster (larger-island) engine reaches a target depth the
interpreter cannot. The matrix is measured under both lazy-island regimes (call-by-need and
call-by-name); see ``main``.

Each cell runs in a fresh subprocess so its peak memory is its own. Phase 1 produces the engine files
(the staged compilers under ``_generated_stages/`` in this package) via the bootstrap (each engine
compiled by the previous); phase 2 measures the matrix. The result is committed as
``first-order/generated/self-compilation-benchmark.tex`` (time and memory tabulars) and ``\\input`` by
the paper. Counts are deterministic in the target depth; time and memory are a measured snapshot.

The console entry point ``co-lambda-benchmark`` (see ``pyproject.toml``) runs ``main``;
equivalently ``python -m co_lambda._benchmark``.
"""

from __future__ import annotations

import os
import resource
import subprocess
import sys
import time

from pathlib import Path

# src/co_lambda/_benchmark.py -> repo root is four parents up.
_REPO_ROOT = Path(__file__).resolve().parents[4]
_OUTPUT = _REPO_ROOT / "first-order" / "generated" / "self-compilation-benchmark.tex"
# The staged compilers are generated Python, so they live under src in this package.
_STAGES_DIR = Path(__file__).resolve().parent / "_generated_stages"

# Increasing island depths (configurable via FOL_BENCH_SIZES, comma-separated). 0 is the flattened AST
# (no islands); 192 admits the deepest combinators (depth 191), the largest island.
_SIZES = tuple(int(size) for size in os.environ.get("FOL_BENCH_SIZES", "0,8,32,64,128,192").split(","))
_CELL_TIMEOUT = int(os.environ.get("FOL_BENCH_TIMEOUT", "600"))


def _build_source():
    from co_lambda._dsl import build
    from co_lambda._reduce import run_in_large_stack
    from co_lambda._specialize import COMPILE

    return run_in_large_stack(lambda: build(COMPILE))


def _cell(engine_spec: str, target: int, regime: str, write_path: "str | None") -> None:
    """Run one cell: ``engine_spec`` (``INTERP`` or an engine module path) compiles the compiler at
    island depth ``target`` under the lazy ``regime`` (``need`` or ``name``). Optionally write the output
    to ``write_path`` (it is the next engine). Print ``<cbv> <lazy> <seconds> <peak_gb> <chars>``.

    The regime is the loaded engine's lazy-island ``Thunk`` (call-by-need memoise vs call-by-name
    recompute); it changes only how fast an engine WITH lazy islands runs, never its output. The
    ``INTERP`` row compiles in-process (the lambda ``COMPILE`` interpreted), which does not execute lazy
    islands, so it is regime-independent."""
    from co_lambda._compiler import runnable_module
    from co_lambda._multistage import _load, _run_compiler
    from co_lambda._specialize import SpecializedOption, compile

    source = _build_source()
    option = SpecializedOption(target)
    start = time.perf_counter()
    if engine_spec == "INTERP":
        output = compile(source, option)
    else:
        engine = _load(Path(engine_spec).read_text(), call_by_need=(regime == "need"))
        output = _run_compiler(engine, source, option)
    elapsed = time.perf_counter() - start
    peak_gb = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1e6
    if write_path is not None:
        Path(write_path).write_text(runnable_module(output))  # self-contained, callable engine module
    cbv = output.count("value_island(")
    lazy = output.count("value_island_by_name(")
    print(f"{cbv} {lazy} {elapsed:.6f} {peak_gb:.6f} {len(output)}")


def _run_cell(
    engine_spec: str, target: int, regime: str = "need", write_path: "str | None" = None,
) -> "tuple[float, float] | None":
    """Spawn a worker for one cell; return (seconds, peak_gb) or None if it timed out / failed."""
    command = [sys.executable, "-m", "co_lambda._benchmark", "--cell", engine_spec, str(target), regime]
    if write_path is not None:
        command.append(write_path)
    try:
        done = subprocess.run(command, check=True, capture_output=True, text=True, timeout=_CELL_TIMEOUT)
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired):
        return None
    _cbv, _lazy, seconds, peak_gb, _chars = done.stdout.split()
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


# The two lazy-island regimes the matrix is doubled across: call-by-need (memoise) and call-by-name
# (recompute). They differ only for an engine that contains lazy islands (depth >= 64 here); for an
# engine with none (the interpreter and the small-island engines) both regimes coincide, so that engine
# is measured once and the value is shared between the two regime blocks.
_REGIMES = tuple(os.environ.get("FOL_BENCH_REGIMES", "need,name").split(","))


def _has_lazy_islands(engine_spec: str) -> bool:
    return engine_spec != "INTERP" and "value_island_by_name(" in Path(engine_spec).read_text()


def _run_matrix() -> None:
    from co_lambda._multistage import stage_filename

    out_dir = _STAGES_DIR
    out_dir.mkdir(parents=True, exist_ok=True)

    # Phase 1: the bootstrap climb -- each engine file produced by the previous engine. Reuse an engine
    # file that already exists (the committed stages), so the matrix run need not re-bootstrap them. The
    # filename is Python-version tagged, so a 3.13 run regenerates rather than reusing a 3.11 file. The
    # output is regime-independent, so the engines are bootstrapped under call-by-need.
    engines: "list[tuple[str, str]]" = [("interpreter", "INTERP")]
    previous = "INTERP"
    for size in _SIZES:
        engine_path = out_dir / stage_filename(size)
        if not engine_path.exists():
            _run_cell(previous, size, "need", str(engine_path))
        engines.append((f"island {size}", str(engine_path)))
        previous = str(engine_path)

    # Phase 2: the matrix, doubled across the lazy regimes. A regime-insensitive engine (no lazy islands)
    # is measured once and shared; only the lazy-bearing engines are re-measured per regime.
    measured: "dict[tuple[str, int, str], tuple[float, float] | None]" = {}
    for _name, spec in engines:
        sensitive = _has_lazy_islands(spec)
        for target in _SIZES:
            if sensitive:
                for regime in _REGIMES:
                    measured[(spec, target, regime)] = _run_cell(spec, target, regime)
            else:
                once = _run_cell(spec, target, _REGIMES[0])
                for regime in _REGIMES:
                    measured[(spec, target, regime)] = once

    parts = ["% Generated by co_lambda._benchmark (co-lambda-benchmark). Do not edit.",
             "% Matrix doubled across lazy regimes; rows = engine version, columns = target island size.",
             "% Each regime block: wall-clock time (s) above, peak resident memory (GB) below."]
    for regime in _REGIMES:
        rows = [(name, [measured[(spec, target, regime)] for target in _SIZES]) for name, spec in engines]
        label = "Call-by-need lazy islands (memoise)" if regime == "need" else \
            "Call-by-name lazy islands (recompute)"
        parts += [
            f"\\medskip\\noindent\\textbf{{{label}.}}\\par\\smallskip",
            _tabular(rows, metric=0),
            "\\par\\smallskip",
            _tabular(rows, metric=1),
            "\\par",
        ]
    _OUTPUT.write_text("\n".join(parts) + "\n")
    print(f"wrote {_OUTPUT}")


def main() -> None:
    """Console entry point. With ``--cell <engine> <target> <regime> [write_path]`` run a single matrix
    cell in this worker process (used by the self-spawned subprocesses); otherwise run the full matrix."""
    if len(sys.argv) >= 5 and sys.argv[1] == "--cell":
        _cell(sys.argv[2], int(sys.argv[3]), sys.argv[4], sys.argv[5] if len(sys.argv) > 5 else None)
    else:
        _run_matrix()


if __name__ == "__main__":
    main()
