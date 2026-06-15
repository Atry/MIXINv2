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
``papers/co-lambda/generated/self-compilation-benchmark.tex`` (time and memory tabulars) and ``\\input`` by
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

from dataclasses import dataclass
from pathlib import Path


@dataclass(kw_only=True, slots=True, frozen=True)
class CellMeasurement:
    """One benchmark cell's measurement: island counts of the output, wall time, peak resident memory,
    output size, and the total interned nodes created during the compile step (the engine-vs-interpreter
    metric: ``len(_ast._canonical)`` delta under ``FOL_INTERNER_RETAIN=inf``)."""

    cbv: int
    lazy: int
    seconds: float
    peak_gb: float
    chars: int
    interns: int

# src/co_lambda/_benchmark.py -> repo root is four parents up.
_REPO_ROOT = Path(__file__).resolve().parents[4]
_OUTPUT = _REPO_ROOT / "papers" / "co-lambda" / "generated" / "self-compilation-benchmark.tex"
# The staged compilers are generated Python, so they live under src in this package.
_STAGES_DIR = Path(__file__).resolve().parent / "_generated_stages"

# Increasing island depths (configurable via FOL_BENCH_SIZES, comma-separated). 0 is the flattened AST
# (no islands); 192 admits the deepest combinators (depth 191), the largest island.
_SIZES = tuple(int(size) for size in os.environ.get("FOL_BENCH_SIZES", "0,8,32,64,128,192").split(","))
_CELL_TIMEOUT = int(os.environ.get("FOL_BENCH_TIMEOUT", "600"))


def _build_source():
    from co_lambda._dsl import build
    from co_lambda._compile_term import COMPILE
    from co_lambda._runtime import run_in_large_stack

    return run_in_large_stack(lambda: build(COMPILE))


def _cell(engine_spec: str, target: int, regime: str, write_path: "str | None") -> None:
    """Run one cell: ``engine_spec`` (``INTERP`` or an engine module path) compiles the compiler at
    island depth ``target`` under the lazy ``regime`` (``need`` or ``name``). Optionally write the output
    to ``write_path`` (it is the next engine). Print ``<cbv> <lazy> <seconds> <peak_gb> <chars>``.

    The regime is the loaded engine's lazy-island ``Thunk`` (call-by-need memoise vs call-by-name
    recompute); it changes only how fast an engine WITH lazy islands runs, never its output. The
    ``INTERP`` row compiles in-process (the lambda ``COMPILE`` interpreted), which does not execute lazy
    islands, so it is regime-independent.

    Prints ``<cbv> <lazy> <seconds> <peak_gb> <chars> <interns>``. ``interns`` is the ``_ast._canonical``
    delta around the compile STEP: the baseline is taken after the shared source is built (and, for an
    engine, after it is loaded), so it counts only the compilation's interning, not the shared source or
    the one-time engine load. This is the engine-vs-interpreter memory metric (run under
    ``FOL_INTERNER_RETAIN=inf`` so nothing is freed and the count is cumulative)."""
    from co_lambda import _ast
    from co_lambda._runtime import runnable_module
    from co_lambda._multistage import _load, _run_compiler
    from co_lambda._specialize import SpecializedOption, compile

    source = _build_source()
    option = SpecializedOption(target)
    if engine_spec == "INTERP":
        baseline = len(_ast._canonical)
        start = time.perf_counter()
        output = compile(source, option)
        elapsed = time.perf_counter() - start
    else:
        engine = _load(Path(engine_spec).read_text(), call_by_need=(regime == "need"))
        baseline = len(_ast._canonical)  # after load: count only the compile step, not the engine graph
        start = time.perf_counter()
        output = _run_compiler(engine, source, option)
        elapsed = time.perf_counter() - start
    interns = len(_ast._canonical) - baseline
    peak_gb = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1e6
    if write_path is not None:
        Path(write_path).write_text(runnable_module(output))  # self-contained, callable engine module
    cbv = output.count("value_island(")
    lazy = output.count("value_island_by_name(")
    print(f"{cbv} {lazy} {elapsed:.6f} {peak_gb:.6f} {len(output)} {interns}")


def _run_cell(
    engine_spec: str, target: int, regime: str = "need", write_path: "str | None" = None,
) -> "CellMeasurement | None":
    """Spawn a worker for one cell in a FRESH process (the interner is process-global, so each cell must
    measure its own ``_canonical`` from empty). Pin ``FOL_INTERNER_RETAIN=inf`` so the intern count is
    cumulative. Return the ``CellMeasurement`` or None if it timed out / failed."""
    command = [sys.executable, "-m", "co_lambda._benchmark", "--cell", engine_spec, str(target), regime]
    if write_path is not None:
        command.append(write_path)
    environment = {**os.environ, "FOL_INTERNER_RETAIN": "inf"}
    try:
        done = subprocess.run(
            command, check=True, capture_output=True, text=True, timeout=_CELL_TIMEOUT, env=environment,
        )
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired):
        return None
    cbv, lazy, seconds, peak_gb, chars, interns = done.stdout.split()
    return CellMeasurement(
        cbv=int(cbv), lazy=int(lazy), seconds=float(seconds), peak_gb=float(peak_gb),
        chars=int(chars), interns=int(interns),
    )


def _two_cell(target: int) -> None:
    """The 2-cell total-intern protocol, self-contained (no committed stages needed):

    - cell A: the INTERPRETER compiles the COMPILE source at ``target``; its output (a runnable engine
      module) is written to a temp file -- that file IS the engine specialized at ``target``.
    - cell B: that freshly-built engine compiles the SAME source at the SAME ``target``.

    Print both intern counts and the ratio, and ASSERT the two outputs are byte-identical (faithful
    rehosting: an intern change must never hide a semantic change). Each cell runs in its own process so
    its interner starts empty."""
    import tempfile

    with tempfile.TemporaryDirectory() as work:
        engine_file = Path(work) / "engine.py"             # cell A writes the engine here
        engine_output = Path(work) / "engine_output.py"    # cell B writes its compilation here
        cell_a = _run_cell("INTERP", target, "need", str(engine_file))
        assert cell_a is not None, "interpreter cell failed or timed out"
        cell_b = _run_cell(str(engine_file), target, "need", str(engine_output))
        assert cell_b is not None, "engine cell failed or timed out"
        assert engine_file.read_text() == engine_output.read_text(), (
            "engine and interpreter produced different output -- an intern change hid a semantic change"
        )
        ratio = cell_b.interns / cell_a.interns if cell_a.interns else float("inf")
        verdict = "engine WINS" if cell_b.interns < cell_a.interns else "engine does NOT win"
        print(f"target={target}  interpreter_interns={cell_a.interns}  engine_interns={cell_b.interns}  "
              f"ratio={ratio:.4f}  ({verdict}); output byte-identical")


def _cell_text(measured: "CellMeasurement | None", metric: int) -> str:
    if measured is None:
        return "\\textemdash"
    if metric == 0:
        return f"{measured.seconds:.1f}"
    if metric == 1:
        return f"{measured.peak_gb:.2f}"
    return str(measured.interns)


def _tabular(rows: "list[tuple[str, list[CellMeasurement | None]]]", metric: int) -> str:
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
    measured: "dict[tuple[str, int, str], CellMeasurement | None]" = {}
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
             "% Each regime block: wall-clock time (s), peak resident memory (GB), and interned nodes."]
    for regime in _REGIMES:
        rows = [(name, [measured[(spec, target, regime)] for target in _SIZES]) for name, spec in engines]
        label = "Call-by-need lazy islands (memoise)" if regime == "need" else \
            "Call-by-name lazy islands (recompute)"
        parts += [
            f"\\medskip\\noindent\\textbf{{{label}.}}\\par\\smallskip",
            _tabular(rows, metric=0),
            "\\par\\smallskip",
            _tabular(rows, metric=1),
            "\\par\\smallskip",
            _tabular(rows, metric=2),
            "\\par",
        ]
    _OUTPUT.write_text("\n".join(parts) + "\n")
    print(f"wrote {_OUTPUT}")


def main() -> None:
    """Console entry point. ``--cell <engine> <target> <regime> [write_path]`` runs a single matrix cell
    in this worker process (used by the self-spawned subprocesses); ``--two-cell <target>`` runs the
    total-intern protocol (interpreter vs engine on the same source); otherwise run the full matrix."""
    if len(sys.argv) >= 5 and sys.argv[1] == "--cell":
        _cell(sys.argv[2], int(sys.argv[3]), sys.argv[4], sys.argv[5] if len(sys.argv) > 5 else None)
    elif len(sys.argv) >= 3 and sys.argv[1] == "--two-cell":
        _two_cell(int(sys.argv[2]))
    else:
        _run_matrix()


if __name__ == "__main__":
    main()
