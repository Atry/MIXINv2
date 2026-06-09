"""Progressive multi-stage self-compilation of the compiler.

The compiler ``COMPILE`` is untypable as a whole, so it stays interpreted, but it contains closed
simply-typable sub-terms that compile to strict call-by-value islands. The more of them are compiled
(a larger island depth), the more of the compiler runs as native Python and the less is interpreted,
so a larger-island compiler is faster and lighter. That is the lever for a bootstrap:

  stage 1: the compiler run on the INTERPRETER compiles the compiler into a small-island compiler;
  stage 2: that small-island compiler compiles the compiler into a mid-island compiler;
  stage 3: the mid-island compiler compiles the compiler into a larger-island compiler;
  ...      until the largest possible island (a depth past the deepest sub-term).

Each stage is compiled by the PREVIOUS stage's compiler (stage 1's is the interpreter), and each stage
is written to its own file. Every stage compiles the same fixed source: the compiler's own source.
Each stage's compiler is a faithful re-hosting (it compiles any program to the same Python as the
in-process compiler); the stages differ only in how the compiler doing the compiling is itself
realized, hence in speed and memory.
"""

from __future__ import annotations

import resource
import time

from dataclasses import dataclass
from pathlib import Path

from first_order_lambda._compiler import interpret_globals, quote
from first_order_lambda._dsl import build
from first_order_lambda._pyast import to_anf_source
from first_order_lambda._reduce import run_in_large_stack
from first_order_lambda._specialize import COMPILE, SpecializedOption, compile


@dataclass(frozen=True, kw_only=True, slots=True)
class StageResult:
    """One stage of the bootstrap: the compiler self-compiled at ``island_size`` by the previous stage."""

    stage: int
    island_size: int
    path: Path
    islands: int
    seconds: float
    peak_rss_gb: float


def _load(module_text: str) -> object:
    """Execute a generated compiler module and return its ``compiled_compiler`` node (the engine)."""
    namespace = dict(interpret_globals())
    exec(module_text, namespace)  # noqa: S102 - running our own generated compiler
    return namespace["compiled_compiler"]


def _run_compiler(engine: object, source: object, option: SpecializedOption) -> str:
    """Run a compiled ``engine`` (a ``COMPILE`` node, applied to an option and a quoted program) on the
    ``source`` node, serializing the interpret-headed result to an A-normal-form module. The deep
    quote/build/serialize all run with the enlarged stack the compiler-scale graph needs."""
    def _go() -> str:
        applied = engine(build(option.scott()), build(quote(source)))
        return to_anf_source(applied, "compiled_compiler")

    return run_in_large_stack(_go)


def multi_stage_compile(island_sizes: "tuple[int, ...]", *, out_dir: Path) -> "list[StageResult]":
    """Bootstrap the compiler through ``island_sizes`` (increasing), each stage compiled by the previous.

    Stage 1 uses the interpreter; stage ``k`` (k>=1 after the first) runs stage ``k-1``'s compiled
    compiler. The fixed source is the compiler's own source ``build(COMPILE)``. Each stage's compiler is
    written to ``out_dir/_generated_compiler_island_<size>.py``. Returns one ``StageResult`` per stage.
    """
    out_dir.mkdir(parents=True, exist_ok=True)
    source = run_in_large_stack(lambda: build(COMPILE))
    engine: object | None = None  # stage 1's engine is the interpreter (None)
    results: "list[StageResult]" = []
    for stage, size in enumerate(island_sizes, start=1):
        option = SpecializedOption(size)
        start = time.perf_counter()
        artifact = compile(source, option) if engine is None else _run_compiler(engine, source, option)
        elapsed = time.perf_counter() - start
        peak_rss_gb = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1e6
        path = out_dir / f"_generated_compiler_island_{size}.py"
        path.write_text(artifact)
        engine = _load(artifact)
        results.append(StageResult(
            stage=stage,
            island_size=size,
            path=path,
            islands=artifact.count("value_island("),
            seconds=elapsed,
            peak_rss_gb=peak_rss_gb,
        ))
    return results
