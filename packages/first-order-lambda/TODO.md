# TODO

Two tracked efforts, both greenlit.

## 1. The `interpret`-emitting target: the compiler returns Python with `interpret(...)` heads

The compiler always returns Python. At each node the emitted Python's head is either compiled
(non-interpreter) code, when that subgraph carries the whole-graph by-value certificate (closed and
simply typable), or `interpret(<that sub-term>)`, which re-submits it to the interpreter at runtime.
`COMPILE` as a whole is not by-value-certified (`specialize(COMPILE)` is `INTERPRET`, now that the
fold oracle is bounded), so the self-hosted compiler's Python is `interpret(...)`-headed with inline
call-by-value islands wherever the certificate fires inside it.

- [ ] Add a `PyInterpret` constructor to the compiled Python AST, emitted for any node classified
      `INTERPRET`.
- [ ] Add the `interpret(...)` runtime function: reconstruct the sub-term `Node`, run the interpreter,
      reify the result (a Scott Python-AST value) back to the host.
- [ ] `compile_to_source` recurses: inline call-by-value for by-value-certified closed simply-typable
      sub-terms (islands), `interpret(<sub-term>)` otherwise. Top of `COMPILE` is `interpret(...)`.
- [ ] Per-island reification classification: splice an island as runnable inline code only when its
      arguments and result reify across the boundary (the church-numeral and identity islands, e.g.
      successor, predecessor, identity, applied to church-numeral depths); the Scott-constructor
      islands take Scott-value (function) arguments, which do not reify, so they stay interpreted.
- [ ] Make `_generated_compiler.py` the specialized self-compilation (`interpret(...)`-headed Python
      with reifiable islands inlined); update the bootstrap (`compiled_compiler`, `compile_with`) and
      `test_bootstrap` to the new artifact.
- [ ] Tests; regenerate the `compiler-examples` fragment.

## 2. BinNat arithmetic library + a hard problem solved trivially in lambda terms

A BinNat is an LSB-first Scott list of bits. Restore the library and grow it from encoding into
arithmetic, so naturals are O(log n) rather than Church's O(n), then solve a genuinely hard problem
as a lambda term the interpreter solves, leaning on its tabling (automatic memoization) and
cycle-folding.

- [ ] Restore `_binnat.py` (encode/decode) and add the arithmetic: `succ`, `pred`, `add`, `sub`,
      compare (`<`, `==`), `min`, and multiplication, all on LSB-first bit lists.
- [ ] Tests for the arithmetic, cross-checked against Python ints.
- [ ] Pick a genuinely hard problem that becomes trivial via tabling (automatic memoization) and
      cycle-folding: a hard dynamic program (edit distance, longest common subsequence, knapsack, a
      counting DP) or a hard graph problem (shortest path over a cyclic state graph, game-tree
      minimax) where naive recursion plus tabling is automatically polynomial.
- [ ] Write the solution as a lambda term; demonstrate the interpreter solving it (overlapping
      subproblems memoized by state identity); cross-check against a reference implementation.
- [ ] Optionally a paper paragraph and a generated example.
