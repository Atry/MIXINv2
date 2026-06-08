# TODO

Two tracked efforts, both greenlit.

## 1. The `interpret`-emitting target: the compiler returns Python with `interpret(...)` heads

The compiler always returns Python. At each node the emitted Python's head is either compiled
(non-interpreter) code, when that subgraph carries the whole-graph by-value certificate (closed and
simply typable), or `interpret(<that sub-term>)`, which re-submits it to the interpreter at runtime.
`COMPILE` as a whole is not by-value-certified (`specialize(COMPILE)` is `INTERPRET`, now that the
fold oracle is bounded), so the self-hosted compiler's Python is `interpret(...)`-headed with inline
call-by-value islands wherever the certificate fires inside it.

- [x] Emit interpret-headed Python: `compile_interpreted` reconstructs the node with
      `make_var`/`make_lam`/`make_app` inside an `interpret(...)` call (self-contained text), and
      `interpret`/`interpret_globals` hand it back to the interpreter.
- [x] Whole-graph decision: `compile_specialized` is inline call-by-value when the term is closed and
      simply typable, `interpret(...)` otherwise. Top of `COMPILE` is `interpret(...)`.
- [ ] Recurse into the interpret head: splice by-value-certified closed simply-typable sub-terms as
      inline islands rather than leaving the whole subgraph interpreted (the per-island step below).
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

- [x] Restore `_binnat.py` (encode/decode) and add the arithmetic: `succ`, `pred`, `add`, `sub`,
      compare (`<`, `==`), `min`, `max`, and multiplication, all on LSB-first bit lists.
- [x] Tests for the arithmetic, cross-checked against Python ints.
- [x] Pick a genuinely hard problem that becomes trivial via tabling: **edit distance** (Levenshtein).
      Its subproblems are pairs of suffixes of the inputs, which are shared interned sub-nodes, so a
      repeated subproblem is the same `App` node and the interpreter memoizes it by identity. The
      exponential naive recursion collapses to the O(mn) table with no memoization code. (Knapsack and
      cyclic shortest path do not fit: computed capacities do not re-intern, and min over an infinite
      domain through a cycle folds to bottom, not the answer.)
- [x] Write the solution as a lambda term (`_editdistance.py`), memoized for free by the interpreter;
      cross-check against the textbook DP reference, and check a moderate input stays fast.
- [ ] Optionally a paper paragraph and a generated example.
