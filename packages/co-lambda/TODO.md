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
- [x] The `interpret` runtime and result reify reuse the existing FFI boundary (`_decode_pyast` for the
      Scott Python-AST encoding, as `church_island`/`_pyast` do for theirs), not new NbE.
- [x] Self-hosting through the interpret target: `compile_with_interpreted` runs the interpret-headed
      compiler (the `COMPILE` node) on a program and reifies the result; it agrees with
      `compile_to_source`.
- [x] Recurse into the interpret head: `compile_interpreted(node, islands)` splices certified closed
      sub-terms as compiled `church_island(...)` calls rather than reconstructing them, so they run
      compiled inside the interpreted skeleton; `compile_specialized` passes `church_numeral_islands`.
- [x] Per-island reification classification, SOUND: an island is spliced only when its principal type
      is the Church-numeral type `(a -> a) -> a -> a` (`_is_church_type`), which by parametricity means
      it is a Church numeral. A behavioural probe is unsound (`identity` coincides with one under
      succ/zero); the type test excludes `identity`, `succ`, and the Scott constructors, so the
      compiler's higher-order islands stay interpreted (the FFI reify here is scoped to Church).
- [x] Make `_generated_compiler.py` the specialized self-compilation (`interpret(...)`-headed Python);
      bootstrap (`compiled_compiler`, `compile_with_interpreted`) and `test_bootstrap` use it.
- [x] Tests; regenerated the `compiler-examples` fragment (self-hosting block is interpret-headed).

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
