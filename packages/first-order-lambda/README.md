# first-order-lambda

A first-order-shape-relation interpreter for the lambda-calculus, realizing the
semantics of the paper `first-order/first-order.tex`, depending on `fixpoints`.

A lambda-term's tree is the readout of a single first-order weak-head **shape relation** `Sh`
over term positions. The shape at a position is single-valued, so there is no set to aggregate.
`readout(node)` resolves each position's head via its `Sh` and descends.

Because positions are **interned** (structurally-equal positions are one object, identity is a
pointer test), a cyclic structure has finitely many positions and the least-fixpoint reading
folds it into a finite rational tree where head reduction would unfold forever. So the readout
terminates on every rational tree, and decides an unproductive cycle as the meaningless leaf in
finite time, where head reduction diverges.

`readout` has two re-entry policies:

- `fold_cycles=True` (default) is the least fixpoint `lfp`, the denotation: a guarded cycle
  folds into a finite rational graph (`render` prints it with `#N` back-references); the only
  leaves are variables and the meaningless `⊥`.
- `fold_cycles=False` is the finite-budget first-iteration reading `T↑1`: a re-entered guarded
  cycle is cut to the distinct guarded-cut leaf `∅` (the hole where the budget stopped on a
  productive cycle), kept separate from the meaningless `⊥` (an unproductive cycle, a position
  with no shape). `∅` never appears in the least fixpoint.

The calculus is **pure** (`Var`/`Lam`/`App`): no recursion binder is needed. The `Y` combinator
produces the structural repetition that interning folds, so:

- `Y (cons 0)` (the cyclic stream `r = cons 0 r`) folds to a finite rational tree.
- `Ω = (λx.xx)(λx.xx)` and `Y (λx.x)` (i.e. `letrec x = x`) are unproductive cycles: they read
  out as `⊥` under both readings.

The fold/cut is taken only at **closed** positions, so a folded back-reference never misreads a
free de Bruijn variable.

No parser is provided. Build terms in Python with the HOAS DSL in `_dsl.py` (`lam`, `app`,
`build`), which compiles to a first-order de Bruijn AST; `_prelude.py` collects example terms
(combinators, Scott-encoded lists, Church numerals with Peano arithmetic).
