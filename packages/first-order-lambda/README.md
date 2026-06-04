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
finite time, where head reduction diverges. Interning is the *finest* instance of a pluggable
**position congruence** (see below); a coarser sound congruence folds more.

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

## Position congruence (a second parameter)

*Which* positions count as "the same" when the readout folds is a parameter, a **position
congruence** (`Definition def:congruence` in the paper). `readout(node, congruence=...)` keys the
fold on `congruence.key(node)` instead of raw object identity. A congruence is **sound** when it
is contained in tree equality (it never folds positions with different trees); stated over the
full signature, soundness is the congruence law read coinductively, so a well-formed congruence
folds without changing the denotation. `_congruence.py` provides four instances, from finest to
coarser:

- `IdentityCongruence` (the default): syntactic de Bruijn identity, `key = id(node)`, a pointer
  test. The finest instance; reproduces the pure-interning readout exactly.
- `EGraphCongruence`: a union-find with congruence closure over the *syntactic* constructors. The
  caller asserts sound (tree-equal) merges with `merge(a, b)`; closure propagates them to
  `App`/`Lam` parents, and the readout shares the merged positions. The inductive
  (least-fixpoint) family: it folds whatever finitely many tree-equal pairs generate.
- `PositionEGraphCongruence`: the faithful `def:congruence`, keyed on the *demanded descent* (the
  shape tree) rather than the syntax. It auto-folds any two positions bisimilar under `Sh` with
  no asserted merge (a redex and its reduct collapse on sight), folding exactly the rational
  fragment. It cannot finitize an infinitely-presented shape graph, so the `Y F 0` witness below
  still diverges: bisimulation alone does not rescue a dead-argument cycle.
- `DeadSubtermCongruence(rules=...)`: equality up to dead subterms, the key being the syntax with
  every dead-argument slot erased to a canonical placeholder (a tree-preserving map, not a
  congruence closure). The dead slots are recognised by a **library of sound rules**; the caller
  enables a subset. `RecursionArgumentRule` folds the paper's `Y F 0` witness, where a
  constant-headed recursion carries an index it never inspects; `UnusedParameterRule` erases the
  argument of a function that discards it. This is the one reading that folds the witness, which
  neither e-graph can.

No parser is provided. Build terms in Python with the HOAS DSL in `_dsl.py` (`lam`, `app`,
`build`), which compiles to a first-order de Bruijn AST; `_prelude.py` collects example terms
(combinators, Scott-encoded lists, Church numerals with Peano arithmetic).
