# first-order-lambda

A first-order-shape-relation interpreter for the lambda-calculus, realizing the
semantics of the paper `first-order/first-order.tex`, depending on `fixpoints`.

A lambda-term's Berarducci tree is the readout of a single first-order weak-head
**shape relation** `Sh` over term positions. The shape at a position is single-valued, so
there is no set to aggregate. `Sh` has two resolutions:

- `operational` (`Sbot`): head reduction, the Berarducci tree (unfolded).
- `least_model` (`Semp`): the **least fixpoint**, computed by merging partial Berarducci
  trees (trees with `⊥` holes that the merge fills) over **interned** positions.

Because positions are interned (structurally-equal positions are one object, identity is a
pointer test), a cyclic structure has finitely many positions and the least-fixpoint reading
folds it into a finite rational tree where head reduction would unfold forever. It is
therefore **strictly more defined** than the Berarducci tree (a convergence hierarchy), not a
conservative extension: at an unproductive cycle the operational reading diverges (`⊥`) while
the least fixpoint settles at the empty value (`∅`).

The calculus is **pure** (`Var`/`Lam`/`App`): no recursion binder is needed. The `Y`
combinator produces the structural repetition that interning folds, so:

- `Y (cons 0)` (the cyclic stream `r = cons 0 r`) folds to a finite rational tree.
- `Ω = (λx.xx)(λx.xx)` and `Y (λx.x)` (i.e. `letrec x=x`) are unproductive cycles, so `Semp`
  gives `∅` (operational gives `⊥`).

The empty value is kept as a distinct leaf so the merge is sound (its bottom is never a reused
value); encoding `∅` object-level as `λa.λb.b` is an optional, side-conditioned comma-ok idiom.
The readout folds only at **closed** positions, so a folded back-reference never misreads free
de Bruijn variables.

No parser is provided. Build terms in Python with the HOAS DSL in `_dsl.py`
(`lam`, `app`, `build`), which compiles to a first-order de Bruijn AST. The `_queries.py`
showcase computes recursive properties (reach, elements, a knot-tying map) over cyclic stream
cells as memoized least fixpoints.
