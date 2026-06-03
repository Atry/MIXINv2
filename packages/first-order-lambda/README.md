# first-order-lambda

A least-fixpoint first-order-shape-relation interpreter for the lambda-calculus,
realizing the semantics of the paper `first-order/first-order.tex`.

A lambda-term's Berarducci tree is the readout of a single first-order weak-head
**shape relation** `Sh` over term nodes. The interpreter computes `Sh` as a least
fixpoint (via the `fixpoints` package), then reads out the Berarducci tree under a
pluggable **aggregate callback** `agg`. The single knob `agg(empty set)` selects the
reading:

- `operational` (`Sbot`): an unproductive head cycle reads out as bottom; this is the
  Berarducci tree.
- `least_model` (`Semp`): an unproductive head cycle reads out as the empty constructor
  `lambda a. lambda b. b`.

Genuine sharing enters only through the `Mu` recursion binder. Beta-reduction copies the
redex body into fresh nodes and shares the argument, so:

- `letrec x = x` (a `Mu` self-loop) reduces to the empty set under `Semp` (reentry on the
  same node), while `Omega` diverges (fresh copies, no reentry).
- `r = cons 0 r` folds into a finite rational tree, while `Y (cons 0)` diverges by copying.

No parser is provided. Build terms in Python with the HOAS DSL in `_dsl.py`
(`lam`, `app`, `mu`, `build`), which compiles to a first-order de Bruijn AST.
