import InheritanceCalculus.Restriction

/-!
# Tabled evaluation (Algorithm alg:tabled)

This module formalizes the paper's Algorithm "Tabled evaluation of
equations eq:supers–eq:this" (alg:tabled, tex line ~4110) as a big-step
operational semantics: `Run` is the judgment of one `Resolve` call (and of a
finite sequence of such calls), and `Rounds`/`Tabled` is the outer
repeat-until-stable loop, iterating from the empty accumulator.

## Modeling notes

- **Relational big-step, not a function.** `Resolve` recurses along the
  dependency graph and the outer loop repeats until stable; neither is
  guaranteed to terminate (the paper's Turing-completeness discussion). A
  big-step derivation exists exactly for the terminating runs, so
  thm:tabling-soundness (4) ("when the iteration does not stabilize, the
  algorithm does not return") is built into the semantics: a run that does
  not stabilize has no `Rounds` derivation, hence no returned answer.
- **State.** `TState` carries the pseudocode's three data: `approx` (every
  query's answer set so far, kept across rounds), `cache` (the queries
  recomputed in the current round), `stack` (the queries being computed), plus
  the round's `changed` flag. The flag is a `Prop` because the algorithm's
  test `produced ⊄ approx[q]` is propositional at this level of abstraction.
- **Reading sub-query facts through `Resolve`.** The production step
  ("`produced ←` the values of all instances of the right-hand side of `q`'s
  equation, every sub-query fact read through `Resolve`") is modeled by a
  *read snapshot* `M : QAMap` constrained between two bounds, rather than by
  one fixed interleaving of reads:

  Additionally, `hcover` states that every sub-query the right-hand side
  reads under the snapshot (`Reads Inh M q`) is among the called queries,
  rendering the pseudocode's "every sub-query fact read through `Resolve`".

  * upper bound: `M ≤ QAMap.restrict (cache ∪ stack) approx₁`, where `approx₁` is
    the accumulator after the sub-calls — every fact read was returned by a
    `Resolve` call (so its query is memoized in `cache`, or re-entrant on
    `stack`), and every returned answer set is contained in the accumulator at
    the end of the sub-calls, since the accumulator only grows
    (`run_approx_mono`);
  * lower bound: `QAMap.restrict (cache ∪ stack) approx₀ ≤ M`, where `approx₀` is
    the accumulator at the entry of this `Resolve` call — a read of a called
    query returns the *full* current answer set of that query, which contains
    its entry value.

  Every actual execution of the pseudocode (any evaluation order, any read
  timing) satisfies these bounds, so the judgment over-approximates the
  implemented algorithm and theorems quantified over derivations apply to it;
  `produced` is then exactly `TPfun Inh M q`, one round of `q`'s equation
  against the snapshot.
- **Return values.** The pseudocode returns `approx[q]`; in relational form
  the caller reads it off the exit state, which is why the judgment carries
  states rather than values.
-/

set_option warningAsError true

namespace InheritanceCalculus

variable {Label : Type*}

/-- The tabling state of Algorithm alg:tabled: the accumulator `approx`, the
per-round memo `cache`, the call `stack`, and the round's `changed` flag. -/
structure TState (Label : Type*) where
  approx : QAMap Label
  cache : Set (Query Label)
  stack : Set (Query Label)
  changed : Prop

/-- Merge a produced set into the accumulator at one query
(`approx[q] ← approx[q] ∪ produced`); other coordinates are unchanged. -/
def mergeAt (A : QAMap Label) (q : Query Label) (P : Set (Ans q)) :
    QAMap Label :=
  fun q' => A q' ∪ {x | ∃ h : q' = q, h ▸ x ∈ P}

theorem mergeAt_self (A : QAMap Label) (q : Query Label) (P : Set (Ans q)) :
    mergeAt A q P q = A q ∪ P := by
  ext x
  constructor
  · rintro (hx | ⟨h, hx⟩)
    · exact Or.inl hx
    · exact Or.inr hx
  · rintro (hx | hx)
    · exact Or.inl hx
    · exact Or.inr ⟨rfl, hx⟩

theorem mergeAt_of_ne (A : QAMap Label) {q q' : Query Label}
    (P : Set (Ans q)) (h : q' ≠ q) : mergeAt A q P q' = A q' := by
  ext x
  constructor
  · rintro (hx | ⟨heq, _⟩)
    · exact hx
    · exact absurd heq h
  · exact fun hx => Or.inl hx

theorem le_mergeAt (A : QAMap Label) (q : Query Label) (P : Set (Ans q)) :
    A ≤ mergeAt A q P :=
  fun _ _ hx => Or.inl hx

variable (Inh : Path Label → Option (Set (Reference Label)))

/-- The two judgment forms of the big-step semantics: `resolve s q s'` is one
`Resolve(q)` call from state `s` exiting in state `s'`, and `calls s s'` is a
finite sequence of `Resolve` calls (the sub-query reads performed while
evaluating one right-hand side). -/
inductive RunGoal (Label : Type*) where
  | resolve (s : TState Label) (q : Query Label) (sExit : TState Label)
  | calls (s sExit : TState Label)

/-- Big-step semantics of `Resolve` (Algorithm alg:tabled, inner function).
The three `resolve` constructors are the pseudocode's three branches in
order; `callsNil`/`callsCons` sequence the sub-calls of a production. -/
inductive Run : RunGoal Label → Prop where
  /-- `q ∈ cache`: recomputed this round; return `approx[q]`, no state
  change. -/
  | cached {s : TState Label} {q : Query Label} (h : q ∈ s.cache) :
      Run (.resolve s q s)
  /-- `q ∈ stack`: re-entry, a cycle in the dependency graph; return the
  running approximation `approx[q]`, no state change. -/
  | reentry {s : TState Label} {q : Query Label} (hc : q ∉ s.cache)
      (hs : q ∈ s.stack) : Run (.resolve s q s)
  /-- Fresh computation: push `q`, perform the sub-calls, produce one round of
  `q`'s equation against a read snapshot `M` (bounded as in the module
  docstring), set `changed` if the production is not already contained in
  `approx[q]`, merge, pop `q`, and memoize it. -/
  | compute {s s₁ : TState Label} {q : Query Label} {M : QAMap Label}
      (hc : q ∉ s.cache) (hs : q ∉ s.stack)
      (hcalls : Run (.calls { s with stack := insert q s.stack } s₁))
      (hlb : QAMap.restrict (s₁.cache ∪ s₁.stack) s.approx ≤ M)
      (hub : M ≤ QAMap.restrict (s₁.cache ∪ s₁.stack) s₁.approx)
      (hcover : Reads Inh M q ⊆ s₁.cache ∪ s₁.stack) :
      Run (.resolve s q
        { approx := mergeAt s₁.approx q (TPfun Inh M q)
          cache := insert q s₁.cache
          stack := s₁.stack \ {q}
          changed := s₁.changed ∨ ¬ TPfun Inh M q ⊆ s₁.approx q })
  /-- No further sub-call. -/
  | callsNil (s : TState Label) : Run (.calls s s)
  /-- One sub-call, then the rest. -/
  | callsCons {s s' s'' : TState Label} {q' : Query Label}
      (hhead : Run (.resolve s q' s')) (htail : Run (.calls s' s'')) :
      Run (.calls s s'')

/-- The outer repeat-until-stable loop of `Tabled(q₀)`, from a given
accumulator: each round starts with an empty `cache` and `stack` and a clear
`changed` flag, resolves `q₀`, and either returns the accumulator (stable
round) or repeats from the grown accumulator. -/
inductive Rounds (q₀ : Query Label) : QAMap Label → QAMap Label → Prop where
  /-- The round added no fact: return the accumulator. -/
  | stable {A : QAMap Label} {sExit : TState Label}
      (hrun : Run Inh (.resolve ⟨A, ∅, ∅, False⟩ q₀ sExit))
      (hstable : ¬ sExit.changed) :
      Rounds q₀ A sExit.approx
  /-- The round added a fact: iterate. -/
  | unstable {A final : QAMap Label} {sExit : TState Label}
      (hrun : Run Inh (.resolve ⟨A, ∅, ∅, False⟩ q₀ sExit))
      (hchanged : sExit.changed)
      (hrest : Rounds q₀ sExit.approx final) :
      Rounds q₀ A final

/-- Algorithm alg:tabled, entry point: `Tabled(q₀)` iterates from the empty
accumulator and returns `final q₀` for the stable accumulator `final`. A
non-stabilizing run has no derivation, hence no returned answer
(thm:tabling-soundness (4)). -/
def Tabled (q₀ : Query Label) (final : QAMap Label) : Prop :=
  Rounds Inh q₀ ⊥ final

/-! ## Basic invariants of a run

thm:tabling-soundness (2) at the algorithm level: along any run, the
accumulator only grows (every assignment is a merge through set union), the
round memo only grows, and the `changed` flag is never cleared within a
round. -/

/-- Match-motive for the growth invariants of `run_growth`. -/
def growthMotive : RunGoal Label → Prop
  | .resolve s _ sExit =>
      s.approx ≤ sExit.approx ∧ s.cache ⊆ sExit.cache ∧
        (s.changed → sExit.changed)
  | .calls s sExit =>
      s.approx ≤ sExit.approx ∧ s.cache ⊆ sExit.cache ∧
        (s.changed → sExit.changed)

theorem run_growth {g : RunGoal Label} (h : Run Inh g) : growthMotive g := by
  induction h with
  | cached _ => exact ⟨le_rfl, Set.Subset.rfl, id⟩
  | reentry _ _ => exact ⟨le_rfl, Set.Subset.rfl, id⟩
  | compute _ _ _ _ _ _ ih =>
      obtain ⟨happrox, hcache, hchanged⟩ := ih
      exact ⟨happrox.trans (le_mergeAt _ _ _),
        hcache.trans (Set.subset_insert _ _),
        fun hch => Or.inl (hchanged hch)⟩
  | callsNil _ => exact ⟨le_rfl, Set.Subset.rfl, id⟩
  | callsCons _ _ ihHead ihTail =>
      obtain ⟨ha₁, hc₁, hch₁⟩ := ihHead
      obtain ⟨ha₂, hc₂, hch₂⟩ := ihTail
      exact ⟨ha₁.trans ha₂, hc₁.trans hc₂, fun hch => hch₂ (hch₁ hch)⟩

/-- thm:tabling-soundness (2), `approx` component: the accumulator only grows
across a `Resolve` call. -/
theorem run_approx_mono {s sExit : TState Label} {q : Query Label}
    (h : Run Inh (.resolve s q sExit)) : s.approx ≤ sExit.approx :=
  (run_growth Inh h).1

/-- The accumulator only grows across the rounds of the outer loop. -/
theorem rounds_le {q₀ : Query Label} {A final : QAMap Label}
    (h : Rounds Inh q₀ A final) : A ≤ final := by
  induction h with
  | stable hrun _ => exact run_approx_mono Inh hrun
  | unstable hrun _ _ ih => exact (run_approx_mono Inh hrun).trans ih

end InheritanceCalculus
