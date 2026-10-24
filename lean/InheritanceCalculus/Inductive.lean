import InheritanceCalculus.Basic

/-!
# The five semantic functions as an inductive family

This module renders the paper's five mutually recursive semantic equations
(eq:supers, eq:overrides, eq:bases, eq:resolve, eq:this; tex lines ~1320–1516)
as a single indexed inductive predicate `Fact`, whose index type `Atom` fuses a
semantic-function query with one candidate answer. An inductive predicate in
Lean *is* the least fixed point of its rules, so this definition is the
denotational semantics `lfp(T_P)` of the paper's Theorem "Well-definedness"
(thm:well-defined); the explicit `T_P` operator and the equality with this
family are established in `Lattice.lean` and `WellDefinedness.lean`.

## Encoding notes

- **Reversed path representation.** Per the convention of `Basic.lean`, paths
  are stored innermost-label-first, so the paper's `p ⌢ ℓ` is `ℓ :: p` and
  `init` is the tail. Every clause of the equations decomposes a path at its
  innermost label, so the decomposition is a constructor pattern: the
  partiality guards (`≠ []` plus `dropLast`) that a paper-order encoding needs
  at every `init` disappear into pattern matching, and `cases` unifies the
  indices directly, with no hand-rolled inversion motives.
- **Fused index instead of a `mutual` block.** A five-member `mutual inductive`
  family has exactly the same least-fixed-point semantics, but its mutual
  recursor is unwieldy; fusing the five coordinates into one index type `Atom`
  gives a single ordinary inductive with nine constructors (one per clause of
  the paper's equations), for which `cases` and `induction` work directly. The
  five semantic functions are recovered as abbreviations (`Supers`, …).
- **`BasesStar` is a coordinate of the derivation system, not of the paper's
  query set.** The paper's eq:supers uses the reflexive-transitive closure
  `bases*`; per Definition "Immediate consequence operator" (convention (a),
  tex line ~3600) that closure is *assembled* from the `bases` answers rather
  than being an independent query. Here the chain is inlined as the `basesStar`
  atom (`Relation.ReflTransGen` cannot mention a predicate still being
  defined); `basesStar_iff_reflTransGen` below discharges the equivalence, and
  the lattice layer (`Lattice.lean`) has no `basesStar` coordinate.
- **`this` is singleton-frontier.** Per the same definition (convention (b),
  tex line ~3603), the `this` equation is unfolded per singleton frontier by
  its additivity in the frontier; the set-frontier function is recovered as
  `thisSet`, with the paper's eq:this and the additivity equation proved as
  lemmas (`thisSet_zero`, `thisSet_succ`, `thisSet_union`).
- **The omission convention is the pattern shape.** The paper's set
  comprehensions silently omit a term when an inner partial function (`init`)
  is undefined on it (tex line ~3339). Here a clause that reads `init(p)`
  requires `p` in the pattern shape `ℓ :: p'`, so the root is excluded by
  non-unification rather than by a guard. Omitting the shape requirement on
  the base path in `supersStep` would, for example, inject the root's
  reflexive pair into every `supers` set reachable through a root-valued base,
  exactly the "ghost" defect the convention exists to exclude.
-/

set_option warningAsError true

namespace InheritanceCalculus

variable {Label : Type*}

/-- A semantic-function query fused with one candidate single answer: the
elements of the paper's `V_q` tagged by their query `q` (Definition
"Immediate consequence operator", tex line ~3576). A `supers` answer is a
pair (inheritance site, override); every other answer is a path. -/
inductive Atom (Label : Type*) where
  | supers (q site override : Path Label)
  | overrides (q override : Path Label)
  | bases (q target : Path Label)
  | basesStar (q target : Path Label)
  | this (source pdef : Path Label) (n : ℕ) (target : Path Label)

/-- Derivability of a semantic fact from the five equations, as an inductive
predicate: the least relation closed under the clauses of eq:supers–eq:this.
Being an inductive predicate, `Fact Inh` *is* the least fixed point of the
paper's monotone operator `T_P` (proved as `lfp_TP_eq_toQAMap` in
`WellDefinedness.lean`). Paths follow the reversed representation of
`Basic.lean`: `ℓ :: p` is the paper's `p ⌢ ℓ`. -/
inductive Fact (Inh : Path Label → Option (Set (Reference Label))) : Atom Label → Prop where
  /-- eq:supers, root clause: `supers(()) = {((), ())}`. -/
  | supersRoot : Fact Inh (.supers [] [] [])
  /-- eq:supers, comprehension clause: `p_base ∈ bases*(q)`,
  `p_override ∈ overrides(p_base)` produce the pair
  `(init(p_base), p_override)`. The pattern `ℓb :: site` on the base path is
  the partiality of `init` under the omission convention. -/
  | supersStep {ℓq : Label} {q : Path Label} {ℓb : Label} {site pov : Path Label}
      (hchain : Fact Inh (.basesStar (ℓq :: q) (ℓb :: site)))
      (hov : Fact Inh (.overrides (ℓb :: site) pov)) :
      Fact Inh (.supers (ℓq :: q) site pov)
  /-- eq:overrides, root clause: `overrides(()) = {()}`. -/
  | overridesRoot : Fact Inh (.overrides [] [])
  /-- eq:overrides, reflexive alternative: the branch qualifies
  (`p_branch ⌢ ℓ ∈ dom(inherits)`) and the path itself is the override. -/
  | overridesSelf {p c pbr : Path Label} {ℓ : Label}
      (hsup : Fact Inh (.supers p c pbr)) (hdom : (ℓ :: pbr) ∈ Dom Inh) :
      Fact Inh (.overrides (ℓ :: p) (ℓ :: p))
  /-- eq:overrides, branch alternative: the qualifying branch's own snoc is the
  override. -/
  | overridesBranch {p c pbr : Path Label} {ℓ : Label}
      (hsup : Fact Inh (.supers p c pbr)) (hdom : (ℓ :: pbr) ∈ Dom Inh) :
      Fact Inh (.overrides (ℓ :: p) (ℓ :: pbr))
  /-- eq:bases (with eq:resolve inlined; `resolveSet_cons` folds it back):
  a reference `(n, w)` written at an override of `p ⌢ ℓ` resolves through
  `this({p}, init(p_override), n)` and projects `w` downward. There is no root
  clause: `bases(()) = ∅` holds by inversion (`basesSet_nil`). -/
  | basesStep {p pcur : Path Label} {ℓ ℓov : Label} {povt : Path Label}
      {n : ℕ} {w : List Label}
      (hov : Fact Inh (.overrides (ℓ :: p) (ℓov :: povt)))
      (href : MemRef Inh (n, w) (ℓov :: povt))
      (hthis : Fact Inh (.this p povt n pcur)) :
      Fact Inh (.bases (ℓ :: p) (w ++ pcur))
  /-- `bases*`: reflexivity. -/
  | basesStarRefl (q : Path Label) : Fact Inh (.basesStar q q)
  /-- `bases*`: transitivity, one `bases` hop at the tail. -/
  | basesStarTail {q r s : Path Label} (hchain : Fact Inh (.basesStar q r))
      (hstep : Fact Inh (.bases r s)) : Fact Inh (.basesStar q s)
  /-- eq:this, `n = 0` clause: the frontier is returned as is. -/
  | thisZero (s pdef : Path Label) : Fact Inh (.this s pdef 0 s)
  /-- eq:this, `n > 0` clause at a singleton frontier: pass to the supers pairs
  whose override component matches `p_def`, shortening `p_def` by one label. -/
  | thisSucc {s psite t : Path Label} {ℓd : Label} {pd : Path Label} {n : ℕ}
      (hsup : Fact Inh (.supers s psite (ℓd :: pd)))
      (hrec : Fact Inh (.this psite pd n t)) :
      Fact Inh (.this s (ℓd :: pd) (n + 1) t)

variable (Inh : Path Label → Option (Set (Reference Label)))

/-- The paper's `supers` (eq:supers) as a ternary relation:
`Supers Inh q site override` renders `(site, override) ∈ supers(q)`. -/
abbrev Supers (q site override : Path Label) : Prop :=
  Fact Inh (.supers q site override)

/-- The paper's `overrides` (eq:overrides): `Overrides Inh q pov` renders
`pov ∈ overrides(q)`. -/
abbrev Overrides (q pov : Path Label) : Prop := Fact Inh (.overrides q pov)

/-- The paper's `bases` (eq:bases): `Bases Inh q t` renders `t ∈ bases(q)`. -/
abbrev Bases (q t : Path Label) : Prop := Fact Inh (.bases q t)

/-- The reflexive-transitive closure `bases*` used by eq:supers, inlined as a
derivation-system coordinate; see `basesStar_iff_reflTransGen`. -/
abbrev BasesStar (q t : Path Label) : Prop := Fact Inh (.basesStar q t)

/-- The paper's `this` (eq:this) at a singleton frontier:
`This Inh s pdef n t` renders `t ∈ this({s}, pdef, n)`. -/
abbrev This (s pdef : Path Label) (n : ℕ) (t : Path Label) : Prop :=
  Fact Inh (.this s pdef n t)

/-- The paper's `resolve` (eq:resolve): non-recursive on top of `This`. The
head/tail decomposition of `pdef` renders the partiality of `init(p_def)`
under the omission convention. -/
def Resolve (psite pdef : Path Label) (n : ℕ) (w : List Label)
    (t : Path Label) : Prop :=
  ∃ ℓd pd, pdef = ℓd :: pd ∧ ∃ pcur, This Inh psite pd n pcur ∧ t = w ++ pcur

/-! ## Set-valued wrappers -/

/-- `supers(q)` as a set of (inheritance site, override) pairs
(eq:supers-signature, tex line ~1273). -/
def supersSet (q : Path Label) : Set (Path Label × Path Label) :=
  {x | Supers Inh q x.1 x.2}

/-- `overrides(q)` as a set of paths. -/
def overridesSet (q : Path Label) : Set (Path Label) := {pov | Overrides Inh q pov}

/-- `bases(q)` as a set of paths. -/
def basesSet (q : Path Label) : Set (Path Label) := {t | Bases Inh q t}

/-- `resolve(p_site, p_def, n, w)` as a set of paths. -/
def resolveSet (psite pdef : Path Label) (n : ℕ) (w : List Label) :
    Set (Path Label) :=
  {t | Resolve Inh psite pdef n w t}

/-- `this({s}, pdef, n)` as a set of paths (singleton frontier). -/
def thisSingleSet (s pdef : Path Label) (n : ℕ) : Set (Path Label) :=
  {t | This Inh s pdef n t}

/-- `this(S, pdef, n)` at a general frontier `S`: the union of the singleton
values, which is forced by the additivity of eq:this in the frontier
(Definition "Immediate consequence operator", convention (b)). The paper's
eq:this for this function is `thisSet_zero`/`thisSet_succ`/`thisSet_nil_succ`,
and additivity is `thisSet_union`. -/
def thisSet (S : Set (Path Label)) (pdef : Path Label) (n : ℕ) :
    Set (Path Label) :=
  ⋃ s ∈ S, thisSingleSet Inh s pdef n

/-! ## Membership characterizations (the five equations, pointwise)

With constructor-form indices, each characterization is one `cases`; no
inversion motives are needed. -/

theorem supers_nil_iff {c pov : Path Label} :
    Supers Inh [] c pov ↔ c = [] ∧ pov = [] := by
  constructor
  · intro h
    cases h with
    | supersRoot => exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact Fact.supersRoot

theorem supers_cons_iff {ℓq : Label} {q c pov : Path Label} :
    Supers Inh (ℓq :: q) c pov ↔
      ∃ ℓb, BasesStar Inh (ℓq :: q) (ℓb :: c) ∧ Overrides Inh (ℓb :: c) pov := by
  constructor
  · intro h
    cases h with
    | supersStep hchain hov => exact ⟨_, hchain, hov⟩
  · rintro ⟨ℓb, hchain, hov⟩
    exact Fact.supersStep hchain hov

theorem overrides_nil_iff {pov : Path Label} :
    Overrides Inh [] pov ↔ pov = [] := by
  constructor
  · intro h
    cases h with
    | overridesRoot => rfl
  · rintro rfl
    exact Fact.overridesRoot

theorem overrides_cons_iff {p : Path Label} {ℓ : Label} {pov : Path Label} :
    Overrides Inh (ℓ :: p) pov ↔
      ∃ c pbr, Supers Inh p c pbr ∧ (ℓ :: pbr) ∈ Dom Inh ∧
        (pov = ℓ :: p ∨ pov = ℓ :: pbr) := by
  constructor
  · intro h
    cases h with
    | overridesSelf hsup hdom => exact ⟨_, _, hsup, hdom, Or.inl rfl⟩
    | overridesBranch hsup hdom => exact ⟨_, _, hsup, hdom, Or.inr rfl⟩
  · rintro ⟨c, pbr, hsup, hdom, (rfl | rfl)⟩
    · exact Fact.overridesSelf hsup hdom
    · exact Fact.overridesBranch hsup hdom

/-- eq:bases has no root clause, so nothing is a base of the root. -/
theorem not_bases_nil {t : Path Label} : ¬ Bases Inh [] t := by
  intro h
  cases h

theorem bases_cons_iff {p : Path Label} {ℓ : Label} {t : Path Label} :
    Bases Inh (ℓ :: p) t ↔
      ∃ pov, Overrides Inh (ℓ :: p) pov ∧
        ∃ n w, MemRef Inh (n, w) pov ∧ Resolve Inh p pov n w t := by
  constructor
  · intro h
    cases h with
    | basesStep hov href hthis =>
        exact ⟨_, hov, _, _, href, _, _, rfl, _, hthis, rfl⟩
  · rintro ⟨pov, hov, n, w, href, ℓov, povt, rfl, pcur, hthis, rfl⟩
    exact Fact.basesStep hov href hthis

theorem this_zero_iff {s pdef t : Path Label} :
    This Inh s pdef 0 t ↔ t = s := by
  constructor
  · intro h
    cases h with
    | thisZero => rfl
  · rintro rfl
    exact Fact.thisZero _ _

theorem this_succ_nil_iff {s t : Path Label} {n : ℕ} :
    ¬ This Inh s [] (n + 1) t := by
  intro h
  cases h

theorem this_succ_iff {s t : Path Label} {ℓd : Label} {pd : Path Label}
    {n : ℕ} :
    This Inh s (ℓd :: pd) (n + 1) t ↔
      ∃ psite, Supers Inh s psite (ℓd :: pd) ∧ This Inh psite pd n t := by
  constructor
  · intro h
    cases h with
    | thisSucc hsup hrec => exact ⟨_, hsup, hrec⟩
  · rintro ⟨psite, hsup, hrec⟩
    exact Fact.thisSucc hsup hrec

/-! ## `bases*` is the reflexive-transitive closure of `bases` -/

/-- Match-motive extracting a `Relation.ReflTransGen` chain from a `basesStar`
fact (an induction over `Fact` still needs a motive on all of `Atom`). -/
def rtgMotive : Atom Label → Prop
  | .basesStar q t => Relation.ReflTransGen (Bases Inh) q t
  | _ => True

theorem basesStar_iff_reflTransGen {q t : Path Label} :
    BasesStar Inh q t ↔ Relation.ReflTransGen (Bases Inh) q t := by
  constructor
  · intro h
    have aux : ∀ {a : Atom Label}, Fact Inh a → rtgMotive Inh a := by
      intro a ha
      induction ha with
      | supersRoot => trivial
      | supersStep _ _ _ _ => trivial
      | overridesRoot => trivial
      | overridesSelf _ _ _ => trivial
      | overridesBranch _ _ _ => trivial
      | basesStep _ _ _ _ _ => trivial
      | basesStarRefl _ => exact Relation.ReflTransGen.refl
      | basesStarTail _ hstep ih _ => exact Relation.ReflTransGen.tail ih hstep
      | thisZero _ _ => trivial
      | thisSucc _ _ _ _ => trivial
    exact aux h
  · intro h
    induction h with
    | refl => exact Fact.basesStarRefl q
    | tail _ hstep ih => exact Fact.basesStarTail ih hstep

/-- A `bases*` chain starting at the root never leaves it, since
`bases(()) = ∅`. -/
theorem basesStar_nil {pb : Path Label} (h : BasesStar Inh [] pb) : pb = [] := by
  have h' := (basesStar_iff_reflTransGen Inh).mp h
  clear h
  induction h' with
  | refl => rfl
  | tail _ hstep ih =>
      subst ih
      exact absurd hstep (not_bases_nil Inh)

/-! ## The five equations, set-valued (paper-verbatim forms) -/

/-- eq:supers, root case: `supers(()) = {((), ())}`. -/
theorem supersSet_nil :
    supersSet Inh [] = {(([] : Path Label), ([] : Path Label))} := by
  ext ⟨c, pov⟩
  simp [supersSet, supers_nil_iff Inh, Prod.ext_iff]

/-- eq:supers at `p ⌢ ℓ`, verbatim. -/
theorem supersSet_cons (ℓq : Label) (q : Path Label) :
    supersSet Inh (ℓq :: q) =
      {x | ∃ ℓb, BasesStar Inh (ℓq :: q) (ℓb :: x.1) ∧
        Overrides Inh (ℓb :: x.1) x.2} := by
  ext ⟨c, pov⟩
  simp [supersSet, supers_cons_iff Inh]

/-- eq:overrides, root case: `overrides(()) = {()}`. -/
theorem overridesSet_nil : overridesSet Inh [] = {([] : Path Label)} := by
  ext pov
  simp [overridesSet, overrides_nil_iff Inh]

/-- eq:overrides at `p ⌢ ℓ`, verbatim: the branches are the override
components of `supers(p)` whose snoc is written, and the produced overrides
are the path itself alongside each qualifying branch's snoc. -/
theorem overridesSet_cons (p : Path Label) (ℓ : Label) :
    overridesSet Inh (ℓ :: p) =
      {pov | ∃ c pbr, Supers Inh p c pbr ∧ (ℓ :: pbr) ∈ Dom Inh ∧
        (pov = ℓ :: p ∨ pov = ℓ :: pbr)} := by
  ext pov
  simp only [overridesSet, Set.mem_setOf_eq]
  exact overrides_cons_iff Inh

/-- eq:bases, root case: `bases(()) = ∅`. -/
theorem basesSet_nil : basesSet Inh [] = ∅ := by
  ext t
  simp [basesSet, not_bases_nil Inh]

/-- eq:bases at `p ⌢ ℓ`, verbatim (with `resolve` folded as `resolveSet`). -/
theorem basesSet_cons (p : Path Label) (ℓ : Label) :
    basesSet Inh (ℓ :: p) =
      {t | ∃ pov, Overrides Inh (ℓ :: p) pov ∧
        ∃ n w, MemRef Inh (n, w) pov ∧ t ∈ resolveSet Inh p pov n w} := by
  ext t
  simp only [basesSet, Set.mem_setOf_eq]
  exact bases_cons_iff Inh

/-- eq:resolve, defined case: projecting `w` downward from
`this({p_site}, init(p_def), n)`. -/
theorem resolveSet_cons (psite : Path Label) (ℓd : Label) (pd : Path Label)
    (n : ℕ) (w : List Label) :
    resolveSet Inh psite (ℓd :: pd) n w =
      (w ++ ·) '' thisSingleSet Inh psite pd n := by
  ext t
  constructor
  · rintro ⟨ℓd', pd', heq, pcur, hthis, rfl⟩
    obtain ⟨rfl, rfl⟩ : ℓd' = ℓd ∧ pd' = pd := by
      simpa using heq.symm
    exact ⟨pcur, hthis, rfl⟩
  · rintro ⟨pcur, hthis, rfl⟩
    exact ⟨ℓd, pd, rfl, pcur, hthis, rfl⟩

/-- eq:resolve, omitted case: `init(p_def)` is undefined on the root, so the
comprehension is empty. -/
theorem resolveSet_nil (psite : Path Label) (n : ℕ) (w : List Label) :
    resolveSet Inh psite [] n w = ∅ := by
  ext t
  simp [resolveSet, Resolve]

/-- The general frontier restricted to a singleton is the singleton value. -/
theorem thisSet_singleton (s pdef : Path Label) (n : ℕ) :
    thisSet Inh {s} pdef n = thisSingleSet Inh s pdef n := by
  simp [thisSet]

/-- eq:this, `n = 0` case: `this(S, p_def, 0) = S`. -/
theorem thisSet_zero (S : Set (Path Label)) (pdef : Path Label) :
    thisSet Inh S pdef 0 = S := by
  ext t
  simp [thisSet, thisSingleSet, this_zero_iff Inh]

/-- eq:this, `n > 0` case: pass through the matching supers pairs and recurse
at `init(p_def)`. -/
theorem thisSet_succ (S : Set (Path Label)) (ℓd : Label) (pd : Path Label)
    (n : ℕ) :
    thisSet Inh S (ℓd :: pd) (n + 1) =
      thisSet Inh {psite | ∃ s ∈ S, Supers Inh s psite (ℓd :: pd)} pd n := by
  ext t
  simp only [thisSet, thisSingleSet, Set.mem_iUnion, Set.mem_setOf_eq,
    exists_prop, this_succ_iff Inh]
  constructor
  · rintro ⟨s, hs, psite, hsup, hthis⟩
    exact ⟨psite, ⟨s, hs, hsup⟩, hthis⟩
  · rintro ⟨psite, ⟨s, hs, hsup⟩, hthis⟩
    exact ⟨s, hs, psite, hsup, hthis⟩

/-- eq:this, omitted case: at `n > 0` the recursion reads `init(p_def)`,
undefined on the root, so the value is empty. -/
theorem thisSet_nil_succ (S : Set (Path Label)) (n : ℕ) :
    thisSet Inh S [] (n + 1) = ∅ := by
  ext t
  simp [thisSet, thisSingleSet, this_succ_nil_iff Inh]

/-- Additivity of `this` in the frontier (Definition "Immediate consequence
operator", convention (b)): definitional under the union encoding; the
induction content of the paper's proof lives in `thisSet_succ`. -/
theorem thisSet_union (S₁ S₂ : Set (Path Label)) (pdef : Path Label) (n : ℕ) :
    thisSet Inh (S₁ ∪ S₂) pdef n = thisSet Inh S₁ pdef n ∪ thisSet Inh S₂ pdef n :=
  Set.biUnion_union S₁ S₂ _

/-! ## Further inversion corollaries -/

/-- A non-root override is itself non-root (both alternatives of
eq:overrides end in `ℓ`). -/
theorem Overrides.ne_nil {ℓ : Label} {p pov : Path Label}
    (h : Overrides Inh (ℓ :: p) pov) : pov ≠ [] := by
  cases h with
  | overridesSelf _ _ => simp
  | overridesBranch _ _ => simp

end InheritanceCalculus
