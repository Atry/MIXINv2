import InheritanceCalculus.Inductive

/-!
# The immediate consequence operator `T_P`

This module renders the paper's Definition "Immediate consequence operator
`T_P`" (def:tp-operator, tex line ~3542) and proves the Monotonicity lemma
(lem:monotonicity, tex line ~3625) and the Knaster–Tarski corollaries of
Theorem "Existence and uniqueness of `lfp(T_P)`" (thm:lfp-exists, tex
line ~3683).

- `Query` is the set `𝒬` of semantic-function queries and `Ans q` the value
  set `𝒱_q` of a single answer to `q`; a query–answer map (`QAMap`) is an
  element of the pointwise product `∏_{q ∈ 𝒬} 𝒫(𝒱_q)`, whose complete-lattice
  structure Lean provides instance-wise (paper: "Each powerset lattice is
  complete, so the pointwise product lattice is also complete").
- `TP` maps a query–answer map `M` to the map collecting, at each query, the
  values produced by all instances of the defining equation's comprehension,
  each sub-query fact interpreted through `M`.
- Per the paper's convention (a), the closure `bases*` in the `supers`
  coordinate is `Relation.ReflTransGen` of the relation assembled from the
  `bases` answers of `M`, not a coordinate of `M`.
- Per convention (b), the `this` coordinate carries singleton frontiers only.
  This is the one deliberate deviation from the vertex set of Definition
  "Dependency graph" (def:dependency-graph): general-frontier `this` vertices
  are determined by additivity as the union of their singletons, which the
  convention itself stipulates; the derived function `thisSet`
  (`Inductive.lean`) discharges the general-frontier reading of eq:this via
  `thisSet_zero`/`thisSet_succ`/`thisSet_nil_succ`/`thisSet_union`.
- Paths follow the reversed representation of `Basic.lean`: the paper's
  `p ⌢ ℓ` is `ℓ :: p`, and each coordinate's `init` reads are head/tail
  decompositions instead of `≠ []` guards with `dropLast`.
-/

set_option warningAsError true

namespace InheritanceCalculus

variable {Label : Type*}

/-- The queries `𝒬`: one constructor per semantic function, `this` at a
singleton frontier (module docstring, deviation note). -/
inductive Query (Label : Type*) where
  | supers (q : Path Label)
  | overrides (q : Path Label)
  | bases (q : Path Label)
  | resolve (site pdef : Path Label) (n : ℕ) (w : List Label)
  | this (source pdef : Path Label) (n : ℕ)

/-- The value set `𝒱_q` of a single answer to query `q`: pairs of paths
(inheritance site, override) for a `supers` query, paths for the rest. The
elements are never themselves sets; the set value of an equation is carried by
the whole answer set `M q`. -/
@[reducible]
def Ans : Query Label → Type _
  | .supers _ => Path Label × Path Label
  | .overrides _ => Path Label
  | .bases _ => Path Label
  | .resolve _ _ _ _ => Path Label
  | .this _ _ _ => Path Label

/-- Query–answer maps: the paper's pointwise product `∏_{q ∈ 𝒬} 𝒫(𝒱_q)`.
The complete-lattice structure is the instance-provided Pi-over-Set one. -/
abbrev QAMap (Label : Type*) := (q : Query Label) → Set (Ans q)

variable (Inh : Path Label → Option (Set (Reference Label)))

/-- The immediate consequence operator, as a plain function: at each query,
collect the productions of all instances of the corresponding equation's
comprehension, reading every bound sub-query fact through `M`. -/
def TPfun (M : QAMap Label) : QAMap Label
  | .supers q =>
      {x : Path Label × Path Label |
        (q = [] ∧ x = ([], [])) ∨
        (q ≠ [] ∧ ∃ ℓb,
          Relation.ReflTransGen (fun a b => b ∈ M (.bases a)) q (ℓb :: x.1) ∧
          x.2 ∈ M (.overrides (ℓb :: x.1)))}
  | .overrides q =>
      {pov : Path Label |
        (q = [] ∧ pov = []) ∨
        ∃ p ℓ c pbr, q = ℓ :: p ∧ (c, pbr) ∈ M (.supers p) ∧
          (ℓ :: pbr) ∈ Dom Inh ∧ (pov = ℓ :: p ∨ pov = ℓ :: pbr)}
  | .bases q =>
      {t : Path Label |
        ∃ p ℓ pov n w, q = ℓ :: p ∧ pov ∈ M (.overrides (ℓ :: p)) ∧
          MemRef Inh (n, w) pov ∧ t ∈ M (.resolve p pov n w)}
  | .resolve site pdef n w =>
      {t : Path Label |
        ∃ ℓd pd, pdef = ℓd :: pd ∧ ∃ pcur, pcur ∈ M (.this site pd n) ∧
          t = w ++ pcur}
  | .this s pdef n =>
      {t : Path Label |
        (n = 0 ∧ t = s) ∨
        ∃ m, n = m + 1 ∧ ∃ ℓd pd, pdef = ℓd :: pd ∧ ∃ psite,
          (psite, pdef) ∈ M (.supers s) ∧
          t ∈ M (.this psite pd m)}

/-- lem:monotonicity: every coordinate's production is a positive existential
collection of `M`-facts; the closure in the `supers` coordinate is monotone in
the relation it closes; the guards (`= []`, head/tail shapes, `∈ Dom Inh`,
`MemRef`) act on the fixed primitive `inherits`, not on sub-queries, so they
are constants of `T_P`. -/
theorem TPfun_mono : Monotone (TPfun Inh (Label := Label)) := by
  intro M M' hM q
  cases q with
  | supers q =>
      rintro x (⟨hq, hx⟩ | ⟨hq, ℓb, hchain, hov⟩)
      · exact Or.inl ⟨hq, hx⟩
      · exact Or.inr ⟨hq, ℓb,
          hchain.mono fun a b hb => hM (.bases a) hb,
          hM (.overrides (ℓb :: x.1)) hov⟩
  | overrides q =>
      rintro pov (⟨hq, hpov⟩ | ⟨p, ℓ, c, pbr, heq, hsup, hdom, hor⟩)
      · exact Or.inl ⟨hq, hpov⟩
      · exact Or.inr ⟨p, ℓ, c, pbr, heq, hM (.supers p) hsup, hdom, hor⟩
  | bases q =>
      rintro t ⟨p, ℓ, pov, n, w, heq, hov, href, ht⟩
      exact ⟨p, ℓ, pov, n, w, heq, hM (.overrides (ℓ :: p)) hov, href,
        hM (.resolve p pov n w) ht⟩
  | resolve site pdef n w =>
      rintro t ⟨ℓd, pd, heq, pcur, hthis, ht⟩
      exact ⟨ℓd, pd, heq, pcur, hM (.this site pd n) hthis, ht⟩
  | this s pdef n =>
      rintro t (⟨hn, ht⟩ | ⟨m, hn, ℓd, pd, heq, psite, hsup, ht⟩)
      · exact Or.inl ⟨hn, ht⟩
      · exact Or.inr ⟨m, hn, ℓd, pd, heq, psite, hM (.supers s) hsup,
          hM (.this psite pd m) ht⟩

/-- The immediate consequence operator as a monotone map on the complete
lattice of query–answer maps (def:tp-operator + lem:monotonicity). -/
def TP : QAMap Label →o QAMap Label := ⟨TPfun Inh, TPfun_mono Inh⟩

/-- thm:lfp-exists, existence: `lfp(T_P)` is a fixed point of `T_P`
(Knaster–Tarski on the complete pointwise product lattice). -/
theorem TP_map_lfp : TP Inh (OrderHom.lfp (TP Inh)) = OrderHom.lfp (TP Inh) :=
  OrderHom.map_lfp (TP Inh)

/-- thm:lfp-exists, uniqueness of the least fixed point: `lfp(T_P)` is the
least element of the set of fixed points of `T_P` (and the least element of a
set is unique). -/
theorem TP_isLeast_lfp :
    IsLeast (Function.fixedPoints (TP Inh)) (OrderHom.lfp (TP Inh)) :=
  OrderHom.isLeast_lfp (TP Inh)

end InheritanceCalculus
