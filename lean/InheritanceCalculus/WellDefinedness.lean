import InheritanceCalculus.Lattice

/-!
# Well-definedness: `lfp(T_P)` is the inductive family

This module proves the paper's Theorem "Well-definedness" (thm:well-defined,
tex line ~3717): the five semantic functions, i.e. the components of the
query–answer map `toQAMap` packaging the inductive family of
`Inductive.lean`, are exactly the components of `lfp(T_P)`, the unique least
fixed point of the immediate consequence operator.

The two inclusions are the two standard halves of Knaster–Tarski:

- `lfp(T_P) ≤ toQAMap` because `toQAMap` is a pre-fixed point of `T_P`
  (`TP_toQAMap_le`): every production instance over the inductive family is
  itself derivable by the corresponding constructor.
- `toQAMap ≤ lfp(T_P)` by induction on derivations (`fact_mem_lfp`): each
  constructor's conclusion is one production of `T_P` over `lfp(T_P)` itself,
  entered through `T_P(lfp(T_P)) = lfp(T_P)`.
-/

set_option warningAsError true

namespace InheritanceCalculus

variable {Label : Type*} (Inh : Path Label → Option (Set (Reference Label)))

/-- The inductive family of `Inductive.lean`, packaged as a query–answer map:
its components are the five semantic functions. -/
def toQAMap : QAMap Label
  | .supers p => supersSet Inh p
  | .overrides p => overridesSet Inh p
  | .bases p => basesSet Inh p
  | .resolve site pdef n w => resolveSet Inh site pdef n w
  | .this s pdef n => thisSingleSet Inh s pdef n

/-- Entering the least fixed point through one `T_P` production step
(`T_P(lfp(T_P)) = lfp(T_P)`, the Knaster–Tarski fixed-point equation). -/
theorem mem_lfp_of_mem_TP {q : Query Label} {x : Ans q}
    (h : x ∈ TP Inh (OrderHom.lfp (TP Inh)) q) :
    x ∈ OrderHom.lfp (TP Inh) q := by
  rw [TP_map_lfp Inh] at h
  exact h

/-- Match-motive for the derivation induction of `fact_mem_lfp`: each
coordinate of the inductive family lands in the corresponding coordinate of
`lfp(T_P)`; a `basesStar` derivation lands in the closure that the `supers`
coordinate of `T_P` assembles from the `bases` answers of `lfp(T_P)`. -/
def lfpMotive : Atom Label → Prop
  | .supers q site ov => (site, ov) ∈ OrderHom.lfp (TP Inh) (.supers q)
  | .overrides q ov => ov ∈ OrderHom.lfp (TP Inh) (.overrides q)
  | .bases q t => t ∈ OrderHom.lfp (TP Inh) (.bases q)
  | .basesStar q t =>
      Relation.ReflTransGen
        (fun a b => b ∈ OrderHom.lfp (TP Inh) (.bases a)) q t
  | .this s pdef n t => t ∈ OrderHom.lfp (TP Inh) (.this s pdef n)

/-- Induction on derivations: every fact of the inductive family belongs to
`lfp(T_P)` (the `toQAMap ≤ lfp(T_P)` half of thm:well-defined). -/
theorem fact_mem_lfp {a : Atom Label} (h : Fact Inh a) : lfpMotive Inh a := by
  induction h with
  | supersRoot =>
      exact mem_lfp_of_mem_TP Inh (Or.inl ⟨rfl, rfl⟩)
  | supersStep _ _ ihchain ihov =>
      exact mem_lfp_of_mem_TP Inh
        (Or.inr ⟨List.cons_ne_nil _ _, _, ihchain, ihov⟩)
  | overridesRoot =>
      exact mem_lfp_of_mem_TP Inh (Or.inl ⟨rfl, rfl⟩)
  | overridesSelf _ hdom ihsup =>
      exact mem_lfp_of_mem_TP Inh
        (Or.inr ⟨_, _, _, _, rfl, ihsup, hdom, Or.inl rfl⟩)
  | overridesBranch _ hdom ihsup =>
      exact mem_lfp_of_mem_TP Inh
        (Or.inr ⟨_, _, _, _, rfl, ihsup, hdom, Or.inr rfl⟩)
  | basesStep _ href _ ihov ihthis =>
      refine mem_lfp_of_mem_TP Inh ⟨_, _, _, _, _, rfl, ihov, href, ?_⟩
      exact mem_lfp_of_mem_TP Inh ⟨_, _, rfl, _, ihthis, rfl⟩
  | basesStarRefl _ =>
      exact Relation.ReflTransGen.refl
  | basesStarTail _ _ ihchain ihstep =>
      exact Relation.ReflTransGen.tail ihchain ihstep
  | thisZero _ _ =>
      exact mem_lfp_of_mem_TP Inh (Or.inl ⟨rfl, rfl⟩)
  | thisSucc _ _ ihsup ihthis =>
      exact mem_lfp_of_mem_TP Inh
        (Or.inr ⟨_, rfl, _, _, rfl, _, ihsup, ihthis⟩)

/-- `toQAMap` is a pre-fixed point of `T_P`: every production instance over
the inductive family is derivable by the corresponding constructor (the
`lfp(T_P) ≤ toQAMap` half of thm:well-defined, through Knaster–Tarski). -/
theorem TP_toQAMap_le : TP Inh (toQAMap Inh) ≤ toQAMap Inh := by
  intro q
  cases q with
  | supers q =>
      rintro x (⟨rfl, rfl⟩ | ⟨hq, ℓb, hchain, hov⟩)
      · exact Fact.supersRoot
      · obtain ⟨ℓq, q', rfl⟩ : ∃ ℓq q', q = ℓq :: q' := by
          cases q with
          | nil => exact absurd rfl hq
          | cons a l => exact ⟨a, l, rfl⟩
        exact Fact.supersStep ((basesStar_iff_reflTransGen Inh).mpr hchain) hov
  | overrides q =>
      rintro pov (⟨rfl, rfl⟩ | ⟨p, ℓ, c, pbr, rfl, hsup, hdom, (rfl | rfl)⟩)
      · exact Fact.overridesRoot
      · exact Fact.overridesSelf hsup hdom
      · exact Fact.overridesBranch hsup hdom
  | bases q =>
      rintro t ⟨p, ℓ, pov, n, w, rfl, hov, href, ℓov, povt, rfl, pcur, hthis, rfl⟩
      exact Fact.basesStep hov href hthis
  | resolve site pdef n w =>
      rintro t ⟨ℓd, pd, rfl, pcur, hthis, rfl⟩
      exact ⟨ℓd, pd, rfl, pcur, hthis, rfl⟩
  | this s pdef n =>
      rintro t (⟨hn, ht⟩ | ⟨m, hn, ℓd, pd, rfl, psite, hsup, hthis⟩)
      · rw [hn, ht]
        exact Fact.thisZero _ _
      · rw [hn]
        exact Fact.thisSucc hsup hthis

/-- The other inclusion, assembled from the derivation induction; the
`resolve` coordinate, which has no `Fact` constructor of its own (eq:resolve
is non-recursive), enters through one `T_P` step. -/
theorem toQAMap_le_lfp : toQAMap Inh ≤ OrderHom.lfp (TP Inh) := by
  intro q
  cases q with
  | supers p => exact fun x hx => fact_mem_lfp Inh hx
  | overrides p => exact fun pov hpov => fact_mem_lfp Inh hpov
  | bases p => exact fun t ht => fact_mem_lfp Inh ht
  | resolve site pdef n w =>
      rintro t ⟨ℓd, pd, rfl, pcur, hthis, rfl⟩
      exact mem_lfp_of_mem_TP Inh ⟨ℓd, pd, rfl, pcur, fact_mem_lfp Inh hthis, rfl⟩
  | this s pdef n => exact fun t ht => fact_mem_lfp Inh ht

/-- thm:well-defined: the semantic functions are well-defined; their
denotational semantics is `lfp(T_P)`, the unique least fixed point of the
immediate consequence operator, and it coincides with the inductive family of
`Inductive.lean`. -/
theorem lfp_TP_eq_toQAMap : OrderHom.lfp (TP Inh) = toQAMap Inh :=
  le_antisymm (OrderHom.lfp_le (TP Inh) (TP_toQAMap_le Inh))
    (toQAMap_le_lfp Inh)

/-- thm:well-defined, `supers` component. -/
theorem lfp_TP_supers (p : Path Label) :
    OrderHom.lfp (TP Inh) (.supers p) = supersSet Inh p := by
  rw [lfp_TP_eq_toQAMap]; rfl

/-- thm:well-defined, `overrides` component. -/
theorem lfp_TP_overrides (p : Path Label) :
    OrderHom.lfp (TP Inh) (.overrides p) = overridesSet Inh p := by
  rw [lfp_TP_eq_toQAMap]; rfl

/-- thm:well-defined, `bases` component. -/
theorem lfp_TP_bases (p : Path Label) :
    OrderHom.lfp (TP Inh) (.bases p) = basesSet Inh p := by
  rw [lfp_TP_eq_toQAMap]; rfl

/-- thm:well-defined, `resolve` component. -/
theorem lfp_TP_resolve (site pdef : Path Label) (n : ℕ) (w : List Label) :
    OrderHom.lfp (TP Inh) (.resolve site pdef n w) =
      resolveSet Inh site pdef n w := by
  rw [lfp_TP_eq_toQAMap]; rfl

/-- thm:well-defined, `this` component (singleton frontier). -/
theorem lfp_TP_this (s pdef : Path Label) (n : ℕ) :
    OrderHom.lfp (TP Inh) (.this s pdef n) = thisSingleSet Inh s pdef n := by
  rw [lfp_TP_eq_toQAMap]; rfl

end InheritanceCalculus
