import InheritanceCalculus.ProgramMonotonicity

/-!
# Substitutability of the inheritance relation

The paper's Theorem "Substitutability of inheritance"
(thm:inheritance-substitutability) and Corollary "Behaviour compatibility"
(cor:behavior-compatibility), Appendix "Algebraic Properties of Deep Merge".

## Setting

Two primitives over the same written positions: `original`, a document in
which some references name a mixin `T` at the nonroot path `basePath`, and
`redirected`, the same document with any subset of those references
redirected to a mixin `S` at `derivedPath`, which inherits `T` in
`redirected` (`basePath ∈ bases*(derivedPath)`). A redirected reference is
*absolute*: its de Bruijn index is the length of the enclosing scope of its
carrying mixin, so its walk climbs to the root and it names `T ⌢ u` by the
full path; redirection replaces the prefix `basePath` of its projection list
by `derivedPath`. Taking `redirected = original` (no reference redirected)
gives the single-document theorem `inheritance_substitutable`.

Paths are in the reversed representation of `Basic.lean`: the paper's
`basePath ⌢ w` is `w ++ basePath`.

## Proof

One induction over `original`'s `Fact` derivations with a motive on `Atom`,
the paper's clauses (E1) to (E4). Each `original` fact has a `redirected`
fact at a related position, where `Related a b` holds when `a = b` or
`a = w ++ derivedPath` and `b = w ++ basePath`; a written override component
is preserved literally. The only fact the induction cannot reach from a
subderivation, a written reflexive override `basePath ⌢ w ∈
overrides(derivedPath ⌢ w)` on the derived side, is constructed directly by
induction on `w` (`overrides_written_base_extension`), and a redirected
reference resolves at the root on both sides (`this_full_length_root`).
-/

set_option warningAsError true

namespace InheritanceCalculus

variable {Label : Type*}

/-! ## Inversion facts about lengths -/

section LengthFacts

variable (Inh : Path Label → Option (Set (Reference Label)))

/-- A `supers` pair at a nonroot path has a nonroot override component, and a
pair at the root is `((), ())`; so the root override component occurs only at
the root. -/
theorem supers_override_nil_path {path site : Path Label}
    (hsupers : Supers Inh path site []) : path = [] := by
  cases hsupers with
  | supersRoot => rfl
  | supersStep _ hoverrides => exact absurd rfl (Overrides.ne_nil Inh hoverrides)

/-- An override component of length one belongs to a pair whose site is the
root: overrides of a top-level path are that path alone. -/
theorem supers_singleton_override_site {path site : Path Label} {label : Label}
    (hsupers : Supers Inh path site [label]) : site = [] := by
  cases hsupers with
  | supersStep _ hoverrides =>
      cases hoverrides with
      | overridesSelf _ _ => rfl
      | overridesBranch hsupersBranch _ => exact supers_override_nil_path Inh hsupersBranch

/-- A top-level override belongs to a top-level path. -/
theorem overrides_singleton_path {path : Path Label} {label overrideLabel : Label}
    (hoverrides : Overrides Inh (label :: path) [overrideLabel]) : path = [] := by
  cases hoverrides with
  | overridesSelf _ _ => rfl
  | overridesBranch hsupers _ => exact supers_override_nil_path Inh hsupers

/-- A walk whose index is the length of its definition site, from a nonroot
definition site, ends at the root. -/
theorem this_full_length_nonroot {source definitionSite target : Path Label}
    (hthis : This Inh source definitionSite definitionSite.length target)
    (hnonroot : definitionSite ≠ []) : target = [] := by
  induction definitionSite generalizing source with
  | nil => exact absurd rfl hnonroot
  | cons definitionLabel rest ih =>
      obtain ⟨site, hsupers, hrest⟩ := (this_succ_iff Inh).mp hthis
      cases rest with
      | nil =>
          rw [(this_zero_iff Inh).mp hrest]
          exact supers_singleton_override_site Inh hsupers
      | cons _ _ => exact ih hrest (by simp)

/-- An absolute reference (index = length of the enclosing scope of its
carrying override) resolves from the root: its walk ends at `()`. -/
theorem this_full_length_root {path : Path Label} {label overrideLabel : Label}
    {overrideRest target : Path Label}
    (hoverrides : Overrides Inh (label :: path) (overrideLabel :: overrideRest))
    (hthis : This Inh path overrideRest overrideRest.length target) : target = [] := by
  cases overrideRest with
  | nil =>
      rw [(this_zero_iff Inh).mp hthis]
      exact overrides_singleton_path Inh hoverrides
  | cons _ _ => exact this_full_length_nonroot Inh hthis (by simp)

/-- If `source` reaches `base` through `bases*` and `base` is nonroot, every
`supers` pair of `base` is a `supers` pair of `source`. -/
theorem supers_of_basesStar {source base site override : Path Label}
    (hsource : source ≠ []) (hbase : base ≠ [])
    (hchain : BasesStar Inh source base) (hsupers : Supers Inh base site override) :
    Supers Inh source site override := by
  obtain ⟨sourceLabel, sourceRest, rfl⟩ := List.exists_cons_of_ne_nil hsource
  obtain ⟨baseLabel, baseRest, rfl⟩ := List.exists_cons_of_ne_nil hbase
  obtain ⟨chainLabel, hbaseChain, hoverrides⟩ := (supers_cons_iff Inh).mp hsupers
  have hfull : BasesStar Inh (sourceLabel :: sourceRest) (chainLabel :: site) :=
    (basesStar_iff_reflTransGen Inh).mpr
      (((basesStar_iff_reflTransGen Inh).mp hchain).trans
        ((basesStar_iff_reflTransGen Inh).mp hbaseChain))
  exact (supers_cons_iff Inh).mpr ⟨chainLabel, hfull, hoverrides⟩

end LengthFacts

/-! ## The setting -/

/-- The setting of thm:inheritance-substitutability and
cor:behavior-compatibility, axiomatized on the abstract primitive. -/
structure Redirection (Label : Type*) where
  /-- The document in which the redirected references name `T`. -/
  original : Path Label → Option (Set (Reference Label))
  /-- The same document with those references naming `S`. -/
  redirected : Path Label → Option (Set (Reference Label))
  /-- The path of `S`, the inheriting mixin. -/
  derivedPath : Path Label
  /-- The path of `T`, the inherited mixin. -/
  basePath : Path Label
  basePath_ne_nil : basePath ≠ []
  /-- The paper's "`dom(inherits)` is prefix-closed", satisfied by every
  document the syntax layer produces. -/
  prefix_closed : ∀ (label : Label) (path : Path Label),
    (label :: path) ∈ Dom original → path ∈ Dom original
  /-- Redirection rewrites references, never written positions. -/
  dom_subset : ∀ path, path ∈ Dom original → path ∈ Dom redirected
  /-- `S` inherits `T` in the redirected document. -/
  inherits : BasesStar redirected derivedPath basePath
  /-- Every reference of `original` is kept, or is an absolute reference to
  some `T ⌢ u` redirected to `S ⌢ u`. -/
  references : ∀ (reference : Reference Label) (override : Path Label),
    MemRef original reference override →
      MemRef redirected reference override ∨
        ∃ projection : List Label,
          reference = (override.tail.length, projection ++ basePath) ∧
            MemRef redirected (override.tail.length, projection ++ derivedPath) override

namespace Redirection

variable (D : Redirection Label)

/-- Positions related by the redirection: equal, or the same extension `w` of
the derived and the base path. -/
def Related (derived base : Path Label) : Prop :=
  derived = base ∨ ∃ suffix, derived = suffix ++ D.derivedPath ∧ base = suffix ++ D.basePath

/-- `Related` with the empty extension `(derivedPath, basePath)` itself left
out: the positions at which `bases`, `bases*` and `overrides` are compared. -/
def RelatedBelow (derived base : Path Label) : Prop :=
  derived = base ∨
    ∃ suffix, suffix ≠ [] ∧ derived = suffix ++ D.derivedPath ∧ base = suffix ++ D.basePath

theorem derivedPath_ne_nil : D.derivedPath ≠ [] := by
  intro hnil
  have hchain := D.inherits
  rw [hnil] at hchain
  exact D.basePath_ne_nil (basesStar_nil D.redirected hchain)

theorem related_refl (path : Path Label) : D.Related path path := Or.inl rfl

theorem relatedBelow_refl (path : Path Label) : D.RelatedBelow path path := Or.inl rfl

theorem related_of_relatedBelow {derived base : Path Label}
    (h : D.RelatedBelow derived base) : D.Related derived base := by
  rcases h with h | ⟨suffix, -, hderived, hbase⟩
  · exact Or.inl h
  · exact Or.inr ⟨suffix, hderived, hbase⟩

theorem related_nil {derived : Path Label} (h : D.Related derived []) : derived = [] := by
  rcases h with h | ⟨suffix, -, hbase⟩
  · exact h
  · exact absurd (List.append_eq_nil_iff.mp hbase.symm).2 D.basePath_ne_nil

theorem relatedBelow_nil {derived : Path Label} (h : D.RelatedBelow derived []) :
    derived = [] :=
  D.related_nil (D.related_of_relatedBelow h)

/-- A `RelatedBelow` pair of nonroot paths shares its innermost label, and the
enclosing scopes are `Related`. -/
theorem relatedBelow_cons {derived : Path Label} {label : Label} {base : Path Label}
    (h : D.RelatedBelow derived (label :: base)) :
    ∃ derivedRest, derived = label :: derivedRest ∧ D.Related derivedRest base := by
  rcases h with h | ⟨suffix, hsuffix, hderived, hbase⟩
  · exact ⟨base, h, D.related_refl base⟩
  · obtain ⟨suffixLabel, suffixRest, rfl⟩ := List.exists_cons_of_ne_nil hsuffix
    simp only [List.cons_append, List.cons.injEq] at hbase
    obtain ⟨rfl, rfl⟩ := hbase
    exact ⟨suffixRest ++ D.derivedPath, by simpa using hderived,
      Or.inr ⟨suffixRest, rfl, rfl⟩⟩

theorem related_append {derived base : Path Label} (projection : List Label)
    (h : D.Related derived base) : D.Related (projection ++ derived) (projection ++ base) := by
  rcases h with rfl | ⟨suffix, rfl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨projection ++ suffix, by simp, by simp⟩

/-- Every prefix of a written path is written. -/
theorem dom_append {suffix path : Path Label} (h : suffix ++ path ∈ Dom D.original) :
    path ∈ Dom D.original := by
  induction suffix with
  | nil => simpa using h
  | cons label rest ih => exact ih (D.prefix_closed label _ h)

/-! ## Facts constructed directly on the derived side -/

/-- A written path is its own override on the derived side. -/
theorem overrides_written_self {path : Path Label} (hwritten : path ∈ Dom D.original) :
    Overrides D.redirected path path := by
  induction path with
  | nil => exact Fact.overridesRoot
  | cons label rest ih =>
      have hrest := ih (D.prefix_closed label rest hwritten)
      have hsupers : Supers D.redirected rest rest.tail rest := by
        cases rest with
        | nil => exact Fact.supersRoot
        | cons _ _ => exact Fact.supersStep (Fact.basesStarRefl _) hrest
      exact Fact.overridesSelf hsupers (D.dom_subset _ hwritten)

/-- A written extension `basePath ⌢ w` is an override component of
`supers(derivedPath ⌢ w)`. -/
theorem supers_written_base_extension :
    ∀ (suffix : Path Label), suffix ++ D.basePath ∈ Dom D.original →
      ∃ site, Supers D.redirected (suffix ++ D.derivedPath) site (suffix ++ D.basePath)
  | [], hwritten => by
      obtain ⟨baseLabel, baseRest, hbase⟩ := List.exists_cons_of_ne_nil D.basePath_ne_nil
      refine ⟨baseRest, ?_⟩
      simp only [List.nil_append] at hwritten ⊢
      have hself : Supers D.redirected D.basePath baseRest D.basePath := by
        rw [hbase]
        exact Fact.supersStep (Fact.basesStarRefl _) (hbase ▸ D.overrides_written_self hwritten)
      exact supers_of_basesStar D.redirected D.derivedPath_ne_nil D.basePath_ne_nil
        D.inherits hself
  | label :: rest, hwritten => by
      obtain ⟨site, hsupers⟩ :=
        supers_written_base_extension rest (D.prefix_closed label _ hwritten)
      exact ⟨rest ++ D.derivedPath, Fact.supersStep (Fact.basesStarRefl _)
        (Fact.overridesBranch hsupers (D.dom_subset _ hwritten))⟩

/-- A written extension `basePath ⌢ w ⌢ ℓ` is an override of
`derivedPath ⌢ w ⌢ ℓ`. -/
theorem overrides_written_base_extension (label : Label) (suffix : Path Label)
    (hwritten : label :: (suffix ++ D.basePath) ∈ Dom D.original) :
    Overrides D.redirected (label :: (suffix ++ D.derivedPath)) (label :: (suffix ++ D.basePath)) := by
  obtain ⟨site, hsupers⟩ :=
    D.supers_written_base_extension suffix (D.prefix_closed label _ hwritten)
  exact Fact.overridesBranch hsupers (D.dom_subset _ hwritten)

/-! ## The simulation -/

/-- The simulation motive over one derivation of `original`: clauses (E1) to
(E4) of the paper's proof. -/
def simulationMotive : Atom Label → Prop
  | .supers path site override =>
      ∀ derived, D.Related derived path →
        ∃ derivedSite derivedOverride, Supers D.redirected derived derivedSite derivedOverride ∧
          D.Related derivedSite site ∧ D.Related derivedOverride override ∧
          (override ∈ Dom D.original → derivedOverride = override)
  | .overrides path override =>
      ∀ derived, D.RelatedBelow derived path →
        ∃ derivedOverride, Overrides D.redirected derived derivedOverride ∧
          D.Related derivedOverride override ∧
          (override ∈ Dom D.original → derivedOverride = override)
  | .bases path target =>
      ∀ derived, D.RelatedBelow derived path →
        ∃ derivedTarget, Bases D.redirected derived derivedTarget ∧ D.Related derivedTarget target
  | .basesStar path target =>
      ∀ derived, D.RelatedBelow derived path →
        ∃ derivedTarget, BasesStar D.redirected derived derivedTarget ∧
          D.RelatedBelow derivedTarget target
  | .this source definitionSite steps target =>
      definitionSite ∈ Dom D.original →
        ∀ derivedSource, D.Related derivedSource source →
          ∃ derivedTarget, This D.redirected derivedSource definitionSite steps derivedTarget ∧
            D.Related derivedTarget target

theorem simulation {atom : Atom Label} (hatom : Fact D.original atom) :
    D.simulationMotive atom := by
  induction hatom with
  | supersRoot =>
      intro derived hrelated
      rw [D.related_nil hrelated]
      exact ⟨[], [], Fact.supersRoot, D.related_refl _, D.related_refl _, fun _ => rfl⟩
  | @supersStep pathLabel path baseLabel site override hchain hoverrides ihChain ihOverrides =>
      -- The comparison at a `RelatedBelow` position, used directly and, for the
      -- pair `(derivedPath, basePath)` itself, after prefixing `S`'s chain to `T`.
      have below : ∀ derived, D.RelatedBelow derived (pathLabel :: path) →
          ∃ derivedSite derivedOverride, Supers D.redirected derived derivedSite derivedOverride ∧
            D.Related derivedSite site ∧ D.Related derivedOverride override ∧
            (override ∈ Dom D.original → derivedOverride = override) := by
        intro derived hrelated
        obtain ⟨derivedBase, hderivedChain, hbaseRelated⟩ := ihChain derived hrelated
        obtain ⟨derivedBaseRest, hderivedBase, hsiteRelated⟩ := D.relatedBelow_cons hbaseRelated
        obtain ⟨derivedOverride, hderivedOverrides, hoverrideRelated, hwritten⟩ :=
          ihOverrides derivedBase hbaseRelated
        obtain ⟨derivedRest, rfl, -⟩ := D.relatedBelow_cons hrelated
        subst hderivedBase
        exact ⟨derivedBaseRest, derivedOverride,
          Fact.supersStep hderivedChain hderivedOverrides, hsiteRelated, hoverrideRelated, hwritten⟩
      intro derived hrelated
      rcases hrelated with hequal | ⟨suffix, hderived, hbase⟩
      · exact below derived (Or.inl hequal)
      · cases suffix with
        | nil =>
            simp only [List.nil_append] at hderived hbase
            obtain ⟨derivedSite, derivedOverride, hsupers, hrest⟩ :=
              below (pathLabel :: path) (D.relatedBelow_refl _)
            rw [hbase] at hsupers
            rw [hderived]
            exact ⟨derivedSite, derivedOverride,
              supers_of_basesStar D.redirected D.derivedPath_ne_nil
                D.basePath_ne_nil D.inherits hsupers, hrest⟩
        | cons suffixLabel suffixRest =>
            exact below derived (Or.inr ⟨_, by simp, hderived, hbase⟩)
  | overridesRoot =>
      intro derived hrelated
      rw [D.relatedBelow_nil hrelated]
      exact ⟨[], Fact.overridesRoot, D.related_refl _, fun _ => rfl⟩
  | @overridesSelf path site branch label hsupers hdom ihSupers =>
      intro derived hrelated
      have hbranch : branch ∈ Dom D.original := D.prefix_closed label branch hdom
      obtain ⟨derivedRest, rfl, hrestRelated⟩ := D.relatedBelow_cons hrelated
      obtain ⟨derivedSite, derivedBranch, hderivedSupers, -, -, hbranchEqual⟩ :=
        ihSupers derivedRest hrestRelated
      rw [hbranchEqual hbranch] at hderivedSupers
      have hdomRedirected := D.dom_subset _ hdom
      rcases hrelated with hequal | ⟨suffix, hsuffix, hderived, hbase⟩
      · have hrest : derivedRest = path := (List.cons.inj hequal).2
        rw [hrest] at hderivedSupers
        rw [hequal]
        exact ⟨label :: path, Fact.overridesSelf hderivedSupers hdomRedirected,
          D.related_refl _, fun _ => rfl⟩
      · by_cases hwritten : label :: path ∈ Dom D.original
        · obtain ⟨suffixLabel, suffixRest, rfl⟩ := List.exists_cons_of_ne_nil hsuffix
          rw [hbase] at hwritten ⊢
          rw [hderived]
          simp only [List.cons_append] at hwritten ⊢
          exact ⟨_, D.overrides_written_base_extension suffixLabel suffixRest hwritten,
            D.related_refl _, fun _ => rfl⟩
        · exact ⟨_, Fact.overridesSelf hderivedSupers hdomRedirected,
            Or.inr ⟨suffix, hderived, hbase⟩, fun h => absurd h hwritten⟩
  | @overridesBranch path site branch label hsupers hdom ihSupers =>
      intro derived hrelated
      have hbranch : branch ∈ Dom D.original := D.prefix_closed label branch hdom
      obtain ⟨derivedRest, rfl, hrestRelated⟩ := D.relatedBelow_cons hrelated
      obtain ⟨derivedSite, derivedBranch, hderivedSupers, -, -, hbranchEqual⟩ :=
        ihSupers derivedRest hrestRelated
      rw [hbranchEqual hbranch] at hderivedSupers
      exact ⟨label :: branch, Fact.overridesBranch hderivedSupers (D.dom_subset _ hdom),
        D.related_refl _, fun _ => rfl⟩
  | @basesStep path current label overrideLabel overrideRest steps projection
      hoverrides hreference hthis ihOverrides ihThis =>
      intro derived hrelated
      have hoverrideWritten : (overrideLabel :: overrideRest) ∈ Dom D.original :=
        hreference.mem_dom
      obtain ⟨derivedOverride, hderivedOverrides, -, hoverrideEqual⟩ :=
        ihOverrides derived hrelated
      rw [hoverrideEqual hoverrideWritten] at hderivedOverrides
      obtain ⟨derivedRest, rfl, hrestRelated⟩ := D.relatedBelow_cons hrelated
      obtain ⟨derivedCurrent, hderivedThis, hcurrentRelated⟩ :=
        ihThis (D.prefix_closed overrideLabel overrideRest hoverrideWritten) derivedRest hrestRelated
      rcases D.references _ _ hreference with hkept | ⟨redirectedProjection, hreferenceEqual, hredirected⟩
      · exact ⟨projection ++ derivedCurrent,
          Fact.basesStep hderivedOverrides hkept hderivedThis,
          D.related_append projection hcurrentRelated⟩
      · simp only [List.tail_cons, Prod.mk.injEq] at hreferenceEqual
        obtain ⟨rfl, rfl⟩ := hreferenceEqual
        have hcurrentRoot : current = [] :=
          this_full_length_root D.original hoverrides hthis
        subst hcurrentRoot
        have hderivedCurrentRoot : derivedCurrent = [] := D.related_nil hcurrentRelated
        subst hderivedCurrentRoot
        refine ⟨redirectedProjection ++ D.derivedPath ++ [],
          Fact.basesStep hderivedOverrides hredirected hderivedThis, ?_⟩
        simp only [List.append_nil]
        exact Or.inr ⟨redirectedProjection, rfl, rfl⟩
  | basesStarRefl path =>
      intro derived hrelated
      exact ⟨derived, Fact.basesStarRefl derived, hrelated⟩
  | @basesStarTail path middle target hchain hstep ihChain ihStep =>
      intro derived hrelated
      obtain ⟨derivedMiddle, hderivedChain, hmiddleRelated⟩ := ihChain derived hrelated
      obtain ⟨derivedTarget, hderivedStep, htargetRelated⟩ := ihStep derivedMiddle hmiddleRelated
      have hextended : BasesStar D.redirected derived derivedTarget :=
        Fact.basesStarTail hderivedChain hderivedStep
      rcases htargetRelated with hequal | ⟨suffix, hderived, hbase⟩
      · exact ⟨derivedTarget, hextended, Or.inl hequal⟩
      · cases suffix with
        | nil =>
            simp only [List.nil_append] at hderived hbase
            subst hderived
            subst hbase
            exact ⟨D.basePath,
              (basesStar_iff_reflTransGen D.redirected).mpr
                (((basesStar_iff_reflTransGen D.redirected).mp hextended).trans
                  ((basesStar_iff_reflTransGen D.redirected).mp D.inherits)),
              D.relatedBelow_refl _⟩
        | cons suffixLabel suffixRest =>
            exact ⟨derivedTarget, hextended, Or.inr ⟨_, by simp, hderived, hbase⟩⟩
  | thisZero source definitionSite =>
      intro _ derivedSource hrelated
      exact ⟨derivedSource, Fact.thisZero _ _, hrelated⟩
  | @thisSucc source site target definitionLabel definitionRest steps hsupers hrecursion
      ihSupers ihRecursion =>
      intro hwritten derivedSource hrelated
      obtain ⟨derivedSite, derivedOverride, hderivedSupers, hsiteRelated, -, hoverrideEqual⟩ :=
        ihSupers derivedSource hrelated
      rw [hoverrideEqual hwritten] at hderivedSupers
      obtain ⟨derivedTarget, hderivedRecursion, htargetRelated⟩ :=
        ihRecursion (D.prefix_closed definitionLabel definitionRest hwritten) derivedSite hsiteRelated
      exact ⟨derivedTarget, Fact.thisSucc hderivedSupers hderivedRecursion, htargetRelated⟩

/-! ## Conclusions -/

/-- cor:behavior-compatibility, at every path: every written override
component of `supers(q)` in `original` is an override component of `supers(q)`
in `redirected`. -/
theorem supers_written_preserved {path site override : Path Label}
    (hsupers : Supers D.original path site override) (hwritten : override ∈ Dom D.original) :
    ∃ derivedSite, Supers D.redirected path derivedSite override := by
  obtain ⟨derivedSite, derivedOverride, hderived, -, -, hequal⟩ :=
    D.simulation hsupers path (D.related_refl path)
  exact ⟨derivedSite, hequal hwritten ▸ hderived⟩

/-- thm:inheritance-substitutability (b2) and cor:behavior-compatibility at the
read point: every written override component of `supers(basePath ⌢ w)` in
`original` is an override component of `supers(derivedPath ⌢ w)` in
`redirected`. -/
theorem supers_written_transferred {suffix site override : Path Label}
    (hsupers : Supers D.original (suffix ++ D.basePath) site override)
    (hwritten : override ∈ Dom D.original) :
    ∃ derivedSite, Supers D.redirected (suffix ++ D.derivedPath) derivedSite override := by
  obtain ⟨derivedSite, derivedOverride, hderived, -, -, hequal⟩ :=
    D.simulation hsupers (suffix ++ D.derivedPath) (Or.inr ⟨suffix, rfl, rfl⟩)
  exact ⟨derivedSite, hequal hwritten ▸ hderived⟩

/-- Existence form at every path: a path that exists in `original` exists in
`redirected`. -/
theorem exists_preserved {path : Path Label}
    (hexists : (supersSet D.original path).Nonempty) :
    (supersSet D.redirected path).Nonempty := by
  obtain ⟨⟨site, override⟩, hsupers⟩ := hexists
  obtain ⟨derivedSite, derivedOverride, hderived, -⟩ :=
    D.simulation hsupers path (D.related_refl path)
  exact ⟨⟨derivedSite, derivedOverride⟩, hderived⟩

/-- Existence form at the read point: if `basePath ⌢ w` exists in `original`,
then `derivedPath ⌢ w` exists in `redirected`. -/
theorem exists_transferred {suffix : Path Label}
    (hexists : (supersSet D.original (suffix ++ D.basePath)).Nonempty) :
    (supersSet D.redirected (suffix ++ D.derivedPath)).Nonempty := by
  obtain ⟨⟨site, override⟩, hsupers⟩ := hexists
  obtain ⟨derivedSite, derivedOverride, hderived, -⟩ :=
    D.simulation hsupers (suffix ++ D.derivedPath) (Or.inr ⟨suffix, rfl, rfl⟩)
  exact ⟨⟨derivedSite, derivedOverride⟩, hderived⟩

end Redirection

/-! ## The single-document theorem -/

/-- The single-document instance: no reference redirected. -/
def Redirection.ofInherits (Inh : Path Label → Option (Set (Reference Label)))
    (derivedPath basePath : Path Label) (hbase : basePath ≠ [])
    (hprefix : ∀ (label : Label) (path : Path Label), (label :: path) ∈ Dom Inh → path ∈ Dom Inh)
    (hinherits : BasesStar Inh derivedPath basePath) : Redirection Label where
  original := Inh
  redirected := Inh
  derivedPath := derivedPath
  basePath := basePath
  basePath_ne_nil := hbase
  prefix_closed := hprefix
  dom_subset := fun _ h => h
  inherits := hinherits
  references := fun _ _ h => Or.inl h

/-- thm:inheritance-substitutability (b2): in a document whose written
positions are prefix-closed, if the mixin at `derivedPath` inherits the mixin
at the nonroot `basePath` (`basePath ∈ bases*(derivedPath)`), then for every
suffix `w`, every written override component of `supers(basePath ⌢ w)` is an
override component of `supers(derivedPath ⌢ w)`, and the existence of
`basePath ⌢ w` implies that of `derivedPath ⌢ w`. -/
theorem inheritance_substitutable (Inh : Path Label → Option (Set (Reference Label)))
    {derivedPath basePath : Path Label} (hbase : basePath ≠ [])
    (hprefix : ∀ (label : Label) (path : Path Label), (label :: path) ∈ Dom Inh → path ∈ Dom Inh)
    (hinherits : BasesStar Inh derivedPath basePath) (suffix : Path Label) :
    (∀ site override, Supers Inh (suffix ++ basePath) site override → override ∈ Dom Inh →
      ∃ derivedSite, Supers Inh (suffix ++ derivedPath) derivedSite override) ∧
    ((supersSet Inh (suffix ++ basePath)).Nonempty →
      (supersSet Inh (suffix ++ derivedPath)).Nonempty) :=
  let D := Redirection.ofInherits Inh derivedPath basePath hbase hprefix hinherits
  ⟨fun _ _ hsupers hwritten => D.supers_written_transferred hsupers hwritten,
    fun hexists => D.exists_transferred hexists⟩

end InheritanceCalculus
