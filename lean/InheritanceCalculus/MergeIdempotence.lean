import InheritanceCalculus.PathExistence

/-!
# Algebraic properties of deep merge: idempotence

The paper's Theorem "Idempotence" (thm:merge-idempotent, Appendix "Algebraic
Properties of Deep Merge"), fully proved: `merge_idempotent` and
`merge_idempotent_exists` at the end of this file. The two sides of the law
are the composition of `p₁` with itself, the wrapper `mergedTwice` written
`[p₁], [p₁]`, and `p₁`; the law compares the two paths of one document.

The two written references enter the proof in one place: `inherits` carries
*sets* of references, so the wrapper inherits the one-element set
`{(1, p₁)}` (`inh_sigma`), and its single ground hop reaches `p₁`
(`bases_sigma`). Every other step is a simulation between the wrapper and
`p₁`.

## Setting

One reserved root, one synthetic root `σ` written with the references
`[p₁], [p₁]`, and a *fixed* target root `p₁` in place of another synthetic
root. The axiomatization `IdempotenceDocument` mirrors
`AssociativityDocument` (`MergeAssociativity.lean`) with a single wrapper
and a single base, plus two hypotheses absent from it: `base_exists` (the
paper's "the path `p` exists") and `prefix_closed` (the paper's
"`dom(inherits)` is prefix-closed", satisfied by every document the syntax
layer produces).

## Why the statement and proof genuinely differ from `merge_associative`

Two real mathematical differences, not artifacts to "align away":

1. **Written components only.** The reflexive override of `σ ⌢ w` is always
   a *synthetic* path (filtered by the statement's outside-subtree
   condition), but the reflexive override of `p₁ ⌢ w` is a *fixed* path
   that eq:overrides can produce *unwritten* (its guard is that some written
   branch qualifies, not that the reflexive path itself is written). An
   unwritten reflexive override therefore can appear on the `p₁` side with
   no `σ`-side counterpart, so the naive "all outside-subtree override
   components agree" statement is false; the theorem compares *written*
   components only, which is exactly what `Dom D.Inh` filters for below.
2. **Prefix closure.** Without it, a qualifying branch `p_branch` could be
   unwritten while `p_branch ⌢ ℓ` is written, letting the `p₁` side reach a
   branch the `σ` side cannot; prefix closure forces every qualifying branch
   to be written (`base_written`-style), closing this gap.

## Structure

- B1 (ground facts): `overrides`/`bases`/`supers` at the reserved root and
  the synthetic root `σ`, plus the new ground fact `overrides_p₁_self`
  (`p₁ ∈ overrides(p₁)`, from `base_exists` via the Path Existence Lemma).
- B2 (structural facts): definedness of `inherits` on `σ` and its proper
  extensions, insulation of walks and literal resolution, and the
  classification lemmas for the rewriting map `φ`.
- B3 (simulation, `σ → p₁`): the paper's clauses (C1)–(C4) as one structural
  induction over `Fact` derivations with a motive on `Atom`, for the single
  root `σ` and the *fixed* target `p₁` (unlike the simulation of
  `MergeSimulation.lean`, no ground-hop parameter is needed: the single-hop
  ground fact `bases_sigma` supplies it directly).
- B3′ (anchored transfer, `p₁ → σ`): no global rewriting map exists on this
  side (a fixed reference may resolve literally to a spine path `p₁ ⌢ u`,
  and such occurrences must stay as they are); clauses (C1′)–(C4′) instead
  assert derivability at the anchors, by the same style of induction.
- B4 (conclusion): both directions give the agreement of the written,
  outside-subtree override components at `σ ⌢ w` and `p₁ ⌢ w`, and
  existence transfers via the Path Existence Lemma.
-/

set_option warningAsError true

namespace InheritanceCalculus

/-- The canonical idempotence construction, axiomatized on the abstract
primitive (paper thm:merge-idempotent, hypothesis part). Paths are in the
reversed representation of `Basic.lean`, so the paper's synthetic root
`(__merge, mergedTwice)` is `[mergedTwice, reserved]` and its extensions are
`w ++ [mergedTwice, reserved]`; the base extension is `w ++ p₁`. -/
structure IdempotenceDocument (Label : Type*) where
  Inh : Path Label → Option (Set (Reference Label))
  reserved : Label
  mergedTwice : Label
  p₁ : Path Label
  wrapper_ne_reserved : mergedTwice ≠ reserved
  inh_reserved : Inh [reserved] = some ∅
  /-- `mergedTwice` is written with the reference `[p₁]` twice. -/
  inh_mergedTwice : Inh [mergedTwice, reserved] = some {(1, p₁), (1, p₁)}
  /-- Nothing else is written inside the reserved subtree: a written path
  ending in the reserved label is the reserved root or the synthetic root. -/
  reserved_subtree : ∀ q ∈ Dom Inh, (∃ w, q = w ++ [reserved]) →
    q = [reserved] ∨ q = [mergedTwice, reserved]
  /-- The reserved label occurs in no reference's projection list. -/
  reserved_not_in_references : ∀ q S, Inh q = some S → ∀ r ∈ S, reserved ∉ r.2
  base_nonempty : p₁ ≠ []
  base_written : p₁ ∈ Dom Inh
  /-- The base lies outside the reserved subtree. -/
  base_outside : ¬ ∃ w, p₁ = w ++ [reserved]
  /-- The wrapper label is distinct from the first label of `p₁` (the
  outermost, the last element in the reversed representation). -/
  base_head_not_wrapper : ¬ ∃ w, p₁ = w ++ [mergedTwice]
  /-- The paper's "the path `p` exists": `supers(p₁) ≠ ∅`. -/
  base_exists : ∃ c pov, Supers Inh p₁ c pov
  /-- The paper's "`dom(inherits)` is prefix-closed". -/
  prefix_closed : ∀ (ℓ : Label) (q : Path Label), (ℓ :: q) ∈ Dom Inh → q ∈ Dom Inh

namespace IdempotenceDocument

variable {Label : Type*} (D : IdempotenceDocument Label)

/-- The reserved root, the paper's `p_reserved = (__merge)`. -/
abbrev reservedRoot : Path Label := [D.reserved]

/-- The synthetic root, the paper's `σ = (__merge, mergedTwice)`. -/
abbrev sigma : Path Label := [D.mergedTwice, D.reserved]

/-- The two written references `[p₁]` are one element of the set `inherits`
carries, so the wrapper inherits the one-element set `{[p₁]}`. -/
theorem inh_sigma : D.Inh D.sigma = some {(1, D.p₁)} := by
  rw [D.inh_mergedTwice, Set.pair_eq_singleton]

/-- A path lies inside the reserved subtree exactly when its outermost label
(the last element in the reversed representation) is the reserved label. -/
def InSubtree (q : Path Label) : Prop := ∃ w, q = w ++ [D.reserved]

/-- A synthetic path: an extension of the synthetic root `σ`. -/
def Synthetic (q : Path Label) : Prop := ∃ w : Path Label, q = w ++ D.sigma

/-- The rewriting map of the `σ → p₁` simulation: send an extension
`w ++ σ` of the synthetic root to the same extension `w ++ p₁` of the
(fixed) target root, and leave every other path fixed. -/
noncomputable def phi (q : Path Label) : Path Label :=
  open Classical in
  if D.Synthetic q then q.dropLast.dropLast ++ D.p₁ else q

theorem phi_of_not_synthetic {q : Path Label} (h : ¬ D.Synthetic q) :
    D.phi q = q := by
  simp [phi, h]

theorem phi_of_synthetic (w : Path Label) : D.phi (w ++ D.sigma) = w ++ D.p₁ := by
  have hsyn : D.Synthetic (w ++ D.sigma) := ⟨w, rfl⟩
  have hdrop : (w ++ D.sigma).dropLast.dropLast = w := by
    show (w ++ [D.mergedTwice, D.reserved]).dropLast.dropLast = w
    rw [show w ++ [D.mergedTwice, D.reserved] = (w ++ [D.mergedTwice]) ++ [D.reserved] by simp,
      List.dropLast_concat, List.dropLast_concat]
  simp only [phi]
  rw [if_pos hsyn, hdrop]

theorem phi_append_of_synthetic (w v : Path Label) :
    D.phi (v ++ (w ++ D.sigma)) = v ++ D.phi (w ++ D.sigma) := by
  rw [phi_of_synthetic D w, show v ++ (w ++ D.sigma) = (v ++ w) ++ D.sigma by simp,
    phi_of_synthetic D (v ++ w), List.append_assoc]

/-! ## Stage B1: ground facts at the reserved root ("chain flattening") -/

theorem overrides_reservedRoot {pov : Path Label} :
    Overrides D.Inh D.reservedRoot pov ↔ pov = D.reservedRoot := by
  constructor
  · intro h
    rcases (overrides_cons_iff D.Inh).mp h with ⟨c, pbr, hsup, hdom, hor⟩
    obtain ⟨rfl, rfl⟩ := (supers_nil_iff D.Inh).mp hsup
    rcases hor with rfl | rfl <;> rfl
  · rintro rfl
    exact Fact.overridesSelf Fact.supersRoot (by simp [Dom, D.inh_reserved])

theorem not_bases_reservedRoot {t : Path Label} :
    ¬ Bases D.Inh D.reservedRoot t := by
  intro h
  rcases (bases_cons_iff D.Inh).mp h with ⟨pov, hov, n, w, href, -⟩
  rw [overrides_reservedRoot D] at hov
  subst hov
  obtain ⟨S, hS, hr⟩ := href
  rw [D.inh_reserved] at hS
  cases hS
  exact hr

theorem basesStar_reservedRoot {pb : Path Label}
    (h : BasesStar D.Inh D.reservedRoot pb) : pb = D.reservedRoot := by
  have h' := (basesStar_iff_reflTransGen D.Inh).mp h
  clear h
  induction h' with
  | refl => rfl
  | tail _ hstep ih =>
      subst ih
      exact absurd hstep (not_bases_reservedRoot D)

theorem supers_reservedRoot {c pov : Path Label} :
    Supers D.Inh D.reservedRoot c pov ↔ c = [] ∧ pov = D.reservedRoot := by
  constructor
  · intro h
    rcases (supers_cons_iff D.Inh).mp h with ⟨ℓb, hchain, hov⟩
    obtain ⟨rfl, rfl⟩ : ℓb = D.reserved ∧ c = [] := by
      simpa using basesStar_reservedRoot D hchain
    rw [overrides_reservedRoot D] at hov
    exact ⟨rfl, hov⟩
  · rintro ⟨rfl, rfl⟩
    exact Fact.supersStep (Fact.basesStarRefl _)
      ((overrides_reservedRoot D).mpr rfl)

theorem sigma_mem_dom : D.sigma ∈ Dom D.Inh := by
  simp [Dom, D.inh_sigma]

theorem overrides_sigma {pov : Path Label} :
    Overrides D.Inh D.sigma pov ↔ pov = D.sigma := by
  constructor
  · intro h
    rcases (overrides_cons_iff D.Inh).mp h with ⟨c, pbr, hsup, hdom, hor⟩
    obtain ⟨rfl, rfl⟩ := (supers_reservedRoot D).mp hsup
    rcases hor with rfl | rfl <;> rfl
  · rintro rfl
    exact Fact.overridesSelf ((supers_reservedRoot D).mpr ⟨rfl, rfl⟩) (sigma_mem_dom D)

/-- The one walk step of the `[p₁]`-style reference consumes exactly the
shared pair `((), p_reserved)`. -/
theorem this_reserved_one {pcur : Path Label} :
    This D.Inh D.reservedRoot D.reservedRoot 1 pcur ↔ pcur = [] := by
  constructor
  · intro h
    rcases (this_succ_iff D.Inh).mp h with ⟨psite, hsup, hrec⟩
    obtain ⟨rfl, -⟩ := (supers_reservedRoot D).mp hsup
    exact (this_zero_iff D.Inh).mp hrec
  · rintro rfl
    exact Fact.thisSucc ((supers_reservedRoot D).mpr ⟨rfl, rfl⟩) (Fact.thisZero _ _)

theorem resolve_sigma_one {w t : Path Label} :
    Resolve D.Inh D.reservedRoot D.sigma 1 w t ↔ t = w := by
  constructor
  · rintro ⟨ℓd, pd, heq, pcur, hthis, rfl⟩
    obtain ⟨rfl, rfl⟩ : D.mergedTwice = ℓd ∧ D.reservedRoot = pd := by simpa [sigma] using heq
    rw [(this_reserved_one D).mp hthis, List.append_nil]
  · rintro rfl
    exact ⟨D.mergedTwice, D.reservedRoot, rfl, [], (this_reserved_one D).mpr rfl,
      (List.append_nil _).symm⟩

theorem bases_sigma {t : Path Label} : Bases D.Inh D.sigma t ↔ t = D.p₁ := by
  constructor
  · intro h
    rcases (bases_cons_iff D.Inh).mp h with ⟨pov, hov, n, w, href, hres⟩
    rw [overrides_sigma D] at hov
    subst hov
    obtain ⟨Srefs, hS, hr⟩ := href
    rw [D.inh_sigma] at hS
    cases hS
    obtain ⟨rfl, rfl⟩ : n = 1 ∧ w = D.p₁ := by simpa using hr
    exact (resolve_sigma_one D).mp hres
  · rintro rfl
    have h := Fact.basesStep ((overrides_sigma D).mpr rfl)
      (⟨_, D.inh_sigma, rfl⟩ : MemRef D.Inh (1, D.p₁) D.sigma)
      ((this_reserved_one D).mpr rfl)
    simpa using h

theorem basesStar_sigma {t : Path Label} :
    BasesStar D.Inh D.sigma t ↔ t = D.sigma ∨ BasesStar D.Inh D.p₁ t := by
  simp only [basesStar_iff_reflTransGen]
  constructor
  · intro h
    rcases h.cases_head with heq | ⟨c, hbc, hct⟩
    · exact Or.inl heq.symm
    · rw [(bases_sigma D).mp hbc] at hct
      exact Or.inr hct
  · rintro (rfl | h)
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.head ((bases_sigma D).mpr rfl) h

/-- `supers` unfolds through `supers_cons_iff` at any nonempty query. -/
theorem supers_iff_of_ne_nil {q : Path Label} (hq : q ≠ []) {c pov : Path Label} :
    Supers D.Inh q c pov ↔
      ∃ ℓb, BasesStar D.Inh q (ℓb :: c) ∧ Overrides D.Inh (ℓb :: c) pov := by
  cases q with
  | nil => exact absurd rfl hq
  | cons ℓq q' => exact supers_cons_iff D.Inh

theorem supers_sigma {c pov : Path Label} :
    Supers D.Inh D.sigma c pov ↔
      (c = D.reservedRoot ∧ pov = D.sigma) ∨ Supers D.Inh D.p₁ c pov := by
  rw [supers_iff_of_ne_nil D (by simp [sigma])]
  constructor
  · rintro ⟨ℓb, hchain, hov⟩
    rcases (basesStar_sigma D).mp hchain with heq | hchain'
    · obtain ⟨rfl, rfl⟩ : ℓb = D.mergedTwice ∧ c = D.reservedRoot := by simpa [sigma] using heq
      rw [overrides_sigma D] at hov
      exact Or.inl ⟨rfl, hov⟩
    · exact Or.inr ((supers_iff_of_ne_nil D D.base_nonempty).mpr ⟨ℓb, hchain', hov⟩)
  · rintro (⟨rfl, rfl⟩ | hsup)
    · exact ⟨D.mergedTwice, (basesStar_sigma D).mpr (Or.inl rfl), (overrides_sigma D).mpr rfl⟩
    · obtain ⟨ℓb, hchain, hov⟩ := (supers_iff_of_ne_nil D D.base_nonempty).mp hsup
      exact ⟨ℓb, (basesStar_sigma D).mpr (Or.inr hchain), hov⟩

/-- The new ground fact of this theorem (absent from `AssociativityDocument`):
since `p₁` exists, the Path Existence Lemma produces a qualifying branch at
`p₁`'s enclosing path, and eq:overrides reads off the reflexive override
`p₁ ∈ overrides(p₁)`. -/
theorem overrides_p₁_self : Overrides D.Inh D.p₁ D.p₁ := by
  have hex : (supersSet D.Inh D.p₁).Nonempty := by
    obtain ⟨c, pov, hsup⟩ := D.base_exists
    exact ⟨(c, pov), hsup⟩
  rw [supersSet_nonempty_iff_existent] at hex
  rcases hex with heq | ⟨p, ℓ, c, pbr, heq, hsup, hdom⟩
  · exact absurd heq D.base_nonempty
  · rw [heq]; exact Fact.overridesSelf hsup hdom

/-! ## Stage B2: structural facts and the classification lemmas for `φ` -/

/-- A proper extension of `σ` is not written (structural fact (i)): the
wrapper body carries a reference and no definitions. -/
theorem synExt_notMem_dom {w : Path Label} (hw : w ≠ []) :
    (w ++ D.sigma) ∉ Dom D.Inh := by
  intro hdom
  rcases D.reserved_subtree _ hdom ⟨w ++ [D.mergedTwice], by simp [sigma]⟩ with heq | heq
  · have hlen := congrArg List.length heq
    simp [sigma, List.length_append] at hlen
  · have hlen := congrArg List.length heq
    simp only [sigma, List.length_append, List.length_cons, List.length_nil] at hlen
    exact hw (by
      have : w.length = 0 := by omega
      exact List.length_eq_zero_iff.mp this)

/-- A written synthetic path is `σ` itself. -/
theorem written_synthetic {q : Path Label} (hq : q ∈ Dom D.Inh) (hsyn : D.Synthetic q) :
    q = D.sigma := by
  obtain ⟨w, rfl⟩ := hsyn
  cases w with
  | nil => rfl
  | cons a w' => exact absurd hq (synExt_notMem_dom D (by simp))

theorem not_synthetic_nil : ¬ D.Synthetic [] := by
  rintro ⟨w, heq⟩
  have := congrArg List.length heq
  simp [sigma, List.length_append] at this

theorem not_synthetic_reservedRoot : ¬ D.Synthetic D.reservedRoot := by
  rintro ⟨w, heq⟩
  have := congrArg List.length heq
  simp [sigma, reservedRoot, List.length_append] at this

theorem phi_nil : D.phi [] = [] := phi_of_not_synthetic D (not_synthetic_nil D)

theorem phi_reservedRoot : D.phi D.reservedRoot = D.reservedRoot :=
  phi_of_not_synthetic D (not_synthetic_reservedRoot D)

theorem phi_sigma : D.phi D.sigma = D.p₁ := by
  have h := phi_of_synthetic D (w := ([] : Path Label))
  simpa using h

/-- `φ` distributes over `cons` away from `σ` itself. -/
theorem phi_cons_of_ne_root {ℓ : Label} {p : Path Label} (h : ℓ :: p ≠ D.sigma) :
    D.phi (ℓ :: p) = ℓ :: D.phi p := by
  by_cases hsyn : D.Synthetic (ℓ :: p)
  · obtain ⟨w, heq⟩ := hsyn
    cases w with
    | nil => exact absurd heq h
    | cons a w' =>
        obtain ⟨rfl, rfl⟩ : ℓ = a ∧ p = w' ++ D.sigma := by simpa using heq
        rw [show ℓ :: (w' ++ D.sigma) = (ℓ :: w') ++ D.sigma from rfl,
          phi_of_synthetic D, phi_of_synthetic D]
        rfl
  · have hp : ¬ D.Synthetic p := by
      rintro ⟨w, rfl⟩
      exact hsyn ⟨ℓ :: w, rfl⟩
    rw [phi_of_not_synthetic D hsyn, phi_of_not_synthetic D hp]

/-- `φ` never collapses a nonempty path to the empty path: it is the
identity off `Synthetic`, and on `Synthetic` inputs its value ends in the
nonempty `p₁`. -/
theorem phi_ne_nil {q : Path Label} (hq : q ≠ []) : D.phi q ≠ [] := by
  by_cases hsyn : D.Synthetic q
  · obtain ⟨w, rfl⟩ := hsyn
    rw [phi_of_synthetic D]
    intro hnil
    exact D.base_nonempty (by
      rcases List.append_eq_nil_iff.mp hnil with ⟨-, hp⟩
      exact hp)
  · rwa [phi_of_not_synthetic D hsyn]

/-- The condition maintained on definition-site paths through the walk: the
reserved root itself, or a path outside the reserved subtree. -/
def PdefCond (q : Path Label) : Prop :=
  q = D.reservedRoot ∨ ¬ D.InSubtree q

theorem pdefCond_not_synthetic {q : Path Label} (h : D.PdefCond q) :
    ¬ D.Synthetic q := by
  rintro ⟨w, rfl⟩
  rcases h with heq | hout
  · have := congrArg List.length heq
    simp [sigma, List.length_append] at this
  · exact hout ⟨w ++ [D.mergedTwice], by simp [sigma]⟩

theorem phi_of_pdefCond {q : Path Label} (h : D.PdefCond q) : D.phi q = q :=
  phi_of_not_synthetic D (pdefCond_not_synthetic D h)

theorem pdefCond_nil : D.PdefCond [] :=
  Or.inr fun ⟨w, hw⟩ => by
    have := congrArg List.length hw
    simp [List.length_append] at this

theorem pdefCond_reservedRoot : D.PdefCond D.reservedRoot := Or.inl rfl

/-- `PdefCond` propagates to the tail of a written path (the `init` of a
definition site stays reserved-root-or-outside). -/
theorem pdefCond_tail_of_written {ℓov : Label} {povt : Path Label}
    (hpov : (ℓov :: povt) ∈ Dom D.Inh) : D.PdefCond povt := by
  by_cases hsub : D.InSubtree (ℓov :: povt)
  · rcases D.reserved_subtree _ hpov hsub with heq | heq
    · obtain ⟨-, rfl⟩ : ℓov = D.reserved ∧ povt = [] := by simpa using heq
      exact pdefCond_nil D
    · obtain ⟨-, rfl⟩ : ℓov = D.mergedTwice ∧ povt = D.reservedRoot := by simpa [sigma] using heq
      exact pdefCond_reservedRoot D
  · exact Or.inr fun ⟨w, hw⟩ => hsub ⟨ℓov :: w, by rw [hw]; rfl⟩

theorem pdefCond_of_cons {ℓd : Label} {pd : Path Label}
    (h : D.PdefCond (ℓd :: pd)) : D.PdefCond pd := by
  rcases h with heq | hout
  · obtain ⟨-, rfl⟩ : ℓd = D.reserved ∧ pd = [] := by simpa [reservedRoot] using heq
    exact pdefCond_nil D
  · cases pd with
    | nil => exact pdefCond_nil D
    | cons a pd' =>
        exact Or.inr fun ⟨w, hw⟩ => hout ⟨ℓd :: w, by rw [hw]; rfl⟩

/-- Appending a reserved-free projection list to a non-synthetic current path
that is not the reserved root cannot create a synthetic path (structural
fact (iii), literal-resolution insulation). -/
theorem append_not_synthetic {wref pcur : Path Label}
    (hres : D.reserved ∉ wref) (hcur : ¬ D.Synthetic pcur) (hne : pcur ≠ D.reservedRoot) :
    ¬ D.Synthetic (wref ++ pcur) := by
  rintro ⟨w, heq⟩
  cases pcur with
  | nil =>
      rw [List.append_nil] at heq
      exact hres (by rw [heq]; simp [sigma])
  | cons a pcur' =>
      cases pcur' with
      | nil =>
          have heq' : wref ++ [a] = (w ++ [D.mergedTwice]) ++ [D.reserved] := by
            simpa [sigma, List.append_assoc] using heq
          obtain ⟨-, ha⟩ := List.append_inj' heq' rfl
          obtain rfl : a = D.reserved := by simpa using ha
          exact hne rfl
      | cons b t =>
          have hwlen : wref.length ≤ w.length := by
            have hlen := congrArg List.length heq
            simp [sigma] at hlen
            omega
          have h1 : (wref ++ (a :: b :: t)).drop wref.length = a :: b :: t :=
            List.drop_left
          have h2 : (w ++ D.sigma).drop wref.length
              = w.drop wref.length ++ D.sigma :=
            List.drop_append_of_le_length hwlen
          have hdrop : a :: b :: t = w.drop wref.length ++ D.sigma := by
            rw [← h1, heq, h2]
          exact hcur ⟨w.drop wref.length, hdrop⟩

theorem not_synthetic_of_not_inSubtree {v : Path Label} (hv : ¬ D.InSubtree v) :
    ¬ D.Synthetic v := by
  rintro ⟨w, rfl⟩
  exact hv ⟨w ++ [D.mergedTwice], by simp [sigma]⟩

theorem base_not_synthetic : ¬ D.Synthetic D.p₁ := by
  rintro ⟨w, heq⟩
  exact D.base_outside ⟨w ++ [D.mergedTwice], by rw [heq]; simp [sigma]⟩

theorem phi_p₁ : D.phi D.p₁ = D.p₁ := phi_of_not_synthetic D (base_not_synthetic D)

/-! ## Stage B3: auxiliary inversion lemmas -/

theorem overrides_target_nil {q : Path Label} (h : Overrides D.Inh q []) : q = [] := by
  cases h with
  | overridesRoot => rfl

theorem supers_override_nil {q c : Path Label} (h : Supers D.Inh q c []) : q = [] := by
  cases h with
  | supersRoot => rfl
  | supersStep hchain hov => exact absurd (overrides_target_nil D hov) (by simp)

theorem written_cons_not_synthetic {ℓ : Label} {pbr : Path Label}
    (hdom : (ℓ :: pbr) ∈ Dom D.Inh) : ¬ D.Synthetic pbr := by
  rintro ⟨w, rfl⟩
  exact synExt_notMem_dom D (w := ℓ :: w) (by simp) hdom

/-! ## Stage B3: the simulation (paper clauses (C1)–(C4)), `σ → p₁` -/

/-- `σ` never satisfies `PdefCond`: it is not the reserved root (a shorter
list) and it does lie in the reserved subtree. Consequently a `PdefCond`
override can never equal `σ`, which is exactly what keeps the rewriting map
`φ` coherent with `cons`-decomposition throughout the simulation below. -/
theorem not_pdefCond_sigma : ¬ D.PdefCond D.sigma := by
  rintro (heq | hout)
  · exact absurd heq (by simp [sigma, reservedRoot])
  · exact hout ⟨[D.mergedTwice], by simp [sigma]⟩

/-- The simulation motive over one `Fact` derivation: every coordinate's
`φ`-image is derivable, together with the reserved-root bookkeeping that
keeps the induction closed (structural fact (iii)): override components
equal to the reserved root force the query onto the reserved root, `bases`
never targets the reserved root, the reflexive override of `σ` is preserved,
and walks match only `PdefCond` definition sites and never output the
reserved root. The `.supers` clause carries both an unconditional existential
witness (used to reconstruct further overrides/supers facts, where the exact
site does not matter) and a conditional *pointwise* witness at `D.phi c`,
valid whenever the override `v` is `PdefCond` (used to feed the site into a
further `this`-recursion, where it must match exactly); the two coincide
except when the untranslated site is exactly `σ`, which `not_pdefCond_sigma`
rules out under the `PdefCond` guard. -/
def simMotive : Atom Label → Prop
  | .overrides q v =>
      Overrides D.Inh (D.phi q) (D.phi v) ∧
        (v = D.reservedRoot → q = D.reservedRoot) ∧
        (D.Synthetic v → v = q ∨ v = D.sigma ∧ q = D.sigma)
  | .basesStar q t =>
      Relation.ReflTransGen (Bases D.Inh) (D.phi q) (D.phi t) ∧
        (t = D.reservedRoot → q = D.reservedRoot)
  | .bases q t =>
      Relation.ReflTransGen (Bases D.Inh) (D.phi q) (D.phi t) ∧ t ≠ D.reservedRoot
  | .supers q c v =>
      (∃ c', Supers D.Inh (D.phi q) c' (D.phi v)) ∧
        (D.PdefCond v → Supers D.Inh (D.phi q) (D.phi c) (D.phi v)) ∧
        (D.PdefCond v → c ≠ D.reservedRoot) ∧
        (v = D.reservedRoot → q = D.reservedRoot)
  | .this s pdef n t =>
      D.PdefCond pdef →
        This D.Inh (D.phi s) pdef n (D.phi t) ∧ (0 < n → t ≠ D.reservedRoot)

/-- The paper's clauses (C1)–(C4) as one derivation induction, for the
single root `σ` and the fixed target `p₁`. Unlike the simulation of
`MergeSimulation.lean`, no ground-hop hypothesis is needed: the single-hop
ground fact `bases_sigma`
supplies it directly wherever the query is exactly `σ`. -/
theorem sim {a : Atom Label} (h : Fact D.Inh a) : D.simMotive a := by
  induction h with
  | supersRoot =>
      refine ⟨⟨[], ?_⟩, fun _ => ?_, fun _ => by simp [reservedRoot], fun h => h⟩
      · simp only [phi_nil]; exact Fact.supersRoot
      · simp only [phi_nil]; exact Fact.supersRoot
  | @supersStep ℓq q ℓb site pov hchain hov ihchain ihov =>
      obtain ⟨hchainφ, hchainres⟩ := ihchain
      obtain ⟨hovφ, hovres, -⟩ := ihov
      refine ⟨?_, ?_, ?_, ?_⟩
      · obtain ⟨ℓ₂, c', hc'⟩ :=
          List.exists_cons_of_ne_nil (phi_ne_nil D (show (ℓb :: site) ≠ ([] : Path Label) by simp))
        refine ⟨c', (supers_iff_of_ne_nil D
          (phi_ne_nil D (show (ℓq :: q) ≠ ([] : Path Label) by simp))).mpr ⟨ℓ₂, ?_, ?_⟩⟩
        · rw [← hc']; exact (basesStar_iff_reflTransGen D.Inh).mpr hchainφ
        · rw [← hc']; exact hovφ
      · intro hpov
        have hne : ℓb :: site ≠ D.sigma := by
          intro heq
          have hpoveq : pov = D.sigma := (overrides_sigma D).mp (heq ▸ hov)
          exact not_pdefCond_sigma D (hpoveq ▸ hpov)
        rw [phi_cons_of_ne_root D hne] at hchainφ hovφ
        exact (supers_iff_of_ne_nil D (phi_ne_nil D (show (ℓq :: q) ≠ ([] : Path Label) by simp))).mpr
          ⟨ℓb, (basesStar_iff_reflTransGen D.Inh).mpr hchainφ, hovφ⟩
      · rintro hpc rfl
        cases hov with
        | overridesSelf hsup₀ hdom₀ =>
            rcases hpc with heq | hout
            · exact absurd heq (by simp [reservedRoot])
            · exact hout ⟨[ℓb], rfl⟩
        | overridesBranch hsup₀ hdom₀ =>
            obtain ⟨-, rfl⟩ := (supers_reservedRoot D).mp hsup₀
            rcases hpc with heq | hout
            · exact absurd heq (by simp [reservedRoot])
            · exact hout ⟨[ℓb], rfl⟩
      · intro hres
        obtain ⟨rfl, rfl⟩ : ℓb = D.reserved ∧ site = [] := by
          simpa [reservedRoot] using hovres hres
        exact hchainres rfl
  | overridesRoot =>
      refine ⟨?_, fun h => absurd h (by simp [reservedRoot]),
        fun h => absurd h (not_synthetic_nil D)⟩
      rw [phi_nil]
      exact Fact.overridesRoot
  | @overridesSelf p c pbr ℓ hsup hdom ihsup =>
      obtain ⟨⟨c₀, hsupφ⟩, -, -, -⟩ := ihsup
      refine ⟨?_, fun h => h, fun _ => Or.inl rfl⟩
      by_cases hroot : ℓ :: p = D.sigma
      · rw [hroot, phi_sigma D]
        exact overrides_p₁_self D
      · rw [phi_cons_of_ne_root D hroot]
        rw [phi_of_not_synthetic D (written_cons_not_synthetic D hdom)] at hsupφ
        exact Fact.overridesSelf hsupφ hdom
  | @overridesBranch p c pbr ℓ hsup hdom ihsup =>
      obtain ⟨⟨c₀, hsupφ⟩, -, hsupsite, hsupres⟩ := ihsup
      refine ⟨?_, ?_, ?_⟩
      · by_cases hroot : ℓ :: p = D.sigma
        · obtain ⟨rfl, rfl⟩ : ℓ = D.mergedTwice ∧ p = D.reservedRoot := by simpa [sigma] using hroot
          obtain ⟨-, rfl⟩ := (supers_reservedRoot D).mp hsup
          rw [show (D.mergedTwice :: D.reservedRoot : Path Label) = D.sigma from rfl, phi_sigma D]
          exact overrides_p₁_self D
        · rw [phi_cons_of_ne_root D hroot]
          by_cases hroot₂ : ℓ :: pbr = D.sigma
          · exfalso
            obtain ⟨rfl, rfl⟩ : ℓ = D.mergedTwice ∧ pbr = D.reservedRoot := by
              simpa [sigma] using hroot₂
            exact hroot (by rw [hsupres rfl])
          · rw [phi_cons_of_ne_root D hroot₂]
            have hpbrφ : D.phi pbr = pbr :=
              phi_of_not_synthetic D (written_cons_not_synthetic D hdom)
            rw [hpbrφ] at hsupφ ⊢
            exact Fact.overridesBranch hsupφ hdom
      · intro hres
        obtain ⟨rfl, rfl⟩ : ℓ = D.reserved ∧ pbr = [] := by simpa [reservedRoot] using hres
        rw [supers_override_nil D hsup]
      · intro hsynv
        obtain ⟨w, heqv⟩ := hsynv
        cases w with
        | cons a w' =>
            exfalso
            apply written_cons_not_synthetic D hdom
            obtain ⟨-, rfl⟩ : ℓ = a ∧ pbr = w' ++ D.sigma := by simpa using heqv
            exact ⟨w', rfl⟩
        | nil =>
            obtain ⟨rfl, rfl⟩ : ℓ = D.mergedTwice ∧ pbr = D.reservedRoot := by
              simpa [sigma] using heqv
            exact Or.inr ⟨by simp [sigma], by rw [hsupres rfl]⟩
  | @basesStep p pcur ℓ ℓov povt n wref hov href hthis ihov ihthis =>
      have hpovdom : (ℓov :: povt) ∈ Dom D.Inh := href.mem_dom
      have hpovt : D.PdefCond povt := pdefCond_tail_of_written D hpovdom
      obtain ⟨hovφ, hovres, hovsyn⟩ := ihov
      obtain ⟨hthisφ, hthisres⟩ := ihthis hpovt
      have hwres : D.reserved ∉ wref := by
        obtain ⟨Sr, hSr, hr⟩ := href
        exact D.reserved_not_in_references _ _ hSr _ hr
      have hpcur_ne : pcur ≠ D.reservedRoot := by
        intro hcr
        cases n with
        | succ n' => exact absurd hcr (hthisres (by omega))
        | zero =>
            have hp : p = D.reservedRoot := by
              rw [← (this_zero_iff D.Inh).mp hthis]
              exact hcr
            subst hp
            have hpov_syn : ℓov :: povt = ℓ :: D.reservedRoot := by
              cases hov with
              | overridesSelf _ _ => rfl
              | overridesBranch hsup₀ _ =>
                  obtain ⟨-, rfl⟩ := (supers_reservedRoot D).mp hsup₀
                  rfl
            have hpovdom' : (ℓ :: D.reservedRoot) ∈ Dom D.Inh := hpov_syn ▸ hpovdom
            rcases D.reserved_subtree _ hpovdom' ⟨[ℓ], rfl⟩ with heq | heq
            · exact absurd heq (by simp)
            · have href' : MemRef D.Inh (0, wref) (ℓ :: D.reservedRoot) := hpov_syn ▸ href
              rw [heq] at href'
              obtain ⟨Sr, hSr, hr⟩ := href'
              rw [D.inh_sigma] at hSr
              cases hSr
              simp at hr
      have htne : wref ++ pcur ≠ D.reservedRoot := by
        cases wref with
        | nil => simpa using hpcur_ne
        | cons a w' =>
            intro hcr
            have ha : a = D.reserved := by
              have hh := congrArg (fun l => l.head?) hcr
              simpa [reservedRoot] using hh
            exact hwres (ha ▸ List.Mem.head _)
      by_cases hroot : ℓ :: p = D.sigma
      · have hb : Bases D.Inh D.sigma (wref ++ pcur) := hroot ▸ Fact.basesStep hov href hthis
        have hwp : wref ++ pcur = D.p₁ := (bases_sigma D).mp hb
        refine ⟨?_, htne⟩
        rw [hroot, phi_sigma D, hwp, phi_p₁ D]
      · have hpov_ns : ¬ D.Synthetic (ℓov :: povt) := by
          intro hsyn
          rcases hovsyn hsyn with heqv | ⟨-, hq⟩
          · exact hroot (heqv ▸ written_synthetic D (heqv ▸ hpovdom) (heqv ▸ hsyn))
          · exact hroot hq
        have hpovφ : D.phi (ℓov :: povt) = ℓov :: povt := phi_of_not_synthetic D hpov_ns
        have hcons := phi_cons_of_ne_root D hroot
        rw [hcons, hpovφ] at hovφ
        have hstep' := Fact.basesStep hovφ href hthisφ
        have happ : D.phi (wref ++ pcur) = wref ++ D.phi pcur := by
          by_cases hcur : D.Synthetic pcur
          · obtain ⟨wc, rfl⟩ := hcur
            exact phi_append_of_synthetic D wc wref
          · rw [phi_of_not_synthetic D hcur]
            by_cases hcr : pcur = D.reservedRoot
            · exact absurd hcr hpcur_ne
            · exact phi_of_not_synthetic D (append_not_synthetic D hwres hcur hcr)
        refine ⟨?_, htne⟩
        rw [hcons, happ]
        exact Relation.ReflTransGen.single hstep'
  | basesStarRefl q =>
      exact ⟨Relation.ReflTransGen.refl, fun h => h⟩
  | @basesStarTail q r t hchain hstep ihchain ihstep =>
      obtain ⟨hcφ, hcres⟩ := ihchain
      obtain ⟨hsφ, hsres⟩ := ihstep
      exact ⟨hcφ.trans hsφ, fun h => absurd h hsres⟩
  | thisZero s pdef =>
      exact fun _ => ⟨Fact.thisZero _ _, fun h0 => absurd h0 (by omega)⟩
  | @thisSucc s psite t ℓd pd n hsup hrec ihsup ihrec =>
      intro hpdef
      obtain ⟨-, hsuppt, hsupsite, -⟩ := ihsup
      have hsupφ := hsuppt hpdef
      have hpdefφ : D.phi (ℓd :: pd) = ℓd :: pd := phi_of_pdefCond D hpdef
      have hpd : D.PdefCond pd := pdefCond_of_cons D hpdef
      obtain ⟨hrecφ, hrecres⟩ := ihrec hpd
      rw [hpdefφ] at hsupφ
      refine ⟨Fact.thisSucc hsupφ hrecφ, fun _ => ?_⟩
      cases n with
      | zero =>
          obtain rfl := (this_zero_iff D.Inh).mp hrec
          exact hsupsite hpdef
      | succ n' => exact hrecres (by omega)

/-! ## Stage B4 (partial): the `σ → p₁` transfer -/

/-- One direction of the transfer: an outside-subtree override component of
`supers` at `w ++ σ` reappears at the same extension `w ++ p₁` of the base. -/
theorem supers_transfer {w : Path Label} {c v : Path Label}
    (hsup : Supers D.Inh (w ++ D.sigma) c v) (hv : ¬ D.InSubtree v) :
    ∃ c', Supers D.Inh (w ++ D.p₁) c' v := by
  have hpdef : D.PdefCond v := Or.inr hv
  have h := (D.sim hsup).2.1 hpdef
  rw [phi_of_synthetic D w, phi_of_not_synthetic D (not_synthetic_of_not_inSubtree D hv)] at h
  exact ⟨_, h⟩

/-- Existence transfers unconditionally: any `supers` pair maps over. -/
theorem supers_nonempty_transfer {w : Path Label}
    (h : (supersSet D.Inh (w ++ D.sigma)).Nonempty) :
    (supersSet D.Inh (w ++ D.p₁)).Nonempty := by
  obtain ⟨⟨c, v⟩, hsup⟩ := h
  obtain ⟨c', hc'⟩ := (D.sim (hsup : Supers D.Inh _ c v)).1
  rw [phi_of_synthetic D w] at hc'
  exact ⟨(_, _), hc'⟩

/-! ## Stage B3′: anchored derivability, `p₁ → σ`

No global rewriting map exists on this side: a fixed reference may resolve
literally to a spine path `p₁ ⌢ u`, and such occurrences must stay as they
are. Instead of rewriting facts, the motive `simMotive2` below *asserts
derivability at the anchors*: whenever an atom's query is a suffix extension
`w ++ p₁` of the base, a corresponding σ-side fact is derivable. Off-spine
atoms carry a vacuously true obligation, so the induction passes through
everywhere except at spine positions.

The two spine helpers come first: a written spine extension is an override
of the corresponding wrapper extension (`spine_override`), because the
branch production climbs the spine down to the ground facts, using prefix
closure at every step. This is the fact whose absence blocked a naive port
of the forward simulation: the σ-side counterpart of a *reflexively*
produced, written override `w ++ p₁` is that same path, reached as a branch
override of `w ++ σ`, not the σ-spine image `w ++ σ` itself. -/

/-- `w ++ p₁` is never the root: `p₁` is nonempty. -/
theorem append_p₁_ne_nil (w : Path Label) : w ++ D.p₁ ≠ [] := by
  intro h
  exact D.base_nonempty (List.append_eq_nil_iff.mp h).2

/-- `w ++ σ` is never the root: `σ` is nonempty. -/
theorem append_sigma_ne_nil (w : Path Label) : w ++ D.sigma ≠ [] := by
  simp [sigma]

/-- Every suffix extension of the wrapper root inherits the corresponding
spine extension of the base, provided the extended base paths are written
along the way (paper clauses (C1′)/(C3′), ground form): by induction on the
suffix, the reflexive `bases*` endpoint of `u ++ σ` carries the branch
override `u ++ p₁` produced by the one-shorter instance, and at the empty
suffix the ground facts give `supers σ ⊇ supers p₁ ∋ (init p₁, p₁)` via
`overrides_p₁_self`. -/
theorem spine_supers :
    ∀ u : Path Label, (u ≠ [] → (u ++ D.p₁) ∈ Dom D.Inh) →
      ∃ c, Supers D.Inh (u ++ D.sigma) c (u ++ D.p₁) := by
  intro u
  induction u with
  | nil =>
      intro _
      obtain ⟨ℓ₁, t₁, hp₁⟩ := List.exists_cons_of_ne_nil D.base_nonempty
      refine ⟨t₁, ?_⟩
      simp only [List.nil_append]
      refine (supers_sigma D).mpr (Or.inr ?_)
      rw [hp₁]
      exact Fact.supersStep (Fact.basesStarRefl _) (hp₁ ▸ overrides_p₁_self D)
  | cons ℓ u₀ ih =>
      intro hdom
      have hdom' : ((ℓ :: u₀) ++ D.p₁) ∈ Dom D.Inh := hdom (by simp)
      obtain ⟨c₀, hsup₀⟩ := ih fun _ => D.prefix_closed ℓ (u₀ ++ D.p₁) hdom'
      exact ⟨u₀ ++ D.sigma,
        Fact.supersStep (Fact.basesStarRefl ((ℓ :: u₀) ++ D.sigma))
          (Fact.overridesBranch hsup₀ hdom')⟩

/-- A *written* nonempty spine extension is an override of the corresponding
wrapper extension. (At the empty extension this is false: `overrides σ`
contains only `σ`, never `p₁`; the empty case is instead handled by the
ground hop `bases σ = {p₁}` wherever `sim2` needs it.) -/
theorem spine_override {ℓ : Label} {u : Path Label}
    (hdom : ((ℓ :: u) ++ D.p₁) ∈ Dom D.Inh) :
    Overrides D.Inh ((ℓ :: u) ++ D.sigma) ((ℓ :: u) ++ D.p₁) := by
  obtain ⟨c₀, hsup₀⟩ := spine_supers D u fun _ => D.prefix_closed ℓ _ hdom
  exact Fact.overridesBranch hsup₀ hdom

/-- The anchored motive of the `p₁ → σ` direction (paper clauses
(C1′)–(C4′)). Each clause is guarded by the query being a spine extension:

- `.overrides` (C1′): a *written* override of a nonempty spine extension is
  derivable as an override of the wrapper extension. Writtenness is
  essential (the reflexive override can be produced unwritten, and then has
  no σ-side counterpart; this is why the final theorem compares written
  components only), and so is nonemptiness of the extension
  (`overrides σ = {σ}` alone).
- `.basesStar`/`.bases` (C2′): a chain from `w ++ p₁` has a σ-side chain
  from `w ++ σ` reaching either the same endpoint or the σ-spine image
  `u ++ σ` of a spine endpoint `u ++ p₁`.
- `.supers` (C3′): a `supers` pair at `w ++ p₁` with *written* override
  component transfers to `w ++ σ` with the same override component; the
  site component is preserved or replaced by its σ-spine image, which is
  exactly what the walk transfer needs.
- `.this` (C4′): walks anchored at spine sites transfer, for *written*
  matched definition paths (prefix closure keeps definition paths written
  through the recursion); the output is preserved or replaced by its
  σ-spine image. -/
def simMotive2 : Atom Label → Prop
  | .overrides q v =>
      ∀ (ℓ : Label) (u : Path Label), q = (ℓ :: u) ++ D.p₁ → v ∈ Dom D.Inh →
        Overrides D.Inh ((ℓ :: u) ++ D.sigma) v
  | .basesStar q t =>
      ∀ w, q = w ++ D.p₁ →
        Relation.ReflTransGen (Bases D.Inh) (w ++ D.sigma) t ∨
          ∃ u, t = u ++ D.p₁ ∧
            Relation.ReflTransGen (Bases D.Inh) (w ++ D.sigma) (u ++ D.sigma)
  | .bases q t =>
      ∀ w, q = w ++ D.p₁ →
        Relation.ReflTransGen (Bases D.Inh) (w ++ D.sigma) t ∨
          ∃ u, t = u ++ D.p₁ ∧
            Relation.ReflTransGen (Bases D.Inh) (w ++ D.sigma) (u ++ D.sigma)
  | .supers q c v =>
      ∀ w, q = w ++ D.p₁ → v ∈ Dom D.Inh →
        ∃ c', (c' = c ∨ ∃ u, c = u ++ D.p₁ ∧ c' = u ++ D.sigma) ∧
          Supers D.Inh (w ++ D.sigma) c' v
  | .this s pdef n t =>
      ∀ w, s = w ++ D.p₁ → pdef ∈ Dom D.Inh →
        ∃ t', (t' = t ∨ ∃ u, t = u ++ D.p₁ ∧ t' = u ++ D.sigma) ∧
          This D.Inh (w ++ D.sigma) pdef n t'

/-- The paper's clauses (C1′)–(C4′) as one derivation induction. Where the
forward `sim` rewrites every coordinate through `φ`, this direction only
asserts derivability at the spine anchors; a σ-side chain ending on the
σ-spine (`u ++ σ`) is realigned at consumption time, either by the ground
hop `bases σ = {p₁}` (empty suffix) or by `spine_override` and the
(C1′)/(C3′) transfers (nonempty suffix, written components). -/
theorem sim2 {a : Atom Label} (h : Fact D.Inh a) : D.simMotive2 a := by
  induction h with
  | supersRoot =>
      intro wa heq _
      exact absurd heq.symm (append_p₁_ne_nil D wa)
  | @supersStep ℓq q ℓb site pov hchain hov ihchain ihov =>
      intro wa heq hvdom
      rcases ihchain wa heq with hchainσ | ⟨u, hendpt, hchainσ⟩
      · exact ⟨site, Or.inl rfl,
          (supers_iff_of_ne_nil D (append_sigma_ne_nil D wa)).mpr
            ⟨ℓb, (basesStar_iff_reflTransGen D.Inh).mpr hchainσ, hov⟩⟩
      · cases u with
        | nil =>
            simp only [List.nil_append] at hendpt hchainσ
            have hchainσ' : Relation.ReflTransGen (Bases D.Inh)
                (wa ++ D.sigma) (ℓb :: site) :=
              hchainσ.tail (by rw [hendpt]; exact (bases_sigma D).mpr rfl)
            exact ⟨site, Or.inl rfl,
              (supers_iff_of_ne_nil D (append_sigma_ne_nil D wa)).mpr
                ⟨ℓb, (basesStar_iff_reflTransGen D.Inh).mpr hchainσ', hov⟩⟩
        | cons ℓu u₀ =>
            obtain ⟨rfl, rfl⟩ : ℓb = ℓu ∧ site = u₀ ++ D.p₁ := by
              simpa using hendpt
            have hovσ : Overrides D.Inh ((ℓb :: u₀) ++ D.sigma) pov :=
              ihov ℓb u₀ rfl hvdom
            exact ⟨u₀ ++ D.sigma, Or.inr ⟨u₀, rfl, rfl⟩,
              (supers_iff_of_ne_nil D (append_sigma_ne_nil D wa)).mpr
                ⟨ℓb, (basesStar_iff_reflTransGen D.Inh).mpr hchainσ, hovσ⟩⟩
  | overridesRoot =>
      intro ℓa ua heq _
      exact absurd heq.symm (by simp)
  | @overridesSelf p c pbr ℓ _ _ _ =>
      intro ℓa ua heq hvdom
      obtain ⟨rfl, rfl⟩ : ℓ = ℓa ∧ p = ua ++ D.p₁ := by simpa using heq
      exact spine_override D hvdom
  | @overridesBranch p c pbr ℓ hsup hdom ihsup =>
      intro ℓa ua heq _
      obtain ⟨rfl, rfl⟩ : ℓ = ℓa ∧ p = ua ++ D.p₁ := by simpa using heq
      obtain ⟨c', -, hsupσ⟩ := ihsup ua rfl (D.prefix_closed _ _ hdom)
      exact Fact.overridesBranch hsupσ hdom
  | @basesStep p pcur ℓ ℓov povt n wref hov href hthis ihov ihthis =>
      intro wa heq
      have hpovdom : (ℓov :: povt) ∈ Dom D.Inh := href.mem_dom
      have hpovtdom : povt ∈ Dom D.Inh := D.prefix_closed _ _ hpovdom
      cases wa with
      | nil =>
          simp only [List.nil_append] at heq ⊢
          left
          have hop1 : Bases D.Inh D.sigma (ℓ :: p) := by
            rw [heq]
            exact (bases_sigma D).mpr rfl
          exact (Relation.ReflTransGen.single hop1).tail
            (Fact.basesStep hov href hthis)
      | cons ℓw w₀ =>
          obtain ⟨rfl, rfl⟩ : ℓ = ℓw ∧ p = w₀ ++ D.p₁ := by simpa using heq
          have hovσ : Overrides D.Inh ((ℓ :: w₀) ++ D.sigma) (ℓov :: povt) :=
            ihov ℓ w₀ rfl hpovdom
          obtain ⟨pcur', halign, hthisσ⟩ := ihthis w₀ rfl hpovtdom
          have hstepσ : Bases D.Inh ((ℓ :: w₀) ++ D.sigma) (wref ++ pcur') :=
            Fact.basesStep hovσ href hthisσ
          rcases halign with rfl | ⟨u, rfl, rfl⟩
          · exact Or.inl (Relation.ReflTransGen.single hstepσ)
          · refine Or.inr ⟨wref ++ u, by rw [List.append_assoc], ?_⟩
            rw [List.append_assoc]
            exact Relation.ReflTransGen.single hstepσ
  | basesStarRefl q =>
      intro wa heq
      exact Or.inr ⟨wa, heq, Relation.ReflTransGen.refl⟩
  | @basesStarTail q r t hchain hstep ihchain ihstep =>
      intro wa heq
      rcases ihchain wa heq with hchainσ | ⟨u, rfl, hchainσ⟩
      · exact Or.inl (hchainσ.tail hstep)
      · rcases ihstep u rfl with hstepσ | ⟨u', rfl, hstepσ⟩
        · exact Or.inl (hchainσ.trans hstepσ)
        · exact Or.inr ⟨u', rfl, hchainσ.trans hstepσ⟩
  | thisZero s pdef =>
      intro wa heq _
      exact ⟨wa ++ D.sigma, Or.inr ⟨wa, heq, rfl⟩, Fact.thisZero _ _⟩
  | @thisSucc s psite t ℓd pd n hsup hrec ihsup ihrec =>
      intro wa heq hpdefdom
      obtain ⟨c', halign, hsupσ⟩ := ihsup wa heq hpdefdom
      rcases halign with rfl | ⟨u, rfl, rfl⟩
      · exact ⟨t, Or.inl rfl, Fact.thisSucc hsupσ hrec⟩
      · obtain ⟨t', ht', hrecσ⟩ := ihrec u rfl (D.prefix_closed _ _ hpdefdom)
        exact ⟨t', ht', Fact.thisSucc hsupσ hrecσ⟩

/-! ## Stage B4: the idempotence theorem -/

/-- **thm:merge-idempotent**: for every path suffix `w`, the sets of
*written*, outside-subtree override components of `supers` agree at the
extension `w ++ σ` of the composition of `p₁` with itself (reversed
representation of the paper's `σ ⌢ w`, with
`σ = D.sigma = [mergedTwice, reserved]`) and at the base extension
`w ++ p₁`. Composing a written, existing mixin with itself is unobservable
outside the reserved subtree, on written components.

The restriction to *written* components (`v ∈ Dom D.Inh`, absent from
`merge_associative` and `merge_commutative`) is genuine: eq:overrides
produces the reflexive override of `p₁ ⌢ w` under the guard that some
written branch qualifies, whether or not that path itself is written, so an
unwritten reflexive override can appear on the base side with no
wrapper-side counterpart. -/
theorem merge_idempotent (w : Path Label) {v : Path Label}
    (hdom : v ∈ Dom D.Inh) (hv : ¬ D.InSubtree v) :
    (∃ c, Supers D.Inh (w ++ D.sigma) c v) ↔
      (∃ c, Supers D.Inh (w ++ D.p₁) c v) := by
  constructor
  · rintro ⟨c, hsup⟩
    exact supers_transfer D hsup hv
  · rintro ⟨c, hsup⟩
    obtain ⟨c', -, hsupσ⟩ := D.sim2 hsup w rfl hdom
    exact ⟨c', hsupσ⟩

/-- thm:merge-idempotent, existence part: the wrapper extension and the base
extension exist together (nonempty `supers`, Section "Semantic Functions").
The backward direction goes through the Path Existence Lemma: a qualifying
branch at `w₀ ++ p₁` is written by prefix closure, hence transfers to
`w₀ ++ σ` by the (C3′) clause of `sim2`, and the existence criterion reads
only the transferred branch. -/
theorem merge_idempotent_exists (w : Path Label) :
    (supersSet D.Inh (w ++ D.sigma)).Nonempty ↔
      (supersSet D.Inh (w ++ D.p₁)).Nonempty := by
  constructor
  · exact supers_nonempty_transfer D
  · intro h
    cases w with
    | nil =>
        exact ⟨(D.reservedRoot, D.sigma),
          (supers_sigma D).mpr (Or.inl ⟨rfl, rfl⟩)⟩
    | cons ℓ w₀ =>
        rw [show (ℓ :: w₀) ++ D.p₁ = ℓ :: (w₀ ++ D.p₁) from rfl,
          supersSet_cons_nonempty_iff] at h
        obtain ⟨c, pbr, hsup, hdom⟩ := h
        obtain ⟨c', -, hsupσ⟩ := D.sim2 hsup w₀ rfl (D.prefix_closed _ _ hdom)
        rw [show (ℓ :: w₀) ++ D.sigma = ℓ :: (w₀ ++ D.sigma) from rfl,
          supersSet_cons_nonempty_iff]
        exact ⟨c', pbr, hsupσ, hdom⟩

end IdempotenceDocument

end InheritanceCalculus
