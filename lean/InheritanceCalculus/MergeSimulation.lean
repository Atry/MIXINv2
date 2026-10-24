import InheritanceCalculus.PathExistence

/-!
# The simulation behind associativity and commutativity

The paper proves associativity (thm:merge-associative) and commutativity
(thm:merge-commutative) of deep merge by one simulation (Appendix "Algebraic
Properties of Deep Merge"): a map `φ` that sends the extensions of some
synthetic roots to the same extensions of another synthetic root carries
every fact of the least fixed point, by a strong induction on Kleene rank
with last-step inversion. This file proves that simulation once, for an
arbitrary family of wrappers named under a reserved label;
`MergeAssociativity.lean` and `MergeCommutativity.lean` instantiate it with
the wrappers of the two theorems. (Idempotence, thm:merge-idempotent, compares
a wrapper with a *fixed* path instead, and has its own simulation in
`MergeIdempotence.lean`.)

## Setting, without the syntax layer

The syntax layer is out of scope, so the family is axiomatized as conditions
on the abstract primitive `Inh`, bundled in `WrapperFamily`:

- the reserved root `[reserved]` is written with no references;
- every wrapper label `X` names a written synthetic root `[X, reserved]`
  whose references are `[p]`-style references to a base, de-Bruijn `(1, p)`
  (one walk step out of the reserved scope to the top level, then project
  `p`), or `[Y]`-style references to a wrapper, `(0, [Y])`;
- nothing else is written inside the reserved subtree (in the reversed path
  representation, "inside the subtree" is "the last list element is
  `reserved`");
- the reserved label occurs in no reference's projection list;
- the bases are nonempty, outside the reserved subtree, and their first
  labels are no wrapper labels.

## Structure

- B1 (ground facts): `overrides`/`bases`/`supers` at the reserved root and
  the synthetic roots by direct equation computation ("chain flattening").
- B2 (structural facts (i) and (iii)): definedness of `inherits` on synthetic
  paths; insulation of walks and literal resolution; classification of the
  rewriting map `φ`.
- B3 (simulation): the paper's clauses (C1)–(C4) as a single structural
  induction over `Fact` derivations with a motive on `Atom` (the paper's
  strong induction on Kleene rank with last-step inversion corresponds to
  the derivation induction, and its inner chain induction to the `basesStar`
  coordinate), for the map `φ` fixed by a set `S` of wrapper labels and a
  target wrapper `Y`. The ground-chain comparison of structural fact (ii) is
  the hypothesis an instance supplies.
- B4 (transfer): the outside-subtree override components of `supers`, and
  existence, carry over from an extension of a synthetic root in `S` to the
  same extension of the synthetic root of `Y`.
-/

set_option warningAsError true

namespace InheritanceCalculus

/-- A family of wrappers named under a reserved label, axiomatized on the
abstract primitive (the common hypothesis part of paper thm:merge-associative
and thm:merge-commutative). Paths are in the reversed representation of
`Basic.lean`, so the paper's synthetic root `(__merge, X)` is `[X, reserved]`
and its extensions are `w ++ [X, reserved]`. -/
structure WrapperFamily (Label : Type*) where
  Inh : Path Label → Option (Set (Reference Label))
  reserved : Label
  /-- The wrapper labels named under the reserved label. -/
  wrappers : Set Label
  /-- The paths the `[p]`-style references of the wrappers point to. -/
  bases : Set (Path Label)
  inh_reserved : Inh [reserved] = some ∅
  /-- Every wrapper is written. -/
  wrapper_written : ∀ X ∈ wrappers, [X, reserved] ∈ Dom Inh
  /-- A wrapper carries `[p]`-style references to bases and `[Y]`-style
  references to wrappers, and nothing else. -/
  wrapper_reference : ∀ X ∈ wrappers, ∀ r, MemRef Inh r [X, reserved] →
    (∃ p ∈ bases, r = (1, p)) ∨ ∃ Y ∈ wrappers, r = (0, [Y])
  /-- Nothing else is written inside the reserved subtree: a written path
  ending in the reserved label is the reserved root or a synthetic root. -/
  reserved_subtree : ∀ q ∈ Dom Inh, (∃ w, q = w ++ [reserved]) →
    q = [reserved] ∨ ∃ X ∈ wrappers, q = [X, reserved]
  /-- The reserved label occurs in no reference's projection list. -/
  reserved_not_in_references : ∀ q S, Inh q = some S →
    ∀ r ∈ S, reserved ∉ r.2
  base_nonempty : ∀ p ∈ bases, p ≠ []
  /-- The bases lie outside the reserved subtree. -/
  base_outside : ∀ p ∈ bases, ¬ ∃ w, p = w ++ [reserved]
  /-- The first label of a base (the outermost, the last element in the
  reversed representation) is no wrapper label. -/
  base_head_not_wrapper : ∀ p ∈ bases, ∀ X ∈ wrappers, ¬ ∃ w, p = w ++ [X]

namespace WrapperFamily

variable {Label : Type*} (F : WrapperFamily Label)

/-- The reserved root, the paper's `p_reserved = (__merge)`. -/
abbrev reservedRoot : Path Label := [F.reserved]

/-- The synthetic root for a wrapper label. -/
abbrev syntheticRoot (X : Label) : Path Label := [X, F.reserved]

/-- A path lies inside the reserved subtree exactly when its outermost label
(the last element in the reversed representation) is the reserved label. -/
def InSubtree (q : Path Label) : Prop := ∃ w, q = w ++ [F.reserved]

/-- A synthetic path of the root set `S`: an extension of a synthetic root
whose wrapper label belongs to `S`. -/
def Synthetic (S : Set Label) (q : Path Label) : Prop :=
  ∃ X ∈ S, ∃ w : Path Label, q = w ++ F.syntheticRoot X

/-- The rewriting map of the simulation: send an extension
`w ++ [X, reserved]` of a synthetic root in `S` to the same extension
`w ++ R'` of the target root `R'`, and leave every other path fixed. The
suffix `w` is recovered from the path itself by dropping the two outermost
labels, so overlapping witnesses agree. -/
noncomputable def phi (S : Set Label) (R' : Path Label) (q : Path Label) :
    Path Label :=
  open Classical in
  if F.Synthetic S q then q.dropLast.dropLast ++ R' else q

theorem phi_of_not_synthetic {S : Set Label} {R' q : Path Label}
    (h : ¬ F.Synthetic S q) : F.phi S R' q = q := by
  simp [phi, h]

theorem phi_of_synthetic {S : Set Label} {R' : Path Label} {X : Label}
    (hX : X ∈ S) (w : Path Label) :
    F.phi S R' (w ++ F.syntheticRoot X) = w ++ R' := by
  have hsyn : F.Synthetic S (w ++ F.syntheticRoot X) := ⟨X, hX, w, rfl⟩
  have hdrop : (w ++ F.syntheticRoot X).dropLast.dropLast = w := by
    show (w ++ [X, F.reserved]).dropLast.dropLast = w
    rw [show w ++ [X, F.reserved] = (w ++ [X]) ++ [F.reserved] by simp,
      List.dropLast_concat, List.dropLast_concat]
  simp only [phi]
  rw [if_pos hsyn, hdrop]

/-- `φ` commutes with extension by a further suffix on synthetic paths. -/
theorem phi_append_of_synthetic {S : Set Label} {R' : Path Label} {X : Label}
    (hX : X ∈ S) (w v : Path Label) :
    F.phi S R' (v ++ (w ++ F.syntheticRoot X)) =
      v ++ F.phi S R' (w ++ F.syntheticRoot X) := by
  rw [phi_of_synthetic F hX,
    show v ++ (w ++ F.syntheticRoot X) = (v ++ w) ++ F.syntheticRoot X by simp,
    phi_of_synthetic F hX, List.append_assoc]

/-! ## Stage B1: ground facts at the reserved root ("chain flattening") -/

theorem overrides_reservedRoot {pov : Path Label} :
    Overrides F.Inh F.reservedRoot pov ↔ pov = F.reservedRoot := by
  constructor
  · intro h
    rcases (overrides_cons_iff F.Inh).mp h with ⟨c, pbr, hsup, hdom, hor⟩
    obtain ⟨rfl, rfl⟩ := (supers_nil_iff F.Inh).mp hsup
    rcases hor with rfl | rfl <;> rfl
  · rintro rfl
    exact Fact.overridesSelf Fact.supersRoot (by simp [Dom, F.inh_reserved])

theorem not_bases_reservedRoot {t : Path Label} :
    ¬ Bases F.Inh F.reservedRoot t := by
  intro h
  rcases (bases_cons_iff F.Inh).mp h with ⟨pov, hov, n, w, href, -⟩
  rw [overrides_reservedRoot F] at hov
  subst hov
  obtain ⟨S, hS, hr⟩ := href
  rw [F.inh_reserved] at hS
  cases hS
  exact hr

theorem basesStar_reservedRoot {pb : Path Label}
    (h : BasesStar F.Inh F.reservedRoot pb) : pb = F.reservedRoot := by
  have h' := (basesStar_iff_reflTransGen F.Inh).mp h
  clear h
  induction h' with
  | refl => rfl
  | tail _ hstep ih =>
      subst ih
      exact absurd hstep (not_bases_reservedRoot F)

theorem supers_reservedRoot {c pov : Path Label} :
    Supers F.Inh F.reservedRoot c pov ↔ c = [] ∧ pov = F.reservedRoot := by
  constructor
  · intro h
    rcases (supers_cons_iff F.Inh).mp h with ⟨ℓb, hchain, hov⟩
    obtain ⟨rfl, rfl⟩ : ℓb = F.reserved ∧ c = [] := by
      simpa using basesStar_reservedRoot F hchain
    rw [overrides_reservedRoot F] at hov
    exact ⟨rfl, hov⟩
  · rintro ⟨rfl, rfl⟩
    exact Fact.supersStep (Fact.basesStarRefl _)
      ((overrides_reservedRoot F).mpr rfl)

theorem syntheticRoot_mem_dom {X : Label} (hX : X ∈ F.wrappers) :
    F.syntheticRoot X ∈ Dom F.Inh :=
  F.wrapper_written X hX

theorem overrides_syntheticRoot {X : Label} (hX : X ∈ F.wrappers)
    {pov : Path Label} :
    Overrides F.Inh (F.syntheticRoot X) pov ↔ pov = F.syntheticRoot X := by
  constructor
  · intro h
    rcases (overrides_cons_iff F.Inh).mp h with ⟨c, pbr, hsup, hdom, hor⟩
    obtain ⟨rfl, rfl⟩ := (supers_reservedRoot F).mp hsup
    rcases hor with rfl | rfl <;> rfl
  · rintro rfl
    exact Fact.overridesSelf ((supers_reservedRoot F).mpr ⟨rfl, rfl⟩)
      (syntheticRoot_mem_dom F hX)

/-- The one walk step of a `[p]`-style reference consumes exactly the shared
pair `((), p_reserved)`. -/
theorem this_reserved_one {pcur : Path Label} :
    This F.Inh F.reservedRoot F.reservedRoot 1 pcur ↔ pcur = [] := by
  constructor
  · intro h
    rcases (this_succ_iff F.Inh).mp h with ⟨psite, hsup, hrec⟩
    obtain ⟨rfl, -⟩ := (supers_reservedRoot F).mp hsup
    exact (this_zero_iff F.Inh).mp hrec
  · rintro rfl
    exact Fact.thisSucc ((supers_reservedRoot F).mpr ⟨rfl, rfl⟩)
      (Fact.thisZero _ _)

/-! ## Stage B1 (continued): bases at the synthetic roots -/

/-- A `[label]`-style reference (index 0) written at a synthetic root
resolves inside the reserved scope. -/
theorem resolve_syntheticRoot_zero {X : Label} {w t : Path Label} :
    Resolve F.Inh F.reservedRoot (F.syntheticRoot X) 0 w t ↔
      t = w ++ F.reservedRoot := by
  constructor
  · rintro ⟨ℓd, pd, heq, pcur, hthis, rfl⟩
    obtain ⟨rfl, rfl⟩ : X = ℓd ∧ F.reservedRoot = pd := by simpa using heq
    rw [(this_zero_iff F.Inh).mp hthis]
  · rintro rfl
    exact ⟨X, F.reservedRoot, rfl, F.reservedRoot, Fact.thisZero _ _, rfl⟩

/-- A `[p]`-style reference (index 1) written at a synthetic root resolves
at the top level. -/
theorem resolve_syntheticRoot_one {X : Label} {w t : Path Label} :
    Resolve F.Inh F.reservedRoot (F.syntheticRoot X) 1 w t ↔ t = w := by
  constructor
  · rintro ⟨ℓd, pd, heq, pcur, hthis, rfl⟩
    obtain ⟨rfl, rfl⟩ : X = ℓd ∧ F.reservedRoot = pd := by simpa using heq
    rw [(this_reserved_one F).mp hthis, List.append_nil]
  · rintro rfl
    exact ⟨X, F.reservedRoot, rfl, [], (this_reserved_one F).mpr rfl,
      (List.append_nil _).symm⟩

/-- eq:bases at a synthetic root: a `[p]`-style reference reaches the base
`p`, and a `[Y]`-style reference reaches the synthetic root of `Y`. -/
theorem bases_syntheticRoot_iff {X : Label} (hX : X ∈ F.wrappers)
    {t : Path Label} :
    Bases F.Inh (F.syntheticRoot X) t ↔
      MemRef F.Inh (1, t) (F.syntheticRoot X) ∨
        ∃ Y, MemRef F.Inh (0, [Y]) (F.syntheticRoot X) ∧
          t = F.syntheticRoot Y := by
  constructor
  · intro h
    rcases (bases_cons_iff F.Inh).mp h with ⟨pov, hov, n, w, href, hres⟩
    rw [overrides_syntheticRoot F hX] at hov
    subst hov
    rcases F.wrapper_reference X hX _ href with ⟨p, -, heq⟩ | ⟨Y, -, heq⟩
    · obtain ⟨rfl, rfl⟩ : n = 1 ∧ w = p := by simpa using heq
      rw [(resolve_syntheticRoot_one F).mp hres]
      exact Or.inl href
    · obtain ⟨rfl, rfl⟩ : n = 0 ∧ w = [Y] := by simpa using heq
      exact Or.inr ⟨Y, href, (resolve_syntheticRoot_zero F).mp hres⟩
  · rintro (href | ⟨Y, href, rfl⟩)
    · have h := Fact.basesStep ((overrides_syntheticRoot F hX).mpr rfl) href
        ((this_reserved_one F).mpr rfl)
      simpa using h
    · exact Fact.basesStep ((overrides_syntheticRoot F hX).mpr rfl) href
        (Fact.thisZero _ _)

/-! ## Stage B2: structural facts and the classification lemmas for `φ` -/

/-- A proper extension of a synthetic root is not written (structural
fact (i)): the wrapper body carries references and no definitions. -/
theorem syntheticExtension_notMem_dom {X : Label} {w : Path Label}
    (hw : w ≠ []) : (w ++ F.syntheticRoot X) ∉ Dom F.Inh := by
  intro hdom
  rcases F.reserved_subtree _ hdom
      ⟨w ++ [X], by simp⟩ with heq | ⟨X', -, heq⟩
  · have hlen := congrArg List.length heq
    simp [List.length_append] at hlen
  · have hlen := congrArg List.length heq
    simp [List.length_append] at hlen
    exact hw hlen

/-- A written synthetic path is a synthetic root. -/
theorem written_synthetic {S : Set Label} {q : Path Label}
    (hq : q ∈ Dom F.Inh) (hsyn : F.Synthetic S q) :
    ∃ X ∈ S, q = F.syntheticRoot X := by
  obtain ⟨X, hX, w, rfl⟩ := hsyn
  cases w with
  | nil => exact ⟨X, hX, rfl⟩
  | cons a w' => exact absurd hq (syntheticExtension_notMem_dom F (by simp))

theorem not_synthetic_nil {S : Set Label} : ¬ F.Synthetic S [] := by
  rintro ⟨X, -, w, heq⟩
  have := congrArg List.length heq
  simp [List.length_append] at this

theorem not_synthetic_reservedRoot {S : Set Label} :
    ¬ F.Synthetic S F.reservedRoot := by
  rintro ⟨X, -, w, heq⟩
  have := congrArg List.length heq
  simp [List.length_append] at this

theorem phi_nil {S : Set Label} {R' : Path Label} : F.phi S R' [] = [] :=
  phi_of_not_synthetic F (not_synthetic_nil F)

theorem phi_reservedRoot {S : Set Label} {R' : Path Label} :
    F.phi S R' F.reservedRoot = F.reservedRoot :=
  phi_of_not_synthetic F (not_synthetic_reservedRoot F)

theorem phi_syntheticRoot_mem {S : Set Label} {R' : Path Label} {X : Label}
    (hX : X ∈ S) : F.phi S R' (F.syntheticRoot X) = R' := by
  have h := phi_of_synthetic F (R' := R') hX []
  simpa using h

/-- `φ` distributes over `cons` away from the synthetic roots themselves. -/
theorem phi_cons_of_ne_root {S : Set Label} {R' : Path Label} {ℓ : Label}
    {p : Path Label} (h : ∀ X ∈ S, ℓ :: p ≠ F.syntheticRoot X) :
    F.phi S R' (ℓ :: p) = ℓ :: F.phi S R' p := by
  by_cases hsyn : F.Synthetic S (ℓ :: p)
  · obtain ⟨X, hX, w, heq⟩ := hsyn
    cases w with
    | nil => exact absurd heq (h X hX)
    | cons a w' =>
        obtain ⟨rfl, rfl⟩ : ℓ = a ∧ p = w' ++ F.syntheticRoot X := by
          simpa using heq
        rw [show ℓ :: (w' ++ F.syntheticRoot X) =
            (ℓ :: w') ++ F.syntheticRoot X from rfl,
          phi_of_synthetic F hX, phi_of_synthetic F hX]
        rfl
  · have hp : ¬ F.Synthetic S p := by
      rintro ⟨X, hX, w, rfl⟩
      exact hsyn ⟨X, hX, ℓ :: w, rfl⟩
    rw [phi_of_not_synthetic F hsyn, phi_of_not_synthetic F hp]

/-- `φ` has cons shape on cons paths (for a synthetic-root target `R'`). -/
theorem phi_cons_shape {S : Set Label} {Y : Label} {ℓ : Label}
    {p : Path Label} :
    ∃ ℓ', F.phi S (F.syntheticRoot Y) (ℓ :: p) =
      ℓ' :: F.phi S (F.syntheticRoot Y) p := by
  by_cases hroot : ∃ X ∈ S, ℓ :: p = F.syntheticRoot X
  · obtain ⟨X, hX, heq⟩ := hroot
    obtain ⟨rfl, rfl⟩ : ℓ = X ∧ p = F.reservedRoot := by simpa using heq
    rw [phi_syntheticRoot_mem F hX, phi_reservedRoot F]
    exact ⟨Y, rfl⟩
  · exact ⟨ℓ, phi_cons_of_ne_root F fun X hX heq => hroot ⟨X, hX, heq⟩⟩

/-- The condition maintained on definition-site paths through the walk: the
reserved root itself, or a path outside the reserved subtree. Every
`init`-iterate of a written path satisfies it. -/
def DefinitionSiteCondition (q : Path Label) : Prop :=
  q = F.reservedRoot ∨ ¬ F.InSubtree q

theorem definitionSiteCondition_not_synthetic {S : Set Label} {q : Path Label}
    (h : F.DefinitionSiteCondition q) : ¬ F.Synthetic S q := by
  rintro ⟨X, -, w, rfl⟩
  rcases h with heq | hout
  · have := congrArg List.length heq
    simp [List.length_append] at this
  · exact hout ⟨w ++ [X], by simp⟩

theorem phi_of_definitionSiteCondition {S : Set Label} {R' : Path Label}
    {q : Path Label} (h : F.DefinitionSiteCondition q) : F.phi S R' q = q :=
  phi_of_not_synthetic F (definitionSiteCondition_not_synthetic F h)

theorem definitionSiteCondition_nil : F.DefinitionSiteCondition [] :=
  Or.inr fun ⟨w, hw⟩ => by
    have := congrArg List.length hw
    simp [List.length_append] at this

theorem definitionSiteCondition_reservedRoot :
    F.DefinitionSiteCondition F.reservedRoot :=
  Or.inl rfl

/-- `DefinitionSiteCondition` propagates to the tail of a written path (the
`init` of a definition site stays reserved-root-or-outside). -/
theorem definitionSiteCondition_tail_of_written {ℓov : Label}
    {povt : Path Label} (hpov : (ℓov :: povt) ∈ Dom F.Inh) :
    F.DefinitionSiteCondition povt := by
  by_cases hsub : F.InSubtree (ℓov :: povt)
  · rcases F.reserved_subtree _ hpov hsub with heq | ⟨X, -, heq⟩
    · obtain ⟨-, rfl⟩ : ℓov = F.reserved ∧ povt = [] := by simpa using heq
      exact definitionSiteCondition_nil F
    · obtain ⟨-, rfl⟩ : ℓov = X ∧ povt = F.reservedRoot := by
        simpa using heq
      exact definitionSiteCondition_reservedRoot F
  · exact Or.inr fun ⟨w, hw⟩ => hsub ⟨ℓov :: w, by rw [hw]; rfl⟩

/-- Appending a reserved-free projection list to a non-synthetic current path
that is not the reserved root cannot create a synthetic path (structural
fact (iii), literal-resolution insulation). -/
theorem append_not_synthetic {S : Set Label} {wref pcur : Path Label}
    (hres : F.reserved ∉ wref) (hcur : ¬ F.Synthetic S pcur)
    (hne : pcur ≠ F.reservedRoot) :
    ¬ F.Synthetic S (wref ++ pcur) := by
  rintro ⟨X, hX, w, heq⟩
  cases pcur with
  | nil =>
      rw [List.append_nil] at heq
      exact hres (by rw [heq]; simp [syntheticRoot])
  | cons a pcur' =>
      cases pcur' with
      | nil =>
          have heq' : wref ++ [a] = (w ++ [X]) ++ [F.reserved] := by
            simpa [syntheticRoot, List.append_assoc] using heq
          obtain ⟨-, ha⟩ := List.append_inj' heq' rfl
          obtain rfl : a = F.reserved := by simpa using ha
          exact hne rfl
      | cons b t =>
          have hwlen : wref.length ≤ w.length := by
            have hlen := congrArg List.length heq
            simp [syntheticRoot] at hlen
            omega
          have h1 : (wref ++ (a :: b :: t)).drop wref.length = a :: b :: t :=
            List.drop_left
          have h2 : (w ++ F.syntheticRoot X).drop wref.length
              = w.drop wref.length ++ F.syntheticRoot X :=
            List.drop_append_of_le_length hwlen
          have hdrop : a :: b :: t = w.drop wref.length ++ F.syntheticRoot X := by
            rw [← h1, heq, h2]
          exact hcur ⟨X, hX, w.drop wref.length, hdrop⟩

/-! ## Stage B3: auxiliary inversion lemmas -/

theorem overrides_target_nil {q : Path Label} (h : Overrides F.Inh q []) :
    q = [] := by
  cases h with
  | overridesRoot => rfl

theorem supers_override_nil {q c : Path Label} (h : Supers F.Inh q c []) :
    q = [] := by
  cases h with
  | supersRoot => rfl
  | supersStep hchain hov =>
      exact absurd (overrides_target_nil F hov) (by simp)

theorem written_cons_not_synthetic {S : Set Label} {ℓ : Label}
    {pbr : Path Label} (hdom : (ℓ :: pbr) ∈ Dom F.Inh) :
    ¬ F.Synthetic S pbr := by
  rintro ⟨X, hX, w, rfl⟩
  exact syntheticExtension_notMem_dom F (X := X) (w := ℓ :: w) (by simp) hdom

theorem synthetic_syntheticRoot_iff {S : Set Label} {Z : Label} :
    F.Synthetic S (F.syntheticRoot Z) ↔ Z ∈ S := by
  constructor
  · rintro ⟨X, hX, w, heq⟩
    cases w with
    | nil =>
        obtain rfl : Z = X := by simpa [syntheticRoot] using heq
        exact hX
    | cons a w' =>
        have := congrArg List.length heq
        simp [syntheticRoot] at this
  · intro hZ
    exact ⟨Z, hZ, [], rfl⟩

theorem definitionSiteCondition_of_cons {ℓd : Label} {pd : Path Label}
    (h : F.DefinitionSiteCondition (ℓd :: pd)) : F.DefinitionSiteCondition pd := by
  rcases h with heq | hout
  · obtain ⟨-, rfl⟩ : ℓd = F.reserved ∧ pd = [] := by
      simpa [reservedRoot] using heq
    exact definitionSiteCondition_nil F
  · cases pd with
    | nil => exact definitionSiteCondition_nil F
    | cons a pd' =>
        exact Or.inr fun ⟨w, hw⟩ => hout ⟨ℓd :: w, by rw [hw]; rfl⟩

/-- The references written at a synthetic root have nonempty projection
lists. -/
theorem syntheticRoot_reference_ne_nil {X : Label} {n : ℕ} {w : Path Label}
    (hX : X ∈ F.wrappers) (href : MemRef F.Inh (n, w) (F.syntheticRoot X)) :
    w ≠ [] := by
  rcases F.wrapper_reference X hX _ href with ⟨p, hp, heq⟩ | ⟨Y, -, heq⟩
  · obtain ⟨-, rfl⟩ : n = 1 ∧ w = p := by simpa using heq
    exact F.base_nonempty _ hp
  · obtain ⟨-, rfl⟩ : n = 0 ∧ w = [Y] := by simpa using heq
    simp

/-- No wrapper outside `S` reaches a wrapper inside `S` by a `[Y]`-style
reference. The root set of a simulation must satisfy it: a reference of a
wrapper outside `S` resolves literally, and must not land on a synthetic
path of `S`. -/
def OutsideClosed (S : Set Label) : Prop :=
  ∀ X ∈ F.wrappers, X ∉ S →
    ∀ Y, MemRef F.Inh (0, [Y]) (F.syntheticRoot X) → Y ∉ S

/-- The resolution targets of a synthetic root outside `S` never land on a
synthetic path of `S` when projected onto the reserved root. -/
theorem syntheticRoot_reference_target_not_synthetic {S : Set Label}
    {X : Label} {n : ℕ} {w : Path Label} (hX : X ∈ F.wrappers) (hXS : X ∉ S)
    (hS : ∀ X' ∈ S, X' ∈ F.wrappers) (hclosed : F.OutsideClosed S)
    (href : MemRef F.Inh (n, w) (F.syntheticRoot X)) :
    ¬ F.Synthetic S (w ++ F.reservedRoot) := by
  rcases F.wrapper_reference X hX _ href with ⟨p, hp, heq⟩ | ⟨Y, -, heq⟩
  · obtain ⟨-, rfl⟩ : n = 1 ∧ w = p := by simpa using heq
    rintro ⟨X', hX', w', heq'⟩
    have heq₃ : w ++ [F.reserved] = (w' ++ [X']) ++ [F.reserved] := by
      rw [heq', show F.syntheticRoot X' = [X'] ++ [F.reserved] from rfl,
        ← List.append_assoc]
    obtain ⟨hpre, -⟩ := List.append_inj' heq₃ rfl
    exact F.base_head_not_wrapper w hp X' (hS X' hX') ⟨w', hpre⟩
  · obtain ⟨rfl, rfl⟩ : n = 0 ∧ w = [Y] := by simpa using heq
    intro hsyn
    exact hclosed X hX hXS Y href ((synthetic_syntheticRoot_iff F).mp hsyn)

/-! ## Stage B3: the simulation (paper clauses (C1)–(C4)) -/

/-- The simulation motive over one `Fact` derivation: every coordinate's
`φ`-image is derivable, together with the reserved-root bookkeeping that
keeps the induction closed (the paper's structural fact (iii)): override
components equal to the reserved root force the query onto the reserved
root, `bases` never targets the reserved root, synthetic overrides are
reflexive, walks match only definition sites satisfying
`DefinitionSiteCondition` and never output the reserved root. -/
def simulationMotive (S : Set Label) (Y : Label) : Atom Label → Prop
  | .overrides q v =>
      Overrides F.Inh (F.phi S (F.syntheticRoot Y) q)
          (F.phi S (F.syntheticRoot Y) v) ∧
        (v = F.reservedRoot → q = F.reservedRoot) ∧
        (F.Synthetic S v →
          v = q ∨ ∃ X ∈ S, v = F.syntheticRoot X ∧ q = F.syntheticRoot X)
  | .basesStar q t =>
      Relation.ReflTransGen (Bases F.Inh) (F.phi S (F.syntheticRoot Y) q)
          (F.phi S (F.syntheticRoot Y) t) ∧
        (t = F.reservedRoot → q = F.reservedRoot)
  | .bases q t =>
      Relation.ReflTransGen (Bases F.Inh) (F.phi S (F.syntheticRoot Y) q)
          (F.phi S (F.syntheticRoot Y) t) ∧
        t ≠ F.reservedRoot
  | .supers q c v =>
      Supers F.Inh (F.phi S (F.syntheticRoot Y) q)
          (F.phi S (F.syntheticRoot Y) c) (F.phi S (F.syntheticRoot Y) v) ∧
        (F.DefinitionSiteCondition v → c ≠ F.reservedRoot) ∧
        (v = F.reservedRoot → q = F.reservedRoot)
  | .this s pdef n t =>
      F.DefinitionSiteCondition pdef →
        This F.Inh (F.phi S (F.syntheticRoot Y) s) pdef n
            (F.phi S (F.syntheticRoot Y) t) ∧
          (0 < n → t ≠ F.reservedRoot)

/-- The paper's clauses (C1)–(C4) as one derivation induction. `hground`
packages the ground-chain comparison of structural fact (ii): every ground
hop out of a synthetic root in `S` is simulated by a chain out of the target
root. -/
theorem simulation {S : Set Label} {Y : Label} (hY : Y ∈ F.wrappers)
    (hS : ∀ X ∈ S, X ∈ F.wrappers) (hclosed : F.OutsideClosed S)
    (hground : ∀ X ∈ S, ∀ t, Bases F.Inh (F.syntheticRoot X) t →
      Relation.ReflTransGen (Bases F.Inh) (F.syntheticRoot Y)
        (F.phi S (F.syntheticRoot Y) t))
    {a : Atom Label} (h : Fact F.Inh a) : F.simulationMotive S Y a := by
  induction h with
  | supersRoot =>
      refine ⟨?_, fun _ => by simp [reservedRoot],
        fun h => absurd h (by simp [reservedRoot])⟩
      rw [phi_nil]
      exact Fact.supersRoot
  | @supersStep ℓq q ℓb site pov hchain hov ihchain ihov =>
      obtain ⟨hchainφ, hchainres⟩ := ihchain
      obtain ⟨hovφ, hovres, -⟩ := ihov
      refine ⟨?_, ?_, ?_⟩
      · obtain ⟨ℓ₁, hq⟩ := phi_cons_shape F (S := S) (Y := Y) (ℓ := ℓq) (p := q)
        obtain ⟨ℓ₂, hb⟩ :=
          phi_cons_shape F (S := S) (Y := Y) (ℓ := ℓb) (p := site)
        rw [hq, hb] at hchainφ
        rw [hb] at hovφ
        rw [hq]
        exact Fact.supersStep ((basesStar_iff_reflTransGen F.Inh).mpr hchainφ)
          hovφ
      · rintro hpc rfl
        cases hov with
        | overridesSelf hsup₀ hdom₀ =>
            rcases hpc with heq | hout
            · exact absurd heq (by simp [reservedRoot])
            · exact hout ⟨[ℓb], rfl⟩
        | overridesBranch hsup₀ hdom₀ =>
            obtain ⟨-, rfl⟩ := (supers_reservedRoot F).mp hsup₀
            rcases hpc with heq | hout
            · exact absurd heq (by simp [reservedRoot])
            · exact hout ⟨[ℓb], rfl⟩
      · intro hres
        obtain ⟨rfl, rfl⟩ : ℓb = F.reserved ∧ site = [] := by
          simpa [reservedRoot] using hovres hres
        exact hchainres rfl
  | overridesRoot =>
      refine ⟨?_, fun h => absurd h (by simp [reservedRoot]),
        fun h => absurd h (not_synthetic_nil F)⟩
      rw [phi_nil]
      exact Fact.overridesRoot
  | @overridesSelf p c pbr ℓ hsup hdom ihsup =>
      obtain ⟨hsupφ, -, -⟩ := ihsup
      refine ⟨?_, fun h => h, fun _ => Or.inl rfl⟩
      by_cases hroot : ∃ X ∈ S, ℓ :: p = F.syntheticRoot X
      · obtain ⟨X, hX, heq⟩ := hroot
        rw [heq, phi_syntheticRoot_mem F hX]
        exact (overrides_syntheticRoot F hY).mpr rfl
      · rw [phi_cons_of_ne_root F fun X hX heq => hroot ⟨X, hX, heq⟩]
        rw [phi_of_not_synthetic F (written_cons_not_synthetic F hdom)] at hsupφ
        exact Fact.overridesSelf hsupφ hdom
  | @overridesBranch p c pbr ℓ hsup hdom ihsup =>
      obtain ⟨hsupφ, hsupsite?, hsupres⟩ := ihsup
      have hpbr_ns : ¬ F.Synthetic S pbr := written_cons_not_synthetic F hdom
      have hpbrφ : F.phi S (F.syntheticRoot Y) pbr = pbr :=
        phi_of_not_synthetic F hpbr_ns
      refine ⟨?_, ?_, ?_⟩
      · by_cases hroot : ∃ X ∈ S, ℓ :: p = F.syntheticRoot X
        · obtain ⟨X, hX, heq⟩ := hroot
          obtain ⟨rfl, rfl⟩ : ℓ = X ∧ p = F.reservedRoot := by
            simpa [syntheticRoot, reservedRoot] using heq
          obtain ⟨-, rfl⟩ := (supers_reservedRoot F).mp hsup
          rw [show (ℓ :: F.reservedRoot : Path Label) = F.syntheticRoot ℓ from rfl,
            phi_syntheticRoot_mem F hX]
          exact (overrides_syntheticRoot F hY).mpr rfl
        · rw [phi_cons_of_ne_root F fun X hX heq => hroot ⟨X, hX, heq⟩]
          by_cases hroot₂ : ∃ X ∈ S, ℓ :: pbr = F.syntheticRoot X
          · obtain ⟨X, hX, heq₂⟩ := hroot₂
            obtain ⟨rfl, rfl⟩ : ℓ = X ∧ pbr = F.reservedRoot := by
              simpa [syntheticRoot, reservedRoot] using heq₂
            exact absurd ⟨ℓ, hX, by rw [hsupres rfl]⟩ hroot
          · rw [phi_cons_of_ne_root F fun X hX heq => hroot₂ ⟨X, hX, heq⟩, hpbrφ]
            rw [hpbrφ] at hsupφ
            exact Fact.overridesBranch hsupφ hdom
      · intro hres
        obtain ⟨rfl, rfl⟩ : ℓ = F.reserved ∧ pbr = [] := by
          simpa [reservedRoot] using hres
        rw [supers_override_nil F hsup]
      · intro hsynv
        obtain ⟨X, hX, w, heqv⟩ := hsynv
        cases w with
        | cons a w' =>
            exfalso
            apply hpbr_ns
            obtain ⟨-, rfl⟩ : ℓ = a ∧ pbr = w' ++ F.syntheticRoot X := by
              simpa using heqv
            exact ⟨X, hX, w', rfl⟩
        | nil =>
            obtain ⟨rfl, rfl⟩ : ℓ = X ∧ pbr = F.reservedRoot := by
              simpa [syntheticRoot, reservedRoot] using heqv
            refine Or.inr ⟨ℓ, hX, rfl, ?_⟩
            rw [hsupres rfl]
  | @basesStep p pcur ℓ ℓov povt n wref hov href hthis ihov ihthis =>
      have hpovdom : (ℓov :: povt) ∈ Dom F.Inh := href.mem_dom
      have hpovt : F.DefinitionSiteCondition povt :=
        definitionSiteCondition_tail_of_written F hpovdom
      obtain ⟨Sr, hSr, hr⟩ := href
      have hwres : F.reserved ∉ wref :=
        F.reserved_not_in_references _ _ hSr _ hr
      obtain ⟨hovφ, hovres, hovsyn⟩ := ihov
      obtain ⟨hthisφ, hthisres⟩ := ihthis hpovt
      have hpov_syn_of_cr : pcur = F.reservedRoot →
          (ℓov :: povt) = F.syntheticRoot ℓ ∧ ℓ ∈ F.wrappers := by
        intro hcr
        cases n with
        | succ n' => exact absurd hcr (hthisres (by omega))
        | zero =>
            have hp : p = F.reservedRoot := by
              rw [← (this_zero_iff F.Inh).mp hthis]
              exact hcr
            subst hp
            have hpov_syn : ℓov :: povt = F.syntheticRoot ℓ := by
              cases hov with
              | overridesSelf _ _ => rfl
              | overridesBranch hsup₀ _ =>
                  obtain ⟨-, rfl⟩ := (supers_reservedRoot F).mp hsup₀
                  rfl
            refine ⟨hpov_syn, ?_⟩
            rw [hpov_syn] at hpovdom
            rcases F.reserved_subtree _ hpovdom ⟨[ℓ], rfl⟩ with
              heq | ⟨X'', hX'', heq⟩
            · exact absurd heq (by simp [syntheticRoot])
            · obtain rfl : ℓ = X'' := by simpa [syntheticRoot] using heq
              exact hX''
      have htne : wref ++ pcur ≠ F.reservedRoot := by
        cases wref with
        | nil =>
            intro hcr
            rw [List.nil_append] at hcr
            obtain ⟨hpov_syn, hlw⟩ := hpov_syn_of_cr hcr
            have href' : MemRef F.Inh (n, ([] : Path Label)) (F.syntheticRoot ℓ) :=
              hpov_syn ▸ (⟨Sr, hSr, hr⟩ :
                MemRef F.Inh (n, ([] : Path Label)) (ℓov :: povt))
            exact syntheticRoot_reference_ne_nil F hlw href' rfl
        | cons a w' =>
            intro hcr
            have ha : a = F.reserved := by
              have hh := congrArg (fun l => l.head?) hcr
              simpa [reservedRoot] using hh
            exact hwres (ha ▸ List.Mem.head _)
      by_cases hroot : ∃ X ∈ S, (ℓ :: p) = F.syntheticRoot X
      · obtain ⟨X, hX, heq⟩ := hroot
        have hb : Bases F.Inh (F.syntheticRoot X) (wref ++ pcur) := by
          rw [← heq]
          exact Fact.basesStep hov ⟨Sr, hSr, hr⟩ hthis
        refine ⟨?_, htne⟩
        rw [heq, phi_syntheticRoot_mem F hX]
        exact hground X hX _ hb
      · have hpov_ns : ¬ F.Synthetic S (ℓov :: povt) := by
          intro hsyn
          rcases hovsyn hsyn with heqv | ⟨X, hX, -, hq⟩
          · obtain ⟨X, hX, hqr⟩ :=
              written_synthetic F (heqv ▸ hpovdom) (heqv ▸ hsyn)
            exact hroot ⟨X, hX, hqr⟩
          · exact hroot ⟨X, hX, hq⟩
        have hpovφ : F.phi S (F.syntheticRoot Y) (ℓov :: povt) = ℓov :: povt :=
          phi_of_not_synthetic F hpov_ns
        have hcons := phi_cons_of_ne_root F
          (S := S) (R' := F.syntheticRoot Y) fun X hX heq => hroot ⟨X, hX, heq⟩
        rw [hcons, hpovφ] at hovφ
        have hstep' := Fact.basesStep hovφ ⟨Sr, hSr, hr⟩ hthisφ
        have happ : F.phi S (F.syntheticRoot Y) (wref ++ pcur)
            = wref ++ F.phi S (F.syntheticRoot Y) pcur := by
          by_cases hcur : F.Synthetic S pcur
          · obtain ⟨Xc, hXc, wc, rfl⟩ := hcur
            exact phi_append_of_synthetic F hXc wc wref
          · rw [phi_of_not_synthetic F hcur]
            by_cases hcr : pcur = F.reservedRoot
            · obtain ⟨hpov_syn, hlw⟩ := hpov_syn_of_cr hcr
              have hℓS : ℓ ∉ S := by
                intro hin
                cases n with
                | succ n' => exact absurd hcr (hthisres (by omega))
                | zero =>
                    have hp : p = F.reservedRoot := by
                      rw [← (this_zero_iff F.Inh).mp hthis]
                      exact hcr
                    exact hroot ⟨ℓ, hin, by rw [hp]⟩
              have href' : MemRef F.Inh (n, wref) (F.syntheticRoot ℓ) :=
                hpov_syn ▸ (⟨Sr, hSr, hr⟩ : MemRef F.Inh (n, wref) (ℓov :: povt))
              subst hcr
              exact phi_of_not_synthetic F
                (syntheticRoot_reference_target_not_synthetic F hlw hℓS hS
                  hclosed href')
            · exact phi_of_not_synthetic F
                (append_not_synthetic F hwres hcur hcr)
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
      obtain ⟨hsupφ, hsupsite, -⟩ := ihsup
      have hpdefφ : F.phi S (F.syntheticRoot Y) (ℓd :: pd) = ℓd :: pd :=
        phi_of_definitionSiteCondition F hpdef
      have hpd : F.DefinitionSiteCondition pd :=
        definitionSiteCondition_of_cons F hpdef
      obtain ⟨hrecφ, hrecres⟩ := ihrec hpd
      rw [hpdefφ] at hsupφ
      refine ⟨Fact.thisSucc hsupφ hrecφ, fun _ => ?_⟩
      cases n with
      | zero =>
          obtain rfl := (this_zero_iff F.Inh).mp hrec
          exact hsupsite hpdef
      | succ n' => exact hrecres (by omega)

/-! ## Stage B4: transfer -/

theorem not_synthetic_of_not_inSubtree {S : Set Label} {v : Path Label}
    (hv : ¬ F.InSubtree v) : ¬ F.Synthetic S v := by
  rintro ⟨X, -, w, rfl⟩
  exact hv ⟨w ++ [X], by simp⟩

theorem base_not_synthetic {S : Set Label} {p : Path Label}
    (hp : p ∈ F.bases) : ¬ F.Synthetic S p := by
  rintro ⟨X, -, w, rfl⟩
  exact F.base_outside _ hp ⟨w ++ [X], by simp⟩

/-- One direction of the transfer: an outside-subtree override component of
`supers` at an extension of a synthetic root in `S` reappears at the same
extension of the target root. -/
theorem supers_transfer {S : Set Label} {Y XA : Label}
    (hY : Y ∈ F.wrappers) (hS : ∀ X ∈ S, X ∈ F.wrappers)
    (hclosed : F.OutsideClosed S)
    (hground : ∀ X ∈ S, ∀ t, Bases F.Inh (F.syntheticRoot X) t →
      Relation.ReflTransGen (Bases F.Inh) (F.syntheticRoot Y)
        (F.phi S (F.syntheticRoot Y) t))
    (hXA : XA ∈ S) (w : Path Label) {c v : Path Label}
    (hsup : Supers F.Inh (w ++ F.syntheticRoot XA) c v) (hv : ¬ F.InSubtree v) :
    ∃ c', Supers F.Inh (w ++ F.syntheticRoot Y) c' v := by
  have h := (simulation F hY hS hclosed hground hsup).1
  rw [phi_of_synthetic F hXA,
    phi_of_not_synthetic F (not_synthetic_of_not_inSubtree F hv)] at h
  exact ⟨_, h⟩

/-- Existence transfers unconditionally: any `supers` pair maps over. -/
theorem supers_nonempty_transfer {S : Set Label} {Y XA : Label}
    (hY : Y ∈ F.wrappers) (hS : ∀ X ∈ S, X ∈ F.wrappers)
    (hclosed : F.OutsideClosed S)
    (hground : ∀ X ∈ S, ∀ t, Bases F.Inh (F.syntheticRoot X) t →
      Relation.ReflTransGen (Bases F.Inh) (F.syntheticRoot Y)
        (F.phi S (F.syntheticRoot Y) t))
    (hXA : XA ∈ S) (w : Path Label)
    (h : (supersSet F.Inh (w ++ F.syntheticRoot XA)).Nonempty) :
    (supersSet F.Inh (w ++ F.syntheticRoot Y)).Nonempty := by
  obtain ⟨⟨c, v⟩, hsup⟩ := h
  have h1 := (simulation F hY hS hclosed hground (hsup : Supers F.Inh _ c v)).1
  rw [phi_of_synthetic F hXA] at h1
  exact ⟨(_, _), h1⟩

end WrapperFamily

end InheritanceCalculus
