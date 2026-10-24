import InheritanceCalculus.Inductive

/-!
# Path existence

This module proves the paper's Lemma "Path existence" (lem:path-existence,
tex line ~3925): `supers(q) ≠ ∅` exactly when `q` is *existent*, i.e. `q` is
the root or some override component of `supers(init(q))` writes `last(q)`
directly. Consequently a label `ℓ` exists at `p`, in the sense of the paper's
Section "Mixin Trees", exactly when `supers(p ⌢ ℓ) ≠ ∅`
(`supersSet_cons_nonempty_iff`; the paper's `p ⌢ ℓ` is `ℓ :: p` in the
reversed representation of `Basic.lean`).

The proof follows the paper's: first `supers(q) ≠ ∅ ↔ overrides(q) ≠ ∅`
(the reflexive term of `bases*` injects `overrides(q)` into `supers(q)`;
conversely an empty `overrides(q)` empties `bases(q)`, collapses `bases*(q)`
to `{q}`, and hence empties `supers(q)`), then eq:overrides is read off at
the root and at `p ⌢ ℓ`.
-/

set_option warningAsError true

namespace InheritanceCalculus

variable {Label : Type*} (Inh : Path Label → Option (Set (Reference Label)))

/-- lem:path-existence's "existent": the root, or a path whose final label is
written by some override component of the supers of its enclosing path. -/
def Existent (q : Path Label) : Prop :=
  q = [] ∨ ∃ p ℓ c pbr, q = ℓ :: p ∧ Supers Inh p c pbr ∧
    (ℓ :: pbr) ∈ Dom Inh

/-- First step of lem:path-existence: `supers(q) ≠ ∅ ↔ overrides(q) ≠ ∅`. -/
theorem supersSet_nonempty_iff_overridesSet_nonempty (q : Path Label) :
    (supersSet Inh q).Nonempty ↔ (overridesSet Inh q).Nonempty := by
  constructor
  · rintro ⟨⟨c, pov⟩, hsup⟩
    have hsup' : Supers Inh q c pov := hsup
    cases hsup' with
    | supersRoot => exact ⟨[], Fact.overridesRoot⟩
    | @supersStep ℓq q' ℓb site pov hchain hov =>
        rcases ((basesStar_iff_reflTransGen Inh).mp hchain).cases_head with
          heq | ⟨x, hqx, -⟩
        · injection heq with h1 h2
          subst h1
          subst h2
          exact ⟨pov, hov⟩
        · cases hqx with
          | basesStep hov' href' hthis' => exact ⟨_, hov'⟩
  · rintro ⟨pov, hov⟩
    cases q with
    | nil => exact ⟨([], []), Fact.supersRoot⟩
    | cons ℓq q' =>
        exact ⟨(q', pov),
          Fact.supersStep (Fact.basesStarRefl (ℓq :: q')) hov⟩

/-- lem:path-existence: `supers(q) ≠ ∅` if and only if `q` is existent. -/
theorem supersSet_nonempty_iff_existent (q : Path Label) :
    (supersSet Inh q).Nonempty ↔ Existent Inh q := by
  rw [supersSet_nonempty_iff_overridesSet_nonempty]
  constructor
  · rintro ⟨pov, hov⟩
    cases hov with
    | overridesRoot => exact Or.inl rfl
    | overridesSelf hsup hdom => exact Or.inr ⟨_, _, _, _, rfl, hsup, hdom⟩
    | overridesBranch hsup hdom => exact Or.inr ⟨_, _, _, _, rfl, hsup, hdom⟩
  · rintro (rfl | ⟨p, ℓ, c, pbr, rfl, hsup, hdom⟩)
    · exact ⟨[], Fact.overridesRoot⟩
    · exact ⟨ℓ :: pbr, Fact.overridesBranch hsup hdom⟩

/-- lem:path-existence, interface contract: a label `ℓ` exists at `p` (in the
sense of Section "Mixin Trees": `supers(p ⌢ ℓ) ≠ ∅`) exactly when some super
mixin of `p` writes `ℓ`. -/
theorem supersSet_cons_nonempty_iff (ℓ : Label) (p : Path Label) :
    (supersSet Inh (ℓ :: p)).Nonempty ↔
      ∃ c pbr, Supers Inh p c pbr ∧ (ℓ :: pbr) ∈ Dom Inh := by
  rw [supersSet_nonempty_iff_existent]
  constructor
  · rintro (habs | ⟨p', ℓ', c, pbr, heq, hsup, hdom⟩)
    · exact absurd habs (by simp)
    · obtain ⟨rfl, rfl⟩ : ℓ' = ℓ ∧ p' = p := by simpa using heq.symm
      exact ⟨c, pbr, hsup, hdom⟩
  · rintro ⟨c, pbr, hsup, hdom⟩
    exact Or.inr ⟨p, ℓ, c, pbr, rfl, hsup, hdom⟩

end InheritanceCalculus
