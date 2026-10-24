import InheritanceCalculus.MergeSimulation

/-!
# Algebraic properties of deep merge: commutativity

The paper's Theorem "Commutativity" (thm:merge-commutative, Appendix
"Algebraic Properties of Deep Merge"), fully proved: `merge_commutative` and
`merge_commutative_exists` at the end of this file. The two sides of the law
are two wrappers of one document, `mergedForward` written `[p₁], [p₂]` and
`mergedReversed` written `[p₂], [p₁]`; the law compares the two paths, and
the simulation of `MergeSimulation.lean` proves it in both directions, as it
proves associativity.

The written order enters the proof in one place: `inherits` carries *sets*
of references, so every ground hop out of one wrapper is a ground hop out of
the other (`ground_mergedForward_mergedReversed`,
`ground_mergedReversed_mergedForward`). This is structural fact (ii) of the
simulation; every other step is the simulation itself.

## Setting, without the syntax layer

The syntax layer is out of scope, so the construction is axiomatized as
conditions on the abstract primitive `Inh`, bundled in
`CommutativityDocument`:

- the reserved root `[reserved]` is written with no references;
- the two synthetic roots `[mergedForward, reserved]` and
  `[mergedReversed, reserved]` are written with the reference lists of the
  paper's display, `[p₁]`-style references being de-Bruijn `(1, p₁)`;
- nothing else is written inside the reserved subtree (in the reversed path
  representation, "inside the subtree" is "the last list element is
  `reserved`");
- the reserved label occurs in no reference's projection list;
- the two base paths `p₁, p₂` are written, nonempty, and outside the
  reserved subtree.
-/

set_option warningAsError true

namespace InheritanceCalculus

/-- The canonical commutativity construction, axiomatized on the abstract
primitive (paper thm:merge-commutative, hypothesis part). Paths are in the
reversed representation of `Basic.lean`, so the paper's synthetic root
`(__merge, X)` is `[X, reserved]` and its extensions are
`w ++ [X, reserved]`. The two wrapper labels are named after the labels of
the paper's display. -/
structure CommutativityDocument (Label : Type*) where
  Inh : Path Label → Option (Set (Reference Label))
  reserved : Label
  mergedForward : Label
  mergedReversed : Label
  p₁ : Path Label
  p₂ : Path Label
  wrapper_ne : mergedForward ≠ mergedReversed
  wrapper_ne_reserved :
    ∀ X ∈ ([mergedForward, mergedReversed] : List Label), X ≠ reserved
  inh_reserved : Inh [reserved] = some ∅
  /-- `mergedForward` is written with the references `[p₁]` and `[p₂]`, in
  this order. -/
  inh_mergedForward : Inh [mergedForward, reserved] = some {(1, p₁), (1, p₂)}
  /-- `mergedReversed` is written with the references `[p₂]` and `[p₁]`, in
  this order. -/
  inh_mergedReversed : Inh [mergedReversed, reserved] = some {(1, p₂), (1, p₁)}
  /-- Nothing else is written inside the reserved subtree: a written path
  ending in the reserved label is the reserved root or a synthetic root. -/
  reserved_subtree : ∀ q ∈ Dom Inh, (∃ w, q = w ++ [reserved]) →
    q = [reserved] ∨
      ∃ X ∈ ([mergedForward, mergedReversed] : List Label), q = [X, reserved]
  /-- The reserved label occurs in no reference's projection list. -/
  reserved_not_in_references : ∀ q S, Inh q = some S →
    ∀ r ∈ S, reserved ∉ r.2
  base_nonempty : ∀ p ∈ ([p₁, p₂] : List (Path Label)), p ≠ []
  base_written : ∀ p ∈ ([p₁, p₂] : List (Path Label)), p ∈ Dom Inh
  /-- The bases lie outside the reserved subtree. -/
  base_outside : ∀ p ∈ ([p₁, p₂] : List (Path Label)),
    ¬ ∃ w, p = w ++ [reserved]
  /-- The paper's "choosing the two wrapper labels distinct from the first
  labels of p₁, p₂" (the first label is the outermost, the last element in
  the reversed representation). -/
  base_head_not_wrapper : ∀ p ∈ ([p₁, p₂] : List (Path Label)),
    ∀ X ∈ ([mergedForward, mergedReversed] : List Label), ¬ ∃ w, p = w ++ [X]

namespace CommutativityDocument

variable {Label : Type*} (D : CommutativityDocument Label)

/-- The two wrapper labels. -/
abbrev wrapperLabels : List Label := [D.mergedForward, D.mergedReversed]

/-- The synthetic root for a wrapper label. -/
abbrev syntheticRoot (X : Label) : Path Label := [X, D.reserved]

/-- A path lies inside the reserved subtree exactly when its outermost label
(the last element in the reversed representation) is the reserved label. -/
def InSubtree (q : Path Label) : Prop := ∃ w, q = w ++ [D.reserved]

/-- The two wrappers form a wrapper family over the two bases. -/
def toWrapperFamily : WrapperFamily Label where
  Inh := D.Inh
  reserved := D.reserved
  wrappers := {X | X ∈ D.wrapperLabels}
  bases := {p | p ∈ ([D.p₁, D.p₂] : List (Path Label))}
  inh_reserved := D.inh_reserved
  wrapper_written := by
    intro X hX
    simp only [Set.mem_setOf_eq, wrapperLabels, List.mem_cons, List.not_mem_nil,
      or_false] at hX
    rcases hX with rfl | rfl <;>
      simp [Dom, D.inh_mergedForward, D.inh_mergedReversed]
  wrapper_reference := by
    rintro X hX r ⟨Sr, hSr, hr⟩
    simp only [Set.mem_setOf_eq, wrapperLabels, List.mem_cons, List.not_mem_nil,
      or_false] at hX
    rcases hX with rfl | rfl
    · rw [D.inh_mergedForward] at hSr; cases hSr
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
      rcases hr with rfl | rfl <;> simp
    · rw [D.inh_mergedReversed] at hSr; cases hSr
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
      rcases hr with rfl | rfl <;> simp
  reserved_subtree := D.reserved_subtree
  reserved_not_in_references := D.reserved_not_in_references
  base_nonempty := D.base_nonempty
  base_outside := D.base_outside
  base_head_not_wrapper := D.base_head_not_wrapper

theorem mem_wrappers {X : Label} (hX : X ∈ D.wrapperLabels) :
    X ∈ D.toWrapperFamily.wrappers :=
  hX

theorem base_not_synthetic {S : Set Label} {p : Path Label}
    (hp : p ∈ ([D.p₁, D.p₂] : List (Path Label))) :
    ¬ D.toWrapperFamily.Synthetic S p :=
  D.toWrapperFamily.base_not_synthetic hp

/-! ## Ground facts: bases at the two synthetic roots -/

theorem bases_mergedForward {t : Path Label} :
    Bases D.Inh (D.syntheticRoot D.mergedForward) t ↔ t = D.p₁ ∨ t = D.p₂ := by
  refine (D.toWrapperFamily.bases_syntheticRoot_iff
    (D.mem_wrappers (by simp))).trans ?_
  simp [toWrapperFamily, MemRef, D.inh_mergedForward]

theorem bases_mergedReversed {t : Path Label} :
    Bases D.Inh (D.syntheticRoot D.mergedReversed) t ↔ t = D.p₂ ∨ t = D.p₁ := by
  refine (D.toWrapperFamily.bases_syntheticRoot_iff
    (D.mem_wrappers (by simp))).trans ?_
  simp [toWrapperFamily, MemRef, D.inh_mergedReversed]

/-! ## Structural fact (ii): root sets and ground chains -/

/-- Neither wrapper carries a `[Y]`-style reference, so every root set is
outside-closed. -/
theorem outsideClosed (S : Set Label) : D.toWrapperFamily.OutsideClosed S := by
  rintro X hX - Y ⟨Sr, hSr, hr⟩
  have hSr' : D.Inh [X, D.reserved] = some Sr := hSr
  simp only [toWrapperFamily, Set.mem_setOf_eq, wrapperLabels, List.mem_cons,
    List.not_mem_nil, or_false] at hX
  rcases hX with rfl | rfl
  · rw [D.inh_mergedForward] at hSr'; cases hSr'
    simp at hr
  · rw [D.inh_mergedReversed] at hSr'; cases hSr'
    simp at hr

/-- Ground-hop simulation, mergedForward into mergedReversed: both wrappers
inherit the set `{[p₁], [p₂]}`. -/
theorem ground_mergedForward_mergedReversed :
    ∀ X ∈ ({D.mergedForward} : Set Label), ∀ t,
      Bases D.Inh (D.syntheticRoot X) t →
      Relation.ReflTransGen (Bases D.Inh) (D.syntheticRoot D.mergedReversed)
        (D.toWrapperFamily.phi {D.mergedForward}
          (D.syntheticRoot D.mergedReversed) t) := by
  intro X hX t hb
  obtain rfl := Set.mem_singleton_iff.mp hX
  rcases (bases_mergedForward D).mp hb with rfl | rfl
  · rw [D.toWrapperFamily.phi_of_not_synthetic (base_not_synthetic D (by simp))]
    exact Relation.ReflTransGen.single
      ((bases_mergedReversed D).mpr (Or.inr rfl))
  · rw [D.toWrapperFamily.phi_of_not_synthetic (base_not_synthetic D (by simp))]
    exact Relation.ReflTransGen.single
      ((bases_mergedReversed D).mpr (Or.inl rfl))

/-- Ground-hop simulation, mergedReversed into mergedForward. -/
theorem ground_mergedReversed_mergedForward :
    ∀ X ∈ ({D.mergedReversed} : Set Label), ∀ t,
      Bases D.Inh (D.syntheticRoot X) t →
      Relation.ReflTransGen (Bases D.Inh) (D.syntheticRoot D.mergedForward)
        (D.toWrapperFamily.phi {D.mergedReversed}
          (D.syntheticRoot D.mergedForward) t) := by
  intro X hX t hb
  obtain rfl := Set.mem_singleton_iff.mp hX
  rcases (bases_mergedReversed D).mp hb with rfl | rfl
  · rw [D.toWrapperFamily.phi_of_not_synthetic (base_not_synthetic D (by simp))]
    exact Relation.ReflTransGen.single
      ((bases_mergedForward D).mpr (Or.inr rfl))
  · rw [D.toWrapperFamily.phi_of_not_synthetic (base_not_synthetic D (by simp))]
    exact Relation.ReflTransGen.single
      ((bases_mergedForward D).mpr (Or.inl rfl))

theorem singleton_mem_wrappers {X : Label} (hX : X ∈ D.wrapperLabels) :
    ∀ X' ∈ ({X} : Set Label), X' ∈ D.toWrapperFamily.wrappers := by
  intro X' hX'
  obtain rfl := Set.mem_singleton_iff.mp hX'
  exact D.mem_wrappers hX

/-- **thm:merge-commutative**: for every path suffix `w`, the sets of
outside-subtree override components of `supers` agree at the two merged
paths. Writing the references of a deep merge in either order is
unobservable outside the reserved subtree. -/
theorem merge_commutative (w : Path Label) {v : Path Label}
    (hv : ¬ D.InSubtree v) :
    (∃ c, Supers D.Inh (w ++ D.syntheticRoot D.mergedForward) c v) ↔
      (∃ c, Supers D.Inh (w ++ D.syntheticRoot D.mergedReversed) c v) := by
  constructor
  · rintro ⟨c, hsup⟩
    exact D.toWrapperFamily.supers_transfer (D.mem_wrappers (by simp))
      (D.singleton_mem_wrappers (by simp)) (D.outsideClosed _)
      (ground_mergedForward_mergedReversed D) rfl w hsup hv
  · rintro ⟨c, hsup⟩
    exact D.toWrapperFamily.supers_transfer (D.mem_wrappers (by simp))
      (D.singleton_mem_wrappers (by simp)) (D.outsideClosed _)
      (ground_mergedReversed_mergedForward D) rfl w hsup hv

/-- thm:merge-commutative, existence part: the two merged paths exist
together (nonempty `supers`, Section "Semantic Functions"). -/
theorem merge_commutative_exists (w : Path Label) :
    (supersSet D.Inh (w ++ D.syntheticRoot D.mergedForward)).Nonempty ↔
      (supersSet D.Inh (w ++ D.syntheticRoot D.mergedReversed)).Nonempty :=
  ⟨D.toWrapperFamily.supers_nonempty_transfer (D.mem_wrappers (by simp))
      (D.singleton_mem_wrappers (by simp)) (D.outsideClosed _)
      (ground_mergedForward_mergedReversed D) rfl w,
    D.toWrapperFamily.supers_nonempty_transfer (D.mem_wrappers (by simp))
      (D.singleton_mem_wrappers (by simp)) (D.outsideClosed _)
      (ground_mergedReversed_mergedForward D) rfl w⟩

end CommutativityDocument

end InheritanceCalculus
