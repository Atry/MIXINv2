import InheritanceCalculus.MergeSimulation

/-!
# Algebraic properties of deep merge: associativity

The paper's Theorem "Associativity" (thm:merge-associative, Appendix
"Algebraic Properties of Deep Merge"), fully proved: `merge_associative` and
`merge_associative_exists` at the end of this file, as instances of the
simulation of `MergeSimulation.lean`.

## Setting, without the syntax layer

The paper states the theorem about a *document* (five wrappers written under
a reserved label `__merge`). Here the syntax layer is out of scope, so the
construction is axiomatized as conditions on the abstract primitive `Inh`,
bundled in `AssociativityDocument`:

- the reserved root `[reserved]` is written with no references;
- the five synthetic roots `[X, reserved]` are written with exactly the
  wrapper reference lists of the paper's display (`[pᵢ]`-style references
  are de-Bruijn `(1, pᵢ)`, one walk step out of the reserved scope to the top
  level, then project `pᵢ`; `[LeftPair]`-style references are
  `(0, [label])`);
- nothing else is written inside the reserved subtree (in the reversed path
  representation, "inside the subtree" is "the last list element is
  `reserved`");
- the reserved label occurs in no reference's projection list;
- the three base paths `p₁, p₂, p₃` are written, nonempty, and outside the
  reserved subtree.

## Structure

- `toWrapperFamily`: the five wrappers form a `WrapperFamily`.
- Ground facts: `bases` at the five synthetic roots (the paper's "chain
  flattening").
- Structural fact (ii): every ground hop of one side is simulated by a chain
  out of the other side (`ground_*`), and each side's root set is
  outside-closed (`outsideClosed`).
- Conclusion: the simulation of `MergeSimulation.lean`, for each ordered
  pair of sides, gives the agreement of the outside-subtree override
  components at the three merged extensions, and existence transfers
  unconditionally.
-/

set_option warningAsError true

namespace InheritanceCalculus

/-- The canonical associativity construction, axiomatized on the abstract
primitive (paper thm:merge-associative, hypothesis part). Paths are in the
reversed representation of `Basic.lean`, so the paper's synthetic root
`(__merge, X)` is `[X, reserved]` and its extensions are
`w ++ [X, reserved]`. The five wrapper labels are named after the labels of
the paper's display. -/
structure AssociativityDocument (Label : Type*) where
  Inh : Path Label → Option (Set (Reference Label))
  reserved : Label
  leftPair : Label
  rightPair : Label
  mergedLeft : Label
  mergedRight : Label
  mergedFlat : Label
  p₁ : Path Label
  p₂ : Path Label
  p₃ : Path Label
  wrapper_nodup :
    ([leftPair, rightPair, mergedLeft, mergedRight, mergedFlat] : List Label).Nodup
  wrapper_ne_reserved :
    ∀ X ∈ ([leftPair, rightPair, mergedLeft, mergedRight, mergedFlat] : List Label),
      X ≠ reserved
  inh_reserved : Inh [reserved] = some ∅
  inh_leftPair : Inh [leftPair, reserved] = some {(1, p₁), (1, p₂)}
  inh_rightPair : Inh [rightPair, reserved] = some {(1, p₂), (1, p₃)}
  inh_mergedLeft : Inh [mergedLeft, reserved] = some {(0, [leftPair]), (1, p₃)}
  inh_mergedRight : Inh [mergedRight, reserved] = some {(1, p₁), (0, [rightPair])}
  inh_mergedFlat : Inh [mergedFlat, reserved] = some {(1, p₁), (1, p₂), (1, p₃)}
  /-- Nothing else is written inside the reserved subtree: a written path
  ending in the reserved label is the reserved root or a synthetic root. -/
  reserved_subtree : ∀ q ∈ Dom Inh, (∃ w, q = w ++ [reserved]) →
    q = [reserved] ∨
      ∃ X ∈ ([leftPair, rightPair, mergedLeft, mergedRight, mergedFlat] : List Label),
        q = [X, reserved]
  /-- The reserved label occurs in no reference's projection list. -/
  reserved_not_in_references : ∀ q S, Inh q = some S →
    ∀ r ∈ S, reserved ∉ r.2
  base_nonempty : ∀ p ∈ ([p₁, p₂, p₃] : List (Path Label)), p ≠ []
  base_written : ∀ p ∈ ([p₁, p₂, p₃] : List (Path Label)), p ∈ Dom Inh
  /-- The bases lie outside the reserved subtree. -/
  base_outside : ∀ p ∈ ([p₁, p₂, p₃] : List (Path Label)),
    ¬ ∃ w, p = w ++ [reserved]
  /-- The paper's "choosing the five wrapper labels distinct from the first
  labels of p₁, p₂, p₃" (the first label is the outermost, the last element
  in the reversed representation). -/
  base_head_not_wrapper : ∀ p ∈ ([p₁, p₂, p₃] : List (Path Label)),
    ∀ X ∈ ([leftPair, rightPair, mergedLeft, mergedRight, mergedFlat] : List Label),
      ¬ ∃ w, p = w ++ [X]

namespace AssociativityDocument

variable {Label : Type*} (D : AssociativityDocument Label)

/-- The five wrapper labels. -/
abbrev wrapperLabels : List Label :=
  [D.leftPair, D.rightPair, D.mergedLeft, D.mergedRight, D.mergedFlat]

/-- The synthetic root for a wrapper label. -/
abbrev syntheticRoot (X : Label) : Path Label := [X, D.reserved]

/-- A path lies inside the reserved subtree exactly when its outermost label
(the last element in the reversed representation) is the reserved label. -/
def InSubtree (q : Path Label) : Prop := ∃ w, q = w ++ [D.reserved]

/-- The five wrappers form a wrapper family over the three bases. -/
def toWrapperFamily : WrapperFamily Label where
  Inh := D.Inh
  reserved := D.reserved
  wrappers := {X | X ∈ D.wrapperLabels}
  bases := {p | p ∈ ([D.p₁, D.p₂, D.p₃] : List (Path Label))}
  inh_reserved := D.inh_reserved
  wrapper_written := by
    intro X hX
    simp only [Set.mem_setOf_eq, wrapperLabels, List.mem_cons, List.not_mem_nil,
      or_false] at hX
    rcases hX with rfl | rfl | rfl | rfl | rfl <;>
      simp [Dom, D.inh_leftPair, D.inh_rightPair, D.inh_mergedLeft,
        D.inh_mergedRight, D.inh_mergedFlat]
  wrapper_reference := by
    rintro X hX r ⟨Sr, hSr, hr⟩
    simp only [Set.mem_setOf_eq, wrapperLabels, List.mem_cons, List.not_mem_nil,
      or_false] at hX
    rcases hX with rfl | rfl | rfl | rfl | rfl
    · rw [D.inh_leftPair] at hSr; cases hSr
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
      rcases hr with rfl | rfl <;> simp
    · rw [D.inh_rightPair] at hSr; cases hSr
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
      rcases hr with rfl | rfl <;> simp
    · rw [D.inh_mergedLeft] at hSr; cases hSr
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
      rcases hr with rfl | rfl <;> simp
    · rw [D.inh_mergedRight] at hSr; cases hSr
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
      rcases hr with rfl | rfl <;> simp
    · rw [D.inh_mergedFlat] at hSr; cases hSr
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
      rcases hr with rfl | rfl | rfl <;> simp
  reserved_subtree := D.reserved_subtree
  reserved_not_in_references := D.reserved_not_in_references
  base_nonempty := D.base_nonempty
  base_outside := D.base_outside
  base_head_not_wrapper := D.base_head_not_wrapper

theorem mem_wrappers {X : Label} (hX : X ∈ D.wrapperLabels) :
    X ∈ D.toWrapperFamily.wrappers :=
  hX

theorem base_not_synthetic {S : Set Label} {p : Path Label}
    (hp : p ∈ ([D.p₁, D.p₂, D.p₃] : List (Path Label))) :
    ¬ D.toWrapperFamily.Synthetic S p :=
  D.toWrapperFamily.base_not_synthetic hp

theorem phi_syntheticRoot_mem {S : Set Label} {R' : Path Label} {X : Label}
    (hX : X ∈ S) : D.toWrapperFamily.phi S R' (D.syntheticRoot X) = R' :=
  D.toWrapperFamily.phi_syntheticRoot_mem hX

/-! ## Ground facts: bases at the synthetic roots -/

theorem bases_leftPair {t : Path Label} :
    Bases D.Inh (D.syntheticRoot D.leftPair) t ↔ t = D.p₁ ∨ t = D.p₂ := by
  refine (D.toWrapperFamily.bases_syntheticRoot_iff
    (D.mem_wrappers (by simp))).trans ?_
  simp [toWrapperFamily, MemRef, D.inh_leftPair]

theorem bases_rightPair {t : Path Label} :
    Bases D.Inh (D.syntheticRoot D.rightPair) t ↔ t = D.p₂ ∨ t = D.p₃ := by
  refine (D.toWrapperFamily.bases_syntheticRoot_iff
    (D.mem_wrappers (by simp))).trans ?_
  simp [toWrapperFamily, MemRef, D.inh_rightPair]

theorem bases_mergedLeft {t : Path Label} :
    Bases D.Inh (D.syntheticRoot D.mergedLeft) t ↔
      t = D.syntheticRoot D.leftPair ∨ t = D.p₃ := by
  refine (D.toWrapperFamily.bases_syntheticRoot_iff
    (D.mem_wrappers (by simp))).trans ?_
  simp [toWrapperFamily, MemRef, D.inh_mergedLeft, or_comm]

theorem bases_mergedRight {t : Path Label} :
    Bases D.Inh (D.syntheticRoot D.mergedRight) t ↔
      t = D.p₁ ∨ t = D.syntheticRoot D.rightPair := by
  refine (D.toWrapperFamily.bases_syntheticRoot_iff
    (D.mem_wrappers (by simp))).trans ?_
  simp [toWrapperFamily, MemRef, D.inh_mergedRight]

theorem bases_mergedFlat {t : Path Label} :
    Bases D.Inh (D.syntheticRoot D.mergedFlat) t ↔
      t = D.p₁ ∨ t = D.p₂ ∨ t = D.p₃ := by
  refine (D.toWrapperFamily.bases_syntheticRoot_iff
    (D.mem_wrappers (by simp))).trans ?_
  simp [toWrapperFamily, MemRef, D.inh_mergedFlat]

/-! ## Structural fact (ii): root sets and ground chains -/

/-- The only `[Y]`-style references are `mergedLeft`'s to `leftPair` and
`mergedRight`'s to `rightPair`, so a root set is outside-closed as soon as it
contains `leftPair` only together with `mergedLeft`, and `rightPair` only
together with `mergedRight`. -/
theorem outsideClosed {S : Set Label}
    (hleft : D.mergedLeft ∉ S → D.leftPair ∉ S)
    (hright : D.mergedRight ∉ S → D.rightPair ∉ S) :
    D.toWrapperFamily.OutsideClosed S := by
  rintro X hX hXS Y ⟨Sr, hSr, hr⟩
  have hSr' : D.Inh [X, D.reserved] = some Sr := hSr
  simp only [toWrapperFamily, Set.mem_setOf_eq, wrapperLabels, List.mem_cons,
    List.not_mem_nil, or_false] at hX
  rcases hX with rfl | rfl | rfl | rfl | rfl
  · rw [D.inh_leftPair] at hSr'; cases hSr'
    simp at hr
  · rw [D.inh_rightPair] at hSr'; cases hSr'
    simp at hr
  · rw [D.inh_mergedLeft] at hSr'; cases hSr'
    obtain rfl : Y = D.leftPair := by simpa using hr
    exact hleft hXS
  · rw [D.inh_mergedRight] at hSr'; cases hSr'
    obtain rfl : Y = D.rightPair := by simpa using hr
    exact hright hXS
  · rw [D.inh_mergedFlat] at hSr'; cases hSr'
    simp at hr

/-- The pairwise distinctness of the wrapper labels, unpacked. -/
theorem wrapper_ne :
    D.leftPair ≠ D.rightPair ∧ D.leftPair ≠ D.mergedLeft ∧
    D.leftPair ≠ D.mergedRight ∧ D.leftPair ≠ D.mergedFlat ∧
    D.rightPair ≠ D.mergedLeft ∧ D.rightPair ≠ D.mergedRight ∧
    D.rightPair ≠ D.mergedFlat ∧ D.mergedLeft ≠ D.mergedRight ∧
    D.mergedLeft ≠ D.mergedFlat ∧ D.mergedRight ≠ D.mergedFlat := by
  have hnd := D.wrapper_nodup
  simp [List.nodup_cons] at hnd
  tauto

/-- Ground-hop simulation, mergedLeft side into mergedFlat. -/
theorem ground_mergedLeft_mergedFlat :
    ∀ X ∈ ({D.mergedLeft, D.leftPair} : Set Label), ∀ t,
      Bases D.Inh (D.syntheticRoot X) t →
      Relation.ReflTransGen (Bases D.Inh) (D.syntheticRoot D.mergedFlat)
        (D.toWrapperFamily.phi {D.mergedLeft, D.leftPair}
          (D.syntheticRoot D.mergedFlat) t) := by
  intro X hX t hb
  rcases Set.mem_insert_iff.mp hX with rfl | hX
  · rcases (bases_mergedLeft D).mp hb with rfl | rfl
    · rw [D.phi_syntheticRoot_mem (by simp)]
    · rw [D.toWrapperFamily.phi_of_not_synthetic (base_not_synthetic D (by simp))]
      exact Relation.ReflTransGen.single
        ((bases_mergedFlat D).mpr (Or.inr (Or.inr rfl)))
  · obtain rfl := Set.mem_singleton_iff.mp hX
    rcases (bases_leftPair D).mp hb with rfl | rfl
    · rw [D.toWrapperFamily.phi_of_not_synthetic (base_not_synthetic D (by simp))]
      exact Relation.ReflTransGen.single ((bases_mergedFlat D).mpr (Or.inl rfl))
    · rw [D.toWrapperFamily.phi_of_not_synthetic (base_not_synthetic D (by simp))]
      exact Relation.ReflTransGen.single
        ((bases_mergedFlat D).mpr (Or.inr (Or.inl rfl)))

/-- Ground-hop simulation, mergedRight side into mergedFlat. -/
theorem ground_mergedRight_mergedFlat :
    ∀ X ∈ ({D.mergedRight, D.rightPair} : Set Label), ∀ t,
      Bases D.Inh (D.syntheticRoot X) t →
      Relation.ReflTransGen (Bases D.Inh) (D.syntheticRoot D.mergedFlat)
        (D.toWrapperFamily.phi {D.mergedRight, D.rightPair}
          (D.syntheticRoot D.mergedFlat) t) := by
  intro X hX t hb
  rcases Set.mem_insert_iff.mp hX with rfl | hX
  · rcases (bases_mergedRight D).mp hb with rfl | rfl
    · rw [D.toWrapperFamily.phi_of_not_synthetic (base_not_synthetic D (by simp))]
      exact Relation.ReflTransGen.single ((bases_mergedFlat D).mpr (Or.inl rfl))
    · rw [D.phi_syntheticRoot_mem (by simp)]
  · obtain rfl := Set.mem_singleton_iff.mp hX
    rcases (bases_rightPair D).mp hb with rfl | rfl
    · rw [D.toWrapperFamily.phi_of_not_synthetic (base_not_synthetic D (by simp))]
      exact Relation.ReflTransGen.single
        ((bases_mergedFlat D).mpr (Or.inr (Or.inl rfl)))
    · rw [D.toWrapperFamily.phi_of_not_synthetic (base_not_synthetic D (by simp))]
      exact Relation.ReflTransGen.single
        ((bases_mergedFlat D).mpr (Or.inr (Or.inr rfl)))

/-- Ground-hop simulation, mergedFlat side into mergedLeft. -/
theorem ground_mergedFlat_mergedLeft :
    ∀ X ∈ ({D.mergedFlat} : Set Label), ∀ t,
      Bases D.Inh (D.syntheticRoot X) t →
      Relation.ReflTransGen (Bases D.Inh) (D.syntheticRoot D.mergedLeft)
        (D.toWrapperFamily.phi {D.mergedFlat} (D.syntheticRoot D.mergedLeft) t) := by
  intro X hX t hb
  obtain rfl := Set.mem_singleton_iff.mp hX
  rcases (bases_mergedFlat D).mp hb with rfl | rfl | rfl
  · rw [D.toWrapperFamily.phi_of_not_synthetic (base_not_synthetic D (by simp))]
    exact Relation.ReflTransGen.tail
      (Relation.ReflTransGen.single ((bases_mergedLeft D).mpr (Or.inl rfl)))
      ((bases_leftPair D).mpr (Or.inl rfl))
  · rw [D.toWrapperFamily.phi_of_not_synthetic (base_not_synthetic D (by simp))]
    exact Relation.ReflTransGen.tail
      (Relation.ReflTransGen.single ((bases_mergedLeft D).mpr (Or.inl rfl)))
      ((bases_leftPair D).mpr (Or.inr rfl))
  · rw [D.toWrapperFamily.phi_of_not_synthetic (base_not_synthetic D (by simp))]
    exact Relation.ReflTransGen.single ((bases_mergedLeft D).mpr (Or.inr rfl))

/-- Ground-hop simulation, mergedFlat side into mergedRight. -/
theorem ground_mergedFlat_mergedRight :
    ∀ X ∈ ({D.mergedFlat} : Set Label), ∀ t,
      Bases D.Inh (D.syntheticRoot X) t →
      Relation.ReflTransGen (Bases D.Inh) (D.syntheticRoot D.mergedRight)
        (D.toWrapperFamily.phi {D.mergedFlat} (D.syntheticRoot D.mergedRight) t) := by
  intro X hX t hb
  obtain rfl := Set.mem_singleton_iff.mp hX
  rcases (bases_mergedFlat D).mp hb with rfl | rfl | rfl
  · rw [D.toWrapperFamily.phi_of_not_synthetic (base_not_synthetic D (by simp))]
    exact Relation.ReflTransGen.single ((bases_mergedRight D).mpr (Or.inl rfl))
  · rw [D.toWrapperFamily.phi_of_not_synthetic (base_not_synthetic D (by simp))]
    exact Relation.ReflTransGen.tail
      (Relation.ReflTransGen.single ((bases_mergedRight D).mpr (Or.inr rfl)))
      ((bases_rightPair D).mpr (Or.inl rfl))
  · rw [D.toWrapperFamily.phi_of_not_synthetic (base_not_synthetic D (by simp))]
    exact Relation.ReflTransGen.tail
      (Relation.ReflTransGen.single ((bases_mergedRight D).mpr (Or.inr rfl)))
      ((bases_rightPair D).mpr (Or.inr rfl))

section Sides

/-- The hypothesis bundles of the simulation, one per ordered side pair: the
target wrapper, the root set, and the root set's outside closure. -/
theorem side_mergedLeft_mergedFlat :
    D.mergedFlat ∈ D.toWrapperFamily.wrappers ∧
    (∀ X ∈ ({D.mergedLeft, D.leftPair} : Set Label),
      X ∈ D.toWrapperFamily.wrappers) ∧
    D.toWrapperFamily.OutsideClosed {D.mergedLeft, D.leftPair} := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := wrapper_ne D
  refine ⟨D.mem_wrappers (by simp), ?_, D.outsideClosed ?_ ?_⟩
  · intro X hX
    rcases Set.mem_insert_iff.mp hX with rfl | hX
    · exact D.mem_wrappers (by simp)
    · obtain rfl := Set.mem_singleton_iff.mp hX
      exact D.mem_wrappers (by simp)
  · intro h
    exact absurd (Set.mem_insert _ _) h
  · intro _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h5, fun h => h1 h.symm⟩

theorem side_mergedRight_mergedFlat :
    D.mergedFlat ∈ D.toWrapperFamily.wrappers ∧
    (∀ X ∈ ({D.mergedRight, D.rightPair} : Set Label),
      X ∈ D.toWrapperFamily.wrappers) ∧
    D.toWrapperFamily.OutsideClosed {D.mergedRight, D.rightPair} := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := wrapper_ne D
  refine ⟨D.mem_wrappers (by simp), ?_, D.outsideClosed ?_ ?_⟩
  · intro X hX
    rcases Set.mem_insert_iff.mp hX with rfl | hX
    · exact D.mem_wrappers (by simp)
    · obtain rfl := Set.mem_singleton_iff.mp hX
      exact D.mem_wrappers (by simp)
  · intro _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h3, h1⟩
  · intro h
    exact absurd (Set.mem_insert _ _) h

theorem side_mergedFlat {Y : Label} (hY : Y ∈ D.wrapperLabels) :
    Y ∈ D.toWrapperFamily.wrappers ∧
    (∀ X ∈ ({D.mergedFlat} : Set Label), X ∈ D.toWrapperFamily.wrappers) ∧
    D.toWrapperFamily.OutsideClosed {D.mergedFlat} := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := wrapper_ne D
  refine ⟨D.mem_wrappers hY, ?_, D.outsideClosed ?_ ?_⟩
  · intro X hX
    obtain rfl := Set.mem_singleton_iff.mp hX
    exact D.mem_wrappers (by simp)
  · intro _
    simp only [Set.mem_singleton_iff]
    exact h4
  · intro _
    simp only [Set.mem_singleton_iff]
    exact h7

end Sides

/-- **thm:merge-associative**: for every path suffix `w`, the sets of
outside-subtree override components of `supers` agree at the three merged
paths, and so does their existence. Regrouping the deep merge of `p₁`, `p₂`,
`p₃` through either pair wrapper, or flattening it, is unobservable outside
the reserved subtree. -/
theorem merge_associative (w : Path Label) {v : Path Label}
    (hv : ¬ D.InSubtree v) :
    ((∃ c, Supers D.Inh (w ++ D.syntheticRoot D.mergedLeft) c v) ↔
      (∃ c, Supers D.Inh (w ++ D.syntheticRoot D.mergedFlat) c v)) ∧
    ((∃ c, Supers D.Inh (w ++ D.syntheticRoot D.mergedRight) c v) ↔
      (∃ c, Supers D.Inh (w ++ D.syntheticRoot D.mergedFlat) c v)) := by
  obtain ⟨hY1, hS1, hc1⟩ := side_mergedLeft_mergedFlat D
  obtain ⟨hY2, hS2, hc2⟩ := side_mergedRight_mergedFlat D
  obtain ⟨hY3, hS3, hc3⟩ := side_mergedFlat D (Y := D.mergedLeft) (by simp)
  obtain ⟨hY4, hS4, hc4⟩ := side_mergedFlat D (Y := D.mergedRight) (by simp)
  constructor
  · constructor
    · rintro ⟨c, hsup⟩
      exact D.toWrapperFamily.supers_transfer hY1 hS1 hc1
        (ground_mergedLeft_mergedFlat D) (Set.mem_insert _ _) w hsup hv
    · rintro ⟨c, hsup⟩
      exact D.toWrapperFamily.supers_transfer hY3 hS3 hc3
        (ground_mergedFlat_mergedLeft D) rfl w hsup hv
  · constructor
    · rintro ⟨c, hsup⟩
      exact D.toWrapperFamily.supers_transfer hY2 hS2 hc2
        (ground_mergedRight_mergedFlat D) (Set.mem_insert _ _) w hsup hv
    · rintro ⟨c, hsup⟩
      exact D.toWrapperFamily.supers_transfer hY4 hS4 hc4
        (ground_mergedFlat_mergedRight D) rfl w hsup hv

/-- thm:merge-associative, existence part: the three merged paths exist
together (nonempty `supers`, Section "Semantic Functions"). -/
theorem merge_associative_exists (w : Path Label) :
    ((supersSet D.Inh (w ++ D.syntheticRoot D.mergedLeft)).Nonempty ↔
      (supersSet D.Inh (w ++ D.syntheticRoot D.mergedFlat)).Nonempty) ∧
    ((supersSet D.Inh (w ++ D.syntheticRoot D.mergedRight)).Nonempty ↔
      (supersSet D.Inh (w ++ D.syntheticRoot D.mergedFlat)).Nonempty) := by
  obtain ⟨hY1, hS1, hc1⟩ := side_mergedLeft_mergedFlat D
  obtain ⟨hY2, hS2, hc2⟩ := side_mergedRight_mergedFlat D
  obtain ⟨hY3, hS3, hc3⟩ := side_mergedFlat D (Y := D.mergedLeft) (by simp)
  obtain ⟨hY4, hS4, hc4⟩ := side_mergedFlat D (Y := D.mergedRight) (by simp)
  constructor
  · exact ⟨D.toWrapperFamily.supers_nonempty_transfer hY1 hS1 hc1
        (ground_mergedLeft_mergedFlat D) (Set.mem_insert _ _) w,
      D.toWrapperFamily.supers_nonempty_transfer hY3 hS3 hc3
        (ground_mergedFlat_mergedLeft D) rfl w⟩
  · exact ⟨D.toWrapperFamily.supers_nonempty_transfer hY2 hS2 hc2
        (ground_mergedRight_mergedFlat D) (Set.mem_insert _ _) w,
      D.toWrapperFamily.supers_nonempty_transfer hY4 hS4 hc4
        (ground_mergedFlat_mergedRight D) rfl w⟩

end AssociativityDocument

end InheritanceCalculus
