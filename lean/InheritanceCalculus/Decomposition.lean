import InheritanceCalculus.Substitutability

/-!
# Decomposition

The paper's Theorem "Decomposition" (thm:decomposition), Appendix "Algebraic
Properties of Deep Merge", at the level of `inherits`.

## Setting

A document `original` (the paper's `D`) writes a mixin `M` at the nonroot path
`p = enclosing ⌢ mixinLabel`, the only definition of its path. Its leaves are
covered by parts indexed by `Part`: the references of part `i` at `p ⌢ v` are
`assigned i v`, and the paths written in part `i` are the suffixes `scope i`
(the paper's `W_i`). The document `decomposed` (the paper's `D'`) writes each
part at `q_i = enclosing ⌢ reserved ⌢ partLabel i`, with every reference that
leaves `M` shifted by one (`shift`), and replaces the absolute reference
`r = (|init(carrier)|, p)` at `carrier` by the absolute references to the
parts. As in the paper, the parts need only cover `M`; a partition of the
leaves of a finite `M` into at least two sets is a special case.

Paths are in the reversed representation of `Basic.lean`: the paper's
`p ⌢ v` is `v ++ p`.

## Proof

The paper's map `φ` is the relation `Image`: a path in which the reserved
label does not occur is its own image, `q_i ⌢ v` has the image `p ⌢ v`, and
the reserved root `enclosing ⌢ reserved` has the image `enclosing`.

- From `decomposed` to `original`: one induction over the derivations of
  `decomposed`, the paper's clauses (B1) to (B4) (`backwardMotive`).
- From `original` to `decomposed`: one induction over the derivations of
  `original`, the paper's clauses (F1) to (F4) (`forwardMotive`). A climb takes
  the version of `M` or of the parts at its top: where it passes `p`, by how
  it lands on `p`; where it stops inside `M`, by how its last site hosts the
  scope above. The version is then carried down level by level through the
  branch clause of eq:overrides. Where the paper reads the last step of a
  climb by strong induction on the Kleene rank, (F1) and (F2) export instead
  how the enclosing scope of an override component of the subtree is hosted in
  `decomposed`, so that one structural induction suffices.

The theorem is `decomposition`, with its existence form
`decomposition_exists`.
-/

set_option warningAsError true

namespace InheritanceCalculus

universe u v

/-- The shift of a reference written at `p ⌢ suffix` when it is copied into a
part: a reference whose climb leaves `M` (its index is at least the length of
`suffix`) climbs one more scope, the reserved one. -/
def shift {Label : Type u} (suffix : Path Label) (reference : Reference Label) :
    Reference Label :=
  if suffix.length ≤ reference.1 then (reference.1 + 1, reference.2) else reference

/-- The setting of thm:decomposition, axiomatized on the abstract primitive. -/
structure Decomposition (Label : Type u) (Part : Type v) where
  /-- The paper's `D`. -/
  original : Path Label → Option (Set (Reference Label))
  /-- The paper's `D'`. -/
  decomposed : Path Label → Option (Set (Reference Label))
  /-- The reserved label `R`. -/
  reserved : Label
  /-- The last label of `p`. -/
  mixinLabel : Label
  /-- `init(p)`, the scope that encloses `M` and the parts. -/
  enclosing : Path Label
  /-- The label `ℓ_i` of each part below the reserved scope. -/
  partLabel : Part → Label
  partLabel_injective : Function.Injective partLabel
  partLabel_ne_reserved : ∀ part, partLabel part ≠ reserved
  /-- The paper's `W_i`: the suffixes `v` with `q_i ⌢ v` written. -/
  scope : Part → Set (Path Label)
  /-- The references of part `i` written at `p ⌢ v`, the paper's `E_i`. -/
  assigned : Part → Path Label → Set (Reference Label)
  /-- The written path `o` that carries the absolute reference to `M`. -/
  carrier : Path Label
  /-- The paper's "`dom(inherits)` is prefix-closed". -/
  prefix_closed : ∀ (label : Label) (path : Path Label),
    (label :: path) ∈ Dom original → path ∈ Dom original
  /-- `R` occurs in no path of `D`. -/
  reserved_unwritten : ∀ path ∈ Dom original, reserved ∉ path
  /-- `R` occurs in no projection list of the references of `D`. -/
  reserved_not_in_references : ∀ (index : ℕ) (projection path : Path Label),
    MemRef original (index, projection) path → reserved ∉ projection
  mixin_written : mixinLabel :: enclosing ∈ Dom original
  /-- The paper's `overrides_D(p) = {p}`. -/
  mixin_sole_definition : ∀ override,
    Overrides original (mixinLabel :: enclosing) override → override = mixinLabel :: enclosing
  scope_nil : ∀ part, [] ∈ scope part
  scope_prefix : ∀ part (label : Label) (suffix : Path Label),
    label :: suffix ∈ scope part → suffix ∈ scope part
  scope_written : ∀ part suffix, suffix ∈ scope part →
    suffix ++ mixinLabel :: enclosing ∈ Dom original
  assigned_reference : ∀ part suffix reference, reference ∈ assigned part suffix →
    MemRef original reference (suffix ++ mixinLabel :: enclosing)
  assigned_scope : ∀ part suffix reference, reference ∈ assigned part suffix →
    suffix ∈ scope part
  /-- Every reference of `M` belongs to a part. -/
  assigned_cover : ∀ suffix reference,
    MemRef original reference (suffix ++ mixinLabel :: enclosing) →
      ∃ part, reference ∈ assigned part suffix
  /-- Every written path of `M` lies in some part, as holds whenever the
  subtree of `p` is finite. -/
  scope_cover : ∀ suffix, suffix ++ mixinLabel :: enclosing ∈ Dom original →
    ∃ part, suffix ∈ scope part
  carrier_outside : ∀ suffix, carrier ≠ suffix ++ mixinLabel :: enclosing
  /-- The carrier inherits `M` through the absolute reference `r`. -/
  carrier_reference :
    MemRef original (carrier.tail.length, mixinLabel :: enclosing) carrier
  decomposed_outside : ∀ path, reserved ∉ path → path ≠ carrier →
    decomposed path = original path
  decomposed_carrier : ∀ references, original carrier = some references →
    decomposed carrier = some
      ((references \ {(carrier.tail.length, mixinLabel :: enclosing)}) ∪
        Set.range fun part => (carrier.tail.length, partLabel part :: reserved :: enclosing))
  decomposed_reservedRoot : decomposed (reserved :: enclosing) = some ∅
  decomposed_part : ∀ part suffix, suffix ∈ scope part →
    decomposed (suffix ++ partLabel part :: reserved :: enclosing) =
      some (shift suffix '' assigned part suffix)
  decomposed_reserved_unwritten : ∀ path, reserved ∈ path →
    path ≠ reserved :: enclosing →
    (∀ part suffix, suffix ∈ scope part →
      path ≠ suffix ++ partLabel part :: reserved :: enclosing) →
    decomposed path = none

namespace Decomposition

variable {Label : Type u} {Part : Type v} (D : Decomposition Label Part)

/-- The paper's `p`. -/
abbrev mixinPath : Path Label := D.mixinLabel :: D.enclosing

/-- The paper's `r̄ = init(p) ⌢ R`. -/
abbrev reservedRoot : Path Label := D.reserved :: D.enclosing

/-- The paper's `q_i`. -/
abbrev partPath (part : Part) : Path Label := D.partLabel part :: D.reservedRoot

/-- The paper's `φ`, as a relation on the paths in which `R` does not occur,
the reserved root, and the paths of the parts. -/
inductive Image : Path Label → Path Label → Prop
  | outside {path : Path Label} (h : D.reserved ∉ path) : Image path path
  | part (part : Part) {suffix : Path Label} (h : D.reserved ∉ suffix) :
      Image (suffix ++ D.partPath part) (suffix ++ D.mixinPath)
  | reservedRoot : Image D.reservedRoot D.enclosing

/-! ## Facts about the written paths -/

theorem reserved_not_mem_mixinPath : D.reserved ∉ D.mixinPath :=
  D.reserved_unwritten _ D.mixin_written

theorem mixinLabel_ne_reserved : D.mixinLabel ≠ D.reserved := by
  intro h
  exact D.reserved_not_mem_mixinPath (by simp [h])

theorem reserved_not_mem_enclosing : D.reserved ∉ D.enclosing := by
  intro h
  exact D.reserved_not_mem_mixinPath (List.mem_cons_of_mem _ h)

theorem dom_append_original {suffix path : Path Label}
    (h : suffix ++ path ∈ Dom D.original) : path ∈ Dom D.original := by
  induction suffix with
  | nil => simpa using h
  | cons label rest ih => exact ih (D.prefix_closed label _ h)

theorem reserved_not_mem_of_scope {part : Part} {suffix : Path Label}
    (h : suffix ∈ D.scope part) : D.reserved ∉ suffix := by
  intro hmem
  exact D.reserved_unwritten _ (D.scope_written part suffix h) (List.mem_append_left _ hmem)

theorem reserved_mem_partPath_append (part : Part) (suffix : Path Label) :
    D.reserved ∈ suffix ++ D.partPath part := by
  simp

theorem carrier_reserved_free : D.reserved ∉ D.carrier :=
  D.reserved_unwritten _ D.carrier_reference.mem_dom

/-- A path in which `R` does not occur is written in `D'` exactly when it is
written in `D`. -/
theorem dom_decomposed_iff_of_reserved_free {path : Path Label}
    (h : D.reserved ∉ path) : path ∈ Dom D.decomposed ↔ path ∈ Dom D.original := by
  by_cases hcarrier : path = D.carrier
  · subst hcarrier
    obtain ⟨references, hreferences, -⟩ := D.carrier_reference
    simp [Dom, hreferences, D.decomposed_carrier references hreferences]
  · simp [Dom, D.decomposed_outside path h hcarrier]

/-- The reserved root and the part paths, by the position of `R`: a path
`suffix ++ q_i` with `R` free in `suffix` determines `suffix` and `i`. -/
theorem partPath_append_inj {part part' : Part} {suffix suffix' : Path Label}
    (hsuffix : D.reserved ∉ suffix) (hsuffix' : D.reserved ∉ suffix')
    (h : suffix ++ D.partPath part = suffix' ++ D.partPath part') :
    suffix = suffix' ∧ part = part' := by
  induction suffix generalizing suffix' with
  | nil =>
      cases suffix' with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at h
          exact ⟨rfl, D.partLabel_injective h.1⟩
      | cons label rest =>
          simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
          obtain ⟨-, h⟩ := h
          cases rest with
          | nil =>
              simp only [List.nil_append, List.cons.injEq] at h
              exact absurd h.1.symm (D.partLabel_ne_reserved part')
          | cons label' rest' =>
              simp only [List.cons_append, List.cons.injEq] at h
              exact absurd (by simp [h.1]) hsuffix'
  | cons label rest ih =>
      cases suffix' with
      | nil =>
          simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
          obtain ⟨-, h⟩ := h
          cases rest with
          | nil =>
              simp only [List.nil_append, List.cons.injEq] at h
              exact absurd h.1 (D.partLabel_ne_reserved part)
          | cons label' rest' =>
              simp only [List.cons_append, List.cons.injEq] at h
              exact absurd (by simp [← h.1]) hsuffix
      | cons label' rest' =>
          simp only [List.cons_append, List.cons.injEq] at h
          obtain ⟨rfl, h⟩ := h
          obtain ⟨rfl, rfl⟩ := ih (fun hm => hsuffix (List.mem_cons_of_mem _ hm))
            (fun hm => hsuffix' (List.mem_cons_of_mem _ hm)) h
          exact ⟨rfl, rfl⟩

theorem partPath_append_ne_reservedRoot (part : Part) (suffix : Path Label) :
    suffix ++ D.partPath part ≠ D.reservedRoot := by
  intro h
  have := congrArg List.length h
  simp at this
  omega

/-- The written paths of `D'` in which `R` occurs are the reserved root and the
paths of the parts. -/
theorem written_reserved {path : Path Label} (hwritten : path ∈ Dom D.decomposed)
    (hreserved : D.reserved ∈ path) :
    path = D.reservedRoot ∨
      ∃ part suffix, suffix ∈ D.scope part ∧ path = suffix ++ D.partPath part := by
  by_cases hroot : path = D.reservedRoot
  · exact Or.inl hroot
  by_cases hparts : ∃ part suffix, suffix ∈ D.scope part ∧ path = suffix ++ D.partPath part
  · exact Or.inr hparts
  exfalso
  refine hwritten (D.decomposed_reserved_unwritten path hreserved hroot ?_)
  intro part suffix hscope heq
  exact hparts ⟨part, suffix, hscope, heq⟩

/-- The only written path of `D'` whose innermost label is `R` is the reserved
root. -/
theorem written_reserved_head {path : Path Label}
    (hwritten : D.reserved :: path ∈ Dom D.decomposed) : path = D.enclosing := by
  rcases D.written_reserved hwritten List.mem_cons_self with h | ⟨part, suffix, hscope, h⟩
  · simpa using h
  · exfalso
    cases suffix with
    | nil =>
        simp only [List.nil_append, List.cons.injEq] at h
        exact D.partLabel_ne_reserved part h.1.symm
    | cons label rest =>
        simp only [List.cons_append, List.cons.injEq] at h
        exact D.reserved_not_mem_of_scope hscope (h.1 ▸ List.mem_cons_self)

/-! ## The relation `Image` -/

/-- The three alternatives of `Image`, as a characterization. -/
theorem image_iff {path image : Path Label} :
    D.Image path image ↔
      (D.reserved ∉ path ∧ image = path) ∨
      (∃ part suffix, D.reserved ∉ suffix ∧ path = suffix ++ D.partPath part ∧
        image = suffix ++ D.mixinPath) ∨
      (path = D.reservedRoot ∧ image = D.enclosing) := by
  constructor
  · intro h
    cases h with
    | outside hfree => exact Or.inl ⟨hfree, rfl⟩
    | part part hsuffix => exact Or.inr (Or.inl ⟨part, _, hsuffix, rfl, rfl⟩)
    | reservedRoot => exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · rintro (⟨hfree, rfl⟩ | ⟨part, suffix, hsuffix, rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Image.outside hfree
    · exact Image.part part hsuffix
    · exact Image.reservedRoot

theorem reserved_mem_reservedRoot : D.reserved ∈ D.reservedRoot := List.mem_cons_self

theorem image_functional {path image image' : Path Label}
    (h : D.Image path image) (h' : D.Image path image') : image = image' := by
  rcases D.image_iff.mp h with ⟨hfree, rfl⟩ | ⟨part, suffix, hsuffix, rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases D.image_iff.mp h' with ⟨-, rfl⟩ | ⟨part', suffix', -, heq, -⟩ | ⟨heq, -⟩
    · rfl
    · exact absurd (heq ▸ D.reserved_mem_partPath_append part' suffix') hfree
    · exact absurd (heq ▸ D.reserved_mem_reservedRoot) hfree
  · rcases D.image_iff.mp h' with ⟨hfree, -⟩ | ⟨part', suffix', hsuffix', heq, rfl⟩ | ⟨heq, -⟩
    · exact absurd (D.reserved_mem_partPath_append part suffix) hfree
    · obtain ⟨rfl, rfl⟩ := D.partPath_append_inj hsuffix hsuffix' heq
      rfl
    · exact absurd heq (D.partPath_append_ne_reservedRoot part suffix)
  · rcases D.image_iff.mp h' with ⟨hfree, -⟩ | ⟨part', suffix', -, heq, -⟩ | ⟨-, rfl⟩
    · exact absurd D.reserved_mem_reservedRoot hfree
    · exact absurd heq.symm (D.partPath_append_ne_reservedRoot part' suffix')
    · rfl

theorem image_nil {image : Path Label} (h : D.Image [] image) : image = [] := by
  rcases D.image_iff.mp h with ⟨-, rfl⟩ | ⟨part, suffix, -, heq, -⟩ | ⟨heq, -⟩
  · rfl
  · simp at heq
  · simp at heq

/-- The image of a nonroot path other than the reserved root: the enclosing
scopes correspond, and the innermost label is kept except at a part root,
whose image is `p`. -/
theorem image_cons {label : Label} {path image : Path Label}
    (h : D.Image (label :: path) image) (hne : label :: path ≠ D.reservedRoot) :
    ∃ image', D.Image path image' ∧
      (image = label :: image' ∨
        ∃ part, label = D.partLabel part ∧ path = D.reservedRoot ∧ image = D.mixinPath ∧
          image' = D.enclosing) := by
  rcases D.image_iff.mp h with ⟨hfree, rfl⟩ | ⟨part, suffix, hsuffix, heq, rfl⟩ | ⟨heq, -⟩
  · exact ⟨path, Image.outside (fun hm => hfree (List.mem_cons_of_mem _ hm)), Or.inl rfl⟩
  · cases suffix with
    | nil =>
        simp only [List.nil_append, List.cons.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact ⟨D.enclosing, Image.reservedRoot, Or.inr ⟨part, rfl, rfl, by simp, rfl⟩⟩
    | cons label' rest =>
        simp only [List.cons_append, List.cons.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact ⟨rest ++ D.mixinPath,
          Image.part part (fun hm => hsuffix (List.mem_cons_of_mem _ hm)), Or.inl rfl⟩
  · exact absurd heq hne

/-- A path in `A` whose innermost label is `R` is the reserved root. -/
theorem image_reserved_head {path image : Path Label}
    (h : D.Image (D.reserved :: path) image) : path = D.enclosing := by
  rcases D.image_iff.mp h with ⟨hfree, -⟩ | ⟨part, suffix, hsuffix, heq, -⟩ | ⟨heq, -⟩
  · exact absurd List.mem_cons_self hfree
  · cases suffix with
    | nil =>
        simp only [List.nil_append, List.cons.injEq] at heq
        exact absurd heq.1.symm (D.partLabel_ne_reserved part)
    | cons label rest =>
        simp only [List.cons_append, List.cons.injEq] at heq
        exact absurd (by simp [heq.1]) hsuffix
  · simp only [List.cons.injEq] at heq
    exact heq.2

/-- A path in `A` of the shape `ℓ :: r̄` is a part root. -/
theorem image_reservedRoot_cons {label : Label} {image : Path Label}
    (h : D.Image (label :: D.reservedRoot) image) :
    ∃ part, label = D.partLabel part ∧ image = D.mixinPath := by
  rcases D.image_iff.mp h with ⟨hfree, -⟩ | ⟨part, suffix, -, heq, rfl⟩ | ⟨heq, -⟩
  · exact absurd (by simp) hfree
  · cases suffix with
    | nil =>
        simp only [List.nil_append, List.cons.injEq] at heq
        exact ⟨part, heq.1, by simp⟩
    | cons label' rest =>
        simp only [List.cons_append, List.cons.injEq] at heq
        have := congrArg List.length heq.2
        simp at this
        omega
  · have := congrArg List.length heq
    simp at this

/-- Appending a projection list free of `R` keeps the relation, except on the
reserved root. -/
theorem image_append {path image projection : Path Label} (h : D.Image path image)
    (hprojection : D.reserved ∉ projection) (hne : path ≠ D.reservedRoot) :
    D.Image (projection ++ path) (projection ++ image) := by
  rcases D.image_iff.mp h with ⟨hfree, rfl⟩ | ⟨part, suffix, hsuffix, rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Image.outside (by simp [hprojection, hfree])
  · rw [← List.append_assoc, ← List.append_assoc]
    exact Image.part part (by simp [hprojection, hsuffix])
  · exact absurd rfl hne

/-- A written extension of a path of `A` other than the reserved root. -/
theorem image_written_cons {label : Label} {path image : Path Label}
    (h : D.Image path image) (hne : path ≠ D.reservedRoot)
    (hcons : label :: path ≠ D.reservedRoot) (hwritten : label :: path ∈ Dom D.decomposed) :
    D.Image (label :: path) (label :: image) ∧ label :: image ∈ Dom D.original := by
  rcases D.image_iff.mp h with ⟨hfree, rfl⟩ | ⟨part, suffix, hsuffix, rfl, rfl⟩ | ⟨rfl, rfl⟩
  · by_cases hlabel : label = D.reserved
    · subst hlabel
      exact absurd (D.written_reserved_head hwritten) (fun h => hcons (by rw [h]))
    · have hfree' : D.reserved ∉ label :: image := by
        simp [hfree, Ne.symm hlabel]
      exact ⟨Image.outside hfree', (D.dom_decomposed_iff_of_reserved_free hfree').mp hwritten⟩
  · have hlabel : label ≠ D.reserved := by
      rintro rfl
      have henclosing := D.written_reserved_head hwritten
      exact D.reserved_not_mem_enclosing (henclosing ▸ D.reserved_mem_partPath_append _ _)
    have hfree : D.reserved ∉ label :: suffix := by simp [Ne.symm hlabel, hsuffix]
    rw [← List.cons_append] at hwritten
    rcases D.written_reserved hwritten (by simp) with hroot | ⟨part', suffix', hscope, heq⟩
    · exact absurd hroot (D.partPath_append_ne_reservedRoot part _)
    · obtain ⟨heqsuffix, rfl⟩ :=
        D.partPath_append_inj hfree (D.reserved_not_mem_of_scope hscope) heq
      rw [← heqsuffix] at hscope
      refine ⟨?_, ?_⟩
      · rw [← List.cons_append, ← List.cons_append]
        exact Image.part part hfree
      · rw [← List.cons_append]
        exact D.scope_written part _ hscope
  · exact absurd rfl hne

/-- `image_cons` without the case split: the image is nonroot, and the
enclosing scopes correspond. -/
theorem image_cons_shape {label : Label} {path image : Path Label}
    (h : D.Image (label :: path) image) (hne : label :: path ≠ D.reservedRoot) :
    ∃ imageLabel image', image = imageLabel :: image' ∧ D.Image path image' := by
  obtain ⟨image', himage, hshape⟩ := D.image_cons h hne
  rcases hshape with rfl | ⟨part, -, -, rfl, rfl⟩
  · exact ⟨label, image', rfl, himage⟩
  · exact ⟨D.mixinLabel, D.enclosing, rfl, himage⟩

/-- A path in `A` whose innermost label is `R` is the reserved root. -/
theorem image_reserved_cons_eq {path image : Path Label}
    (h : D.Image (D.reserved :: path) image) : D.reserved :: path = D.reservedRoot := by
  rw [D.image_reserved_head h]

theorem append_ne_reservedRoot {projection path : Path Label}
    (hprojection : D.reserved ∉ projection) (hpath : path ≠ D.reservedRoot) :
    projection ++ path ≠ D.reservedRoot := by
  cases projection with
  | nil => simpa using hpath
  | cons label rest =>
      intro h
      simp only [List.cons_append, List.cons.injEq] at h
      exact hprojection (by simp [h.1])

theorem partPath_ne_reservedRoot (part : Part) : D.partPath part ≠ D.reservedRoot := by
  intro h
  have := congrArg List.length h
  simp at this

theorem image_partPath (part : Part) : D.Image (D.partPath part) D.mixinPath := by
  simpa using Image.part (D := D) part (suffix := []) (by simp)

/-! ## Written paths are their own overrides -/

/-- In a document whose `dom(inherits)` is prefix-closed, a written path is its
own override. -/
theorem overrides_written_self_of_prefix_closed
    (inheritsFunction : Path Label → Option (Set (Reference Label)))
    (hprefix : ∀ (label : Label) (path : Path Label),
      (label :: path) ∈ Dom inheritsFunction → path ∈ Dom inheritsFunction) :
    ∀ {path : Path Label}, path ∈ Dom inheritsFunction → Overrides inheritsFunction path path
  | [], _ => Fact.overridesRoot
  | label :: rest, hwritten => by
      have hrest := overrides_written_self_of_prefix_closed inheritsFunction hprefix
        (hprefix label rest hwritten)
      have hsupers : Supers inheritsFunction rest rest.tail rest := by
        cases rest with
        | nil => exact Fact.supersRoot
        | cons _ _ => exact Fact.supersStep (Fact.basesStarRefl _) hrest
      exact Fact.overridesSelf hsupers hwritten

theorem prefix_closed_decomposed (label : Label) (path : Path Label)
    (hwritten : label :: path ∈ Dom D.decomposed) : path ∈ Dom D.decomposed := by
  by_cases hfree : D.reserved ∈ label :: path
  · rcases D.written_reserved hwritten hfree with hroot | ⟨part, suffix, hscope, heq⟩
    · simp only [List.cons.injEq] at hroot
      obtain ⟨-, rfl⟩ := hroot
      exact (D.dom_decomposed_iff_of_reserved_free D.reserved_not_mem_enclosing).mpr
        (D.prefix_closed _ _ D.mixin_written)
    · cases suffix with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at heq
          obtain ⟨-, rfl⟩ := heq
          simp [Dom, D.decomposed_reservedRoot]
      | cons label' rest =>
          simp only [List.cons_append, List.cons.injEq] at heq
          obtain ⟨-, rfl⟩ := heq
          have hscope' := D.scope_prefix part label' rest hscope
          simp [Dom, D.decomposed_part part rest hscope']
  · have hpathfree : D.reserved ∉ path := fun hm => hfree (List.mem_cons_of_mem _ hm)
    exact (D.dom_decomposed_iff_of_reserved_free hpathfree).mpr
      (D.prefix_closed label path ((D.dom_decomposed_iff_of_reserved_free hfree).mp hwritten))

theorem overrides_original_mixin : Overrides D.original D.mixinPath D.mixinPath :=
  overrides_written_self_of_prefix_closed D.original D.prefix_closed D.mixin_written

/-! ## Ground facts at the reserved root and the part roots (K1, K2) -/

theorem overrides_reservedRoot {override : Path Label}
    (h : Overrides D.decomposed D.reservedRoot override) : override = D.reservedRoot := by
  obtain ⟨-, branch, -, hdom, hoverride⟩ := (overrides_cons_iff D.decomposed).mp h
  rw [D.written_reserved_head hdom] at hoverride
  rcases hoverride with h | h <;> exact h

theorem not_bases_reservedRoot {target : Path Label} :
    ¬ Bases D.decomposed D.reservedRoot target := by
  intro h
  obtain ⟨override, hoverride, index, projection, hreference, -⟩ :=
    (bases_cons_iff D.decomposed).mp h
  rw [D.overrides_reservedRoot hoverride] at hreference
  obtain ⟨references, hreferences, hmem⟩ := hreference
  rw [D.decomposed_reservedRoot] at hreferences
  cases hreferences
  exact hmem

theorem basesStar_reservedRoot {target : Path Label}
    (h : BasesStar D.decomposed D.reservedRoot target) : target = D.reservedRoot := by
  have hchain := (basesStar_iff_reflTransGen D.decomposed).mp h
  clear h
  induction hchain with
  | refl => rfl
  | tail _ hstep ih =>
      subst ih
      exact absurd hstep D.not_bases_reservedRoot

/-- (K1) `supers_{D'}(r̄) = {(init(p), r̄)}`, the inclusion. -/
theorem supers_reservedRoot {site override : Path Label}
    (h : Supers D.decomposed D.reservedRoot site override) :
    site = D.enclosing ∧ override = D.reservedRoot := by
  obtain ⟨baseLabel, hchain, hoverride⟩ := (supers_cons_iff D.decomposed).mp h
  have hbase := D.basesStar_reservedRoot hchain
  simp only [List.cons.injEq] at hbase
  obtain ⟨rfl, rfl⟩ := hbase
  exact ⟨rfl, D.overrides_reservedRoot hoverride⟩

/-- (K1) `supers_{D'}(r̄) = {(init(p), r̄)}`, the pair itself. -/
theorem supers_reservedRoot_self :
    Supers D.decomposed D.reservedRoot D.enclosing D.reservedRoot := by
  have henclosing : D.enclosing ∈ Dom D.decomposed :=
    (D.dom_decomposed_iff_of_reserved_free D.reserved_not_mem_enclosing).mpr
      (D.prefix_closed _ _ D.mixin_written)
  have hself := overrides_written_self_of_prefix_closed D.decomposed
    D.prefix_closed_decomposed henclosing
  have hsupers : Supers D.decomposed D.enclosing D.enclosing.tail D.enclosing := by
    cases henclosingShape : D.enclosing with
    | nil => exact Fact.supersRoot
    | cons _ _ =>
        rw [henclosingShape] at hself
        exact Fact.supersStep (Fact.basesStarRefl _) hself
  have hroot : D.reservedRoot ∈ Dom D.decomposed := by simp [Dom, D.decomposed_reservedRoot]
  exact Fact.supersStep (Fact.basesStarRefl _) (Fact.overridesSelf hsupers hroot)

/-- (K2) The only override of a part root is itself. -/
theorem overrides_partPath {part : Part} {override : Path Label}
    (h : Overrides D.decomposed (D.partPath part) override) : override = D.partPath part := by
  obtain ⟨_, branch, hsupers, _, hoverride⟩ := (overrides_cons_iff D.decomposed).mp h
  rw [(D.supers_reservedRoot hsupers).2] at hoverride
  rcases hoverride with h | h <;> exact h

/-! ## Climbs through the reserved root -/

/-- A climb of `n` steps from the definition site `d` visits the reserved root. -/
def Passes (definitionSite : Path Label) (steps : ℕ) : Prop :=
  ∃ index < steps, definitionSite.drop index = D.reservedRoot

theorem not_passes_zero (definitionSite : Path Label) : ¬ D.Passes definitionSite 0 := by
  rintro ⟨index, hindex, -⟩
  exact Nat.not_lt_zero _ hindex

theorem passes_succ {label : Label} {definitionSite : Path Label} {steps : ℕ} :
    D.Passes (label :: definitionSite) (steps + 1) ↔
      label :: definitionSite = D.reservedRoot ∨ D.Passes definitionSite steps := by
  constructor
  · rintro ⟨index, hindex, hdrop⟩
    cases index with
    | zero => exact Or.inl hdrop
    | succ index => exact Or.inr ⟨index, by omega, by simpa using hdrop⟩
  · rintro (h | ⟨index, hindex, hdrop⟩)
    · exact ⟨0, by omega, h⟩
    · exact ⟨index + 1, by omega, by simpa using hdrop⟩

theorem drop_reserved_free {path : Path Label} (hfree : D.reserved ∉ path) (index : ℕ) :
    D.reserved ∉ path.drop index :=
  fun hm => hfree (List.mem_of_mem_drop hm)

theorem not_passes_of_reserved_free {definitionSite : Path Label}
    (hfree : D.reserved ∉ definitionSite) (steps : ℕ) : ¬ D.Passes definitionSite steps := by
  rintro ⟨index, -, hdrop⟩
  exact D.drop_reserved_free hfree index (hdrop ▸ D.reserved_mem_reservedRoot)

theorem passes_reservedRoot {steps : ℕ} : D.Passes D.reservedRoot steps ↔ 0 < steps := by
  constructor
  · rintro ⟨index, hindex, -⟩
    omega
  · intro h
    exact ⟨0, h, rfl⟩

theorem passes_part {part : Part} {suffix : Path Label} {steps : ℕ} :
    D.Passes (suffix ++ D.partPath part) steps ↔ suffix.length + 1 < steps := by
  constructor
  · rintro ⟨index, hindex, hdrop⟩
    have := congrArg List.length hdrop
    simp at this
    omega
  · intro h
    refine ⟨suffix.length + 1, h, ?_⟩
    rw [List.drop_append]
    simp

/-- A suffix of a path that is a part root is reached after dropping exactly
the suffix written below the part root. -/
theorem drop_eq_partPath {path : Path Label} {part : Part} {index : ℕ}
    (hdrop : path.drop index = D.partPath part) :
    index + (D.partPath part).length = path.length := by
  have := congrArg List.length hdrop
  simp only [List.length_drop] at this
  have hpos : 0 < (D.partPath part).length := by simp
  omega

/-! ## The references of `D'` -/

theorem memRef_decomposed_outside {reference : Reference Label} {path : Path Label}
    (hfree : D.reserved ∉ path) (hcarrier : path ≠ D.carrier)
    (h : MemRef D.decomposed reference path) : MemRef D.original reference path := by
  rw [MemRef, ← D.decomposed_outside path hfree hcarrier]
  exact h

theorem memRef_decomposed_carrier {reference : Reference Label}
    (h : MemRef D.decomposed reference D.carrier) :
    MemRef D.original reference D.carrier ∨
      ∃ part, reference = (D.carrier.tail.length, D.partPath part) := by
  obtain ⟨references, hreferences, -⟩ := D.carrier_reference
  obtain ⟨decomposedReferences, hdecomposed, hmem⟩ := h
  rw [D.decomposed_carrier references hreferences] at hdecomposed
  cases hdecomposed
  rcases hmem with ⟨hmem, -⟩ | ⟨part, rfl⟩
  · exact Or.inl ⟨references, hreferences, hmem⟩
  · exact Or.inr ⟨part, rfl⟩

theorem memRef_original_carrier {reference : Reference Label}
    (h : MemRef D.original reference D.carrier)
    (hne : reference ≠ (D.carrier.tail.length, D.mixinPath)) :
    MemRef D.decomposed reference D.carrier := by
  obtain ⟨references, hreferences, hmem⟩ := h
  exact ⟨_, D.decomposed_carrier references hreferences, Or.inl ⟨hmem, hne⟩⟩

theorem memRef_decomposed_part {reference : Reference Label} {part : Part}
    {suffix : Path Label} (hfree : D.reserved ∉ suffix)
    (h : MemRef D.decomposed reference (suffix ++ D.partPath part)) :
    suffix ∈ D.scope part ∧
      ∃ assignedReference ∈ D.assigned part suffix, shift suffix assignedReference = reference := by
  rcases D.written_reserved h.mem_dom (D.reserved_mem_partPath_append part suffix) with
    hroot | ⟨part', suffix', hscope, heq⟩
  · exact absurd hroot (D.partPath_append_ne_reservedRoot part suffix)
  · obtain ⟨rfl, rfl⟩ := D.partPath_append_inj hfree (D.reserved_not_mem_of_scope hscope) heq
    obtain ⟨references, hreferences, hmem⟩ := h
    rw [D.decomposed_part part suffix hscope] at hreferences
    cases hreferences
    exact ⟨hscope, hmem⟩

/-! ## From `D'` to `D`: clauses (B1) to (B4) -/

/-- The paper's clauses (B1) to (B4), with the bookkeeping that keeps the
induction closed: no override component, base or chain end is the reserved
root, a site at the reserved root belongs to a part root, and a climb that
ends at the reserved root has just passed a part root. -/
def backwardMotive : Atom Label → Prop
  | .supers path site override =>
      ∀ image, D.Image path image → path ≠ D.reservedRoot →
        override ≠ D.reservedRoot ∧
        (site = D.reservedRoot → ∃ part, override = D.partPath part) ∧
        ∃ siteImage overrideImage, D.Image site siteImage ∧ D.Image override overrideImage ∧
          Supers D.original image siteImage overrideImage
  | .overrides path override =>
      ∀ image, D.Image path image → path ≠ D.reservedRoot →
        override ≠ D.reservedRoot ∧
        ∃ overrideImage, D.Image override overrideImage ∧
          Overrides D.original image overrideImage
  | .bases path target =>
      ∀ image, D.Image path image → path ≠ D.reservedRoot →
        target ≠ D.reservedRoot ∧
        ∃ targetImage, D.Image target targetImage ∧ Bases D.original image targetImage
  | .basesStar path target =>
      ∀ image, D.Image path image → path ≠ D.reservedRoot →
        target ≠ D.reservedRoot ∧
        ∃ targetImage, D.Image target targetImage ∧ BasesStar D.original image targetImage
  | .this source definitionSite steps target =>
      ∀ sourceImage definitionSiteImage, D.Image source sourceImage →
        D.Image definitionSite definitionSiteImage →
        (0 < steps → target = D.reservedRoot →
          ∃ part, definitionSite.drop (steps - 1) = D.partPath part) ∧
        ∃ targetImage, D.Image target targetImage ∧
          (D.Passes definitionSite steps →
            This D.original sourceImage definitionSiteImage (steps - 1) targetImage) ∧
          (¬ D.Passes definitionSite steps →
            This D.original sourceImage definitionSiteImage steps targetImage)

/-- A climb that ends at the reserved root after at least one step. -/
theorem drop_partPath_reserved_free {definitionSite : Path Label} {part : Part}
    (hfree : D.reserved ∉ definitionSite) (index : ℕ) :
    definitionSite.drop index ≠ D.partPath part := by
  intro h
  exact D.drop_reserved_free hfree index (h ▸ by simp)

theorem backward {atom : Atom Label} (h : Fact D.decomposed atom) : D.backwardMotive atom := by
  induction h with
  | supersRoot =>
      intro image himage _
      rw [D.image_nil himage]
      refine ⟨by simp, fun h => absurd h (by simp), [], [], Image.outside (by simp),
        Image.outside (by simp), Fact.supersRoot⟩
  | @supersStep pathLabel path baseLabel site override hchain hoverride ihChain ihOverride =>
      intro image himage hne
      obtain ⟨hbaseNe, baseImage, hbase, hchainImage⟩ := ihChain image himage hne
      obtain ⟨hoverrideNe, overrideImage, hoverrideImage, hoverridesImage⟩ :=
        ihOverride baseImage hbase hbaseNe
      obtain ⟨baseImageLabel, siteImage, rfl, hsite⟩ := D.image_cons_shape hbase hbaseNe
      obtain ⟨imageLabel, imageRest, rfl, -⟩ := D.image_cons_shape himage hne
      refine ⟨hoverrideNe, ?_, siteImage, overrideImage, hsite, hoverrideImage,
        Fact.supersStep hchainImage hoverridesImage⟩
      intro hsiteRoot
      subst hsiteRoot
      obtain ⟨part, rfl, -⟩ := D.image_reservedRoot_cons hbase
      exact ⟨part, D.overrides_partPath hoverride⟩
  | overridesRoot =>
      intro image himage _
      rw [D.image_nil himage]
      exact ⟨by simp, [], Image.outside (by simp), Fact.overridesRoot⟩
  | @overridesSelf path site branch label hsupers hdom ih =>
      intro image himage hne
      refine ⟨hne, image, himage, ?_⟩
      by_cases hpath : path = D.reservedRoot
      · subst hpath
        obtain ⟨part, rfl, rfl⟩ := D.image_reservedRoot_cons himage
        exact D.overrides_original_mixin
      · obtain ⟨image', himage', hshape⟩ := D.image_cons himage hne
        rcases hshape with rfl | ⟨_, _, hroot, _⟩
        · obtain ⟨hbranchNe, -, siteImage, branchImage, -, hbranch, hsupersImage⟩ :=
            ih image' himage' hpath
          have hcons : label :: branch ≠ D.reservedRoot := by
            intro heq
            simp only [List.cons.injEq] at heq
            obtain ⟨rfl, -⟩ := heq
            exact hne (D.image_reserved_cons_eq himage)
          obtain ⟨-, hdomImage⟩ := D.image_written_cons hbranch hbranchNe hcons hdom
          exact Fact.overridesSelf hsupersImage hdomImage
        · exact absurd hroot hpath
  | @overridesBranch path site branch label hsupers hdom ih =>
      intro image himage hne
      by_cases hpath : path = D.reservedRoot
      · subst hpath
        obtain ⟨part, rfl, rfl⟩ := D.image_reservedRoot_cons himage
        rw [(D.supers_reservedRoot hsupers).2]
        exact ⟨D.partPath_ne_reservedRoot part, D.mixinPath, D.image_partPath part,
          D.overrides_original_mixin⟩
      · obtain ⟨image', himage', hshape⟩ := D.image_cons himage hne
        rcases hshape with rfl | ⟨_, _, hroot, _⟩
        · obtain ⟨hbranchNe, -, siteImage, branchImage, -, hbranch, hsupersImage⟩ :=
            ih image' himage' hpath
          have hcons : label :: branch ≠ D.reservedRoot := by
            intro heq
            simp only [List.cons.injEq] at heq
            obtain ⟨rfl, -⟩ := heq
            exact hne (D.image_reserved_cons_eq himage)
          obtain ⟨hbranchImage, hdomImage⟩ := D.image_written_cons hbranch hbranchNe hcons hdom
          exact ⟨hcons, label :: branchImage, hbranchImage,
            Fact.overridesBranch hsupersImage hdomImage⟩
        · exact absurd hroot hpath
  | @basesStep path current label overrideLabel overrideRest index projection
      hoverride hreference hthis ihOverride ihThis =>
      intro image himage hne
      obtain ⟨hoverrideNe, overrideImage, hoverrideImageRel, hoverridesImage⟩ :=
        ihOverride image himage hne
      obtain ⟨imageLabel, image', rfl, himage'⟩ := D.image_cons_shape himage hne
      -- At a part root, the only override is the part root itself.
      have hpartRoot : path = D.reservedRoot →
          ∃ part, overrideLabel :: overrideRest = D.partPath part := by
        intro hpath
        subst hpath
        obtain ⟨part, rfl, -⟩ := D.image_reservedRoot_cons himage
        exact ⟨part, D.overrides_partPath hoverride⟩
      rcases D.image_iff.mp hoverrideImageRel with
        ⟨hfree, rfl⟩ | ⟨part, suffix, hsuffix, hoverrideEq, rfl⟩ | ⟨hroot, -⟩
      · -- The override is outside the reserved subtree.
        have hrestFree : D.reserved ∉ overrideRest := fun hm => hfree (List.mem_cons_of_mem _ hm)
        have hpathNe : path ≠ D.reservedRoot := by
          intro hpath
          obtain ⟨part, heq⟩ := hpartRoot hpath
          exact hfree (heq ▸ by simp)
        have horiginal : MemRef D.original (index, projection) (overrideLabel :: overrideRest) ∨
            ∃ part, (index, projection) =
              (D.carrier.tail.length, D.partPath part) ∧ overrideLabel :: overrideRest = D.carrier := by
          by_cases hcarrier : overrideLabel :: overrideRest = D.carrier
          · rw [hcarrier] at hreference ⊢
            rcases D.memRef_decomposed_carrier hreference with h | ⟨part, h⟩
            · exact Or.inl h
            · exact Or.inr ⟨part, h, rfl⟩
          · exact Or.inl (D.memRef_decomposed_outside hfree hcarrier hreference)
        rcases horiginal with horiginal | ⟨part, hreferenceEq, hcarrier⟩
        · have hprojection := D.reserved_not_in_references _ _ _ horiginal
          obtain ⟨hclause, currentImage, hcurrent, -, hnoPass⟩ :=
            ihThis image' overrideRest himage' (Image.outside hrestFree)
          have hthisImage := hnoPass (D.not_passes_of_reserved_free hrestFree index)
          have hcurrentNe : current ≠ D.reservedRoot := by
            intro hcurrentRoot
            cases index with
            | zero =>
                rw [(this_zero_iff D.decomposed).mp hthis] at hcurrentRoot
                exact hpathNe hcurrentRoot
            | succ index =>
                obtain ⟨part, hdrop⟩ := hclause (by omega) hcurrentRoot
                exact D.drop_partPath_reserved_free hrestFree _ hdrop
          exact ⟨D.append_ne_reservedRoot hprojection hcurrentNe, projection ++ currentImage,
            D.image_append hcurrent hprojection hcurrentNe,
            Fact.basesStep hoverridesImage horiginal hthisImage⟩
        · simp only [Prod.mk.injEq] at hreferenceEq
          obtain ⟨rfl, rfl⟩ := hreferenceEq
          have hcarrierTail : D.carrier.tail = overrideRest := by rw [← hcarrier]; rfl
          rw [hcarrierTail] at hthis
          have hcurrentNil := this_full_length_root D.decomposed hoverride hthis
          subst hcurrentNil
          obtain ⟨-, currentImage, hcurrent, -, hnoPass⟩ :=
            ihThis image' overrideRest himage' (Image.outside hrestFree)
          rw [D.image_nil hcurrent] at hnoPass
          have hthisImage := hnoPass (D.not_passes_of_reserved_free hrestFree _)
          have hreferenceImage := D.carrier_reference
          rw [← hcarrier, show (overrideLabel :: overrideRest).tail = overrideRest from rfl]
            at hreferenceImage
          rw [hcarrierTail] at hthisImage
          refine ⟨by rw [List.append_nil]; exact D.partPath_ne_reservedRoot part, D.mixinPath,
            by simpa using D.image_partPath part, ?_⟩
          simpa using Fact.basesStep hoverridesImage hreferenceImage hthisImage
      · -- The override is a path of a part.
        rw [hoverrideEq] at hreference
        obtain ⟨hscope, assignedReference, hassigned, hshift⟩ :=
          D.memRef_decomposed_part hsuffix hreference
        have horiginal := D.assigned_reference part suffix assignedReference hassigned
        obtain ⟨assignedIndex, assignedProjection⟩ := assignedReference
        have hprojectionEq : assignedProjection = projection := by
          unfold shift at hshift
          split_ifs at hshift <;> simp only [Prod.mk.injEq] at hshift <;> exact hshift.2
        subst hprojectionEq
        have hprojection := D.reserved_not_in_references _ _ _ horiginal
        cases suffix with
        | nil =>
            simp only [List.nil_append, List.cons.injEq] at hoverrideEq
            obtain ⟨rfl, rfl⟩ := hoverrideEq
            have hindex : index = assignedIndex + 1 := by
              unfold shift at hshift
              simp only [List.length_nil, Nat.zero_le, if_true, Prod.mk.injEq] at hshift
              exact hshift.1.symm
            subst hindex
            obtain ⟨hclause, currentImage, hcurrent, hpass, -⟩ :=
              ihThis image' D.enclosing himage' Image.reservedRoot
            have hthisImage := hpass (D.passes_reservedRoot.mpr (by omega))
            have hcurrentNe : current ≠ D.reservedRoot := by
              intro hcurrentRoot
              obtain ⟨part', hdrop⟩ := hclause (by omega) hcurrentRoot
              have := D.drop_eq_partPath hdrop
              simp at this
              omega
            exact ⟨D.append_ne_reservedRoot hprojection hcurrentNe, assignedProjection ++ currentImage,
              D.image_append hcurrent hprojection hcurrentNe,
              Fact.basesStep hoverridesImage (by simpa using horiginal) (by simpa using hthisImage)⟩
        | cons suffixLabel suffixRest =>
            simp only [List.cons_append, List.cons.injEq] at hoverrideEq
            obtain ⟨rfl, rfl⟩ := hoverrideEq
            have hrestFree : D.reserved ∉ suffixRest := fun hm => hsuffix (List.mem_cons_of_mem _ hm)
            obtain ⟨hclause, currentImage, hcurrent, hpass, hnoPass⟩ :=
              ihThis image' (suffixRest ++ D.mixinPath) himage' (Image.part part hrestFree)
            have hthisImage : This D.original image' (suffixRest ++ D.mixinPath) assignedIndex
                currentImage := by
              unfold shift at hshift
              split_ifs at hshift with hle
              · simp only [Prod.mk.injEq] at hshift
                obtain ⟨rfl, -⟩ := hshift
                have := hpass (D.passes_part.mpr (by simp at hle ⊢; omega))
                simpa using this
              · simp only [Prod.mk.injEq] at hshift
                obtain ⟨rfl, -⟩ := hshift
                exact hnoPass (fun hpasses => hle (by
                  have := D.passes_part.mp hpasses
                  simp; omega))
            have hcurrentNe : current ≠ D.reservedRoot := by
              intro hcurrentRoot
              cases index with
              | zero =>
                  rw [(this_zero_iff D.decomposed).mp hthis] at hcurrentRoot
                  obtain ⟨part', heq⟩ := hpartRoot hcurrentRoot
                  have := congrArg List.length heq
                  simp at this
                  omega
              | succ index =>
                  obtain ⟨part', hdrop⟩ := hclause (by omega) hcurrentRoot
                  have hlength := D.drop_eq_partPath hdrop
                  simp at hlength
                  unfold shift at hshift
                  split_ifs at hshift with hle <;> simp only [Prod.mk.injEq] at hshift <;>
                    simp at hle <;> omega
            exact ⟨D.append_ne_reservedRoot hprojection hcurrentNe, assignedProjection ++ currentImage,
              D.image_append hcurrent hprojection hcurrentNe,
              Fact.basesStep hoverridesImage horiginal hthisImage⟩
      · exact absurd hroot hoverrideNe
  | basesStarRefl path =>
      intro image himage hne
      exact ⟨hne, image, himage, Fact.basesStarRefl _⟩
  | basesStarTail hchain hstep ihChain ihStep =>
      intro image himage hne
      obtain ⟨hmiddleNe, middleImage, hmiddle, hchainImage⟩ := ihChain image himage hne
      obtain ⟨htargetNe, targetImage, htarget, hstepImage⟩ := ihStep middleImage hmiddle hmiddleNe
      exact ⟨htargetNe, targetImage, htarget, Fact.basesStarTail hchainImage hstepImage⟩
  | thisZero source definitionSite =>
      intro sourceImage definitionSiteImage hsource _
      refine ⟨fun h => absurd h (Nat.lt_irrefl 0), sourceImage, hsource,
        fun h => absurd h (D.not_passes_zero _), fun _ => Fact.thisZero _ _⟩
  | @thisSucc source site target definitionLabel definitionRest steps hsupers hrest
      ihSupers ihRest =>
      intro sourceImage definitionSiteImage hsource hdefinitionSite
      by_cases hroot : definitionLabel :: definitionRest = D.reservedRoot
      · -- The step from the reserved root, which has no counterpart in `D`.
        have hdefinitionSiteImage : definitionSiteImage = D.enclosing := by
          rw [hroot] at hdefinitionSite
          exact D.image_functional hdefinitionSite Image.reservedRoot
        have hsourceRoot : source = D.reservedRoot := by
          by_contra hsourceNe
          exact (ihSupers sourceImage hsource hsourceNe).1 hroot
        subst hsourceRoot
        have hsourceImage : sourceImage = D.enclosing :=
          D.image_functional hsource Image.reservedRoot
        obtain ⟨rfl, -⟩ := D.supers_reservedRoot hsupers
        simp only [List.cons.injEq] at hroot
        obtain ⟨rfl, rfl⟩ := hroot
        subst hdefinitionSiteImage hsourceImage
        obtain ⟨hclause, targetImage, htarget, -, hnoPass⟩ :=
          ihRest D.enclosing D.enclosing (Image.outside D.reserved_not_mem_enclosing)
            (Image.outside D.reserved_not_mem_enclosing)
        have hthisImage := hnoPass (D.not_passes_of_reserved_free D.reserved_not_mem_enclosing _)
        have htargetNe : target ≠ D.reservedRoot := by
          intro htargetRoot
          cases steps with
          | zero =>
              rw [(this_zero_iff D.decomposed).mp hrest] at htargetRoot
              exact D.reserved_not_mem_enclosing (htargetRoot ▸ D.reserved_mem_reservedRoot)
          | succ steps =>
              obtain ⟨part, hdrop⟩ := hclause (by omega) htargetRoot
              exact D.drop_partPath_reserved_free D.reserved_not_mem_enclosing _ hdrop
        refine ⟨fun _ h => absurd h htargetNe, targetImage, htarget, fun _ => by simpa using hthisImage,
          fun hnot => absurd (D.passes_succ.mpr (Or.inl rfl)) hnot⟩
      · have hsourceNe : source ≠ D.reservedRoot := by
          intro hsourceRoot
          subst hsourceRoot
          exact hroot (D.supers_reservedRoot hsupers).2
        obtain ⟨-, hsiteClause, siteImage, overrideImage, hsite, hoverride, hsupersImage⟩ :=
          ihSupers sourceImage hsource hsourceNe
        have hoverrideImage := D.image_functional hoverride hdefinitionSite
        subst hoverrideImage
        obtain ⟨imageLabel, restImage, rfl, hrestImage⟩ := D.image_cons_shape hoverride hroot
        obtain ⟨hclause, targetImage, htarget, hpass, hnoPass⟩ :=
          ihRest siteImage restImage hsite hrestImage
        refine ⟨?_, targetImage, htarget, ?_, ?_⟩
        · intro _ htargetRoot
          cases steps with
          | zero =>
              rw [(this_zero_iff D.decomposed).mp hrest] at htargetRoot
              obtain ⟨part, hpart⟩ := hsiteClause htargetRoot
              exact ⟨part, by simpa using hpart⟩
          | succ steps =>
              obtain ⟨part, hdrop⟩ := hclause (by omega) htargetRoot
              exact ⟨part, by simpa using hdrop⟩
        · intro hpasses
          have hrestPasses := (D.passes_succ.mp hpasses).resolve_left hroot
          obtain ⟨index, hindex, -⟩ := id hrestPasses
          obtain ⟨steps', rfl⟩ : ∃ steps', steps = steps' + 1 := ⟨steps - 1, by omega⟩
          simpa using Fact.thisSucc hsupersImage (by simpa using hpass hrestPasses)
        · intro hnotPasses
          exact Fact.thisSucc hsupersImage
            (hnoPass (fun h => hnotPasses (D.passes_succ.mpr (Or.inr h))))

/-- The inclusion of thm:decomposition (b) from `D'` to `D`: at a path free of
`R`, every override component of `supers` in `D'` has its image among those
in `D`, with the image of its site. -/
theorem supers_decomposed_to_original {path site override : Path Label}
    (hfree : D.reserved ∉ path) (h : Supers D.decomposed path site override) :
    ∃ siteImage overrideImage, D.Image site siteImage ∧ D.Image override overrideImage ∧
      Supers D.original path siteImage overrideImage :=
  ((D.backward h) path (Image.outside hfree)
    (fun hroot => hfree (hroot ▸ D.reserved_mem_reservedRoot))).2.2

/-! ## From `D` to `D'`: clauses (F1) to (F4) -/

/-- Both alternatives of eq:overrides keep the innermost label. -/
theorem overrides_innermost_label
    {inheritsFunction : Path Label → Option (Set (Reference Label))}
    {label overrideLabel : Label} {path overrideRest : Path Label}
    (h : Overrides inheritsFunction (label :: path) (overrideLabel :: overrideRest)) :
    label = overrideLabel := by
  cases h <;> rfl

/-- The first step of a climb of at least one step. -/
theorem this_succ_supers {inheritsFunction : Path Label → Option (Set (Reference Label))}
    {source definitionSite target : Path Label} {steps : ℕ}
    (h : This inheritsFunction source definitionSite (steps + 1) target) :
    ∃ site, Supers inheritsFunction source site definitionSite := by
  cases definitionSite with
  | nil => exact absurd h (this_succ_nil_iff inheritsFunction)
  | cons _ _ =>
      obtain ⟨site, hsupers, -⟩ := (this_succ_iff inheritsFunction).mp h
      exact ⟨site, hsupers⟩

/-- A path of the subtree of `p`, `p` included. -/
def InSubtree (path : Path Label) : Prop := ∃ suffix, path = suffix ++ D.mixinPath

theorem not_inSubtree_enclosing : ¬ D.InSubtree D.enclosing := by
  rintro ⟨suffix, h⟩
  have := congrArg List.length h
  simp at this
  omega

theorem not_inSubtree_of_cons {label : Label} {path : Path Label}
    (h : ¬ D.InSubtree (label :: path)) : ¬ D.InSubtree path := by
  rintro ⟨suffix, rfl⟩
  exact h ⟨label :: suffix, rfl⟩

theorem mixinPath_ne_append {suffix : Path Label} (hsuffix : suffix ≠ []) :
    D.mixinPath ≠ suffix ++ D.mixinPath := by
  intro h
  have hlength := congrArg List.length h
  rw [List.length_append] at hlength
  exact hsuffix (List.length_eq_zero_iff.mp (by omega))

theorem dom_decomposed_of_original {path : Path Label} (h : path ∈ Dom D.original) :
    path ∈ Dom D.decomposed :=
  (D.dom_decomposed_iff_of_reserved_free (D.reserved_unwritten _ h)).mpr h

theorem dom_decomposed_part {part : Part} {suffix : Path Label}
    (h : suffix ∈ D.scope part) : suffix ++ D.partPath part ∈ Dom D.decomposed := by
  simp [Dom, D.decomposed_part part suffix h]

theorem overrides_partPath_self (part : Part) :
    Overrides D.decomposed (D.partPath part) (D.partPath part) :=
  Fact.overridesSelf D.supers_reservedRoot_self (by
    simpa using D.dom_decomposed_part (D.scope_nil part))

theorem supers_written_self_decomposed {path : Path Label}
    (hwritten : path ∈ Dom D.decomposed) (hne : path ≠ []) :
    Supers D.decomposed path path.tail path := by
  obtain ⟨label, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  exact Fact.supersStep (Fact.basesStarRefl _)
    (overrides_written_self_of_prefix_closed D.decomposed D.prefix_closed_decomposed hwritten)

theorem memRef_decomposed_of_original {reference : Reference Label} {path : Path Label}
    (h : MemRef D.original reference path) (hcarrier : path ≠ D.carrier) :
    MemRef D.decomposed reference path := by
  rw [MemRef, D.decomposed_outside path (D.reserved_unwritten _ h.mem_dom) hcarrier]
  exact h

theorem memRef_decomposed_shift {part : Part} {suffix : Path Label}
    {reference : Reference Label} (h : reference ∈ D.assigned part suffix) :
    MemRef D.decomposed (shift suffix reference) (suffix ++ D.partPath part) :=
  ⟨_, D.decomposed_part part suffix (D.assigned_scope part suffix reference h), ⟨reference, h, rfl⟩⟩

theorem carrier_ne_inSubtree {path : Path Label} (h : D.InSubtree path) : path ≠ D.carrier := by
  obtain ⟨suffix, rfl⟩ := h
  exact fun heq => D.carrier_outside suffix heq.symm

/-- The paper's clauses (F1) to (F4). (F1) and (F2) also export how the scope
that encloses an override component of the subtree is hosted in `D'`, by `M`
or by every part that writes it, which (F4) uses where a climb stops inside
`M`; a reflexive override instead puts the site on that scope. -/
def forwardMotive : Atom Label → Prop
  | .supers path site override =>
      (Supers D.decomposed path site override ∨
        (override = D.mixinPath ∧ site = D.enclosing ∧
          ∀ part, Supers D.decomposed path D.reservedRoot (D.partPath part)) ∨
        (∃ suffix, suffix ≠ [] ∧ override = suffix ++ D.mixinPath ∧
          override ∈ Dom D.original ∧
          ∀ part, suffix ∈ D.scope part →
            Supers D.decomposed path site (suffix ++ D.partPath part))) ∧
      (∀ label suffix, override = label :: (suffix ++ D.mixinPath) →
        (site = suffix ++ D.mixinPath ∨
          (∃ site', Supers D.decomposed site site' (suffix ++ D.mixinPath)) ∨
          (∀ part, suffix ∈ D.scope part →
            ∃ site', Supers D.decomposed site site' (suffix ++ D.partPath part))) ∧
        (override ∈ Dom D.original →
          (∃ site', Supers D.decomposed site site' (suffix ++ D.mixinPath)) →
          Supers D.decomposed path site override) ∧
        (∀ part, label :: suffix ∈ D.scope part →
          (∃ site', Supers D.decomposed site site' (suffix ++ D.partPath part)) →
          Supers D.decomposed path site (label :: (suffix ++ D.partPath part))))
  | .overrides path override =>
      (Overrides D.decomposed path override ∨
        (∃ suffix, suffix ≠ [] ∧ override = suffix ++ D.mixinPath ∧
          override ∈ Dom D.original ∧
          ∀ part, suffix ∈ D.scope part →
            Overrides D.decomposed path (suffix ++ D.partPath part))) ∧
      (∀ label suffix, override = label :: (suffix ++ D.mixinPath) →
        path = override ∨
          (∃ site', Supers D.decomposed path.tail site' (suffix ++ D.mixinPath)) ∨
          (∀ part, suffix ∈ D.scope part →
            ∃ site', Supers D.decomposed path.tail site' (suffix ++ D.partPath part)))
  | .bases path target =>
      (Bases D.decomposed path target ∨
        (target = D.mixinPath ∧ ∀ part, Bases D.decomposed path (D.partPath part))) ∧
      (path = D.mixinPath → ∃ part, Bases D.decomposed (D.partPath part) target)
  | .basesStar path target =>
      BasesStar D.decomposed path target ∨
        (target = D.mixinPath ∧ ∀ part, BasesStar D.decomposed path (D.partPath part))
  | .this source definitionSite steps target =>
      (¬ D.InSubtree definitionSite → This D.decomposed source definitionSite steps target) ∧
      (∀ suffix, definitionSite = suffix ++ D.mixinPath → definitionSite ∈ Dom D.original →
        This D.decomposed source definitionSite steps target ∨
          ∀ part, suffix ∈ D.scope part →
            This D.decomposed source (suffix ++ D.partPath part)
              (if suffix.length < steps then steps + 1 else steps) target)

theorem forward {atom : Atom Label} (h : Fact D.original atom) : D.forwardMotive atom := by
  induction h with
  | supersRoot =>
      exact ⟨Or.inl Fact.supersRoot, fun label suffix h => absurd h (by simp)⟩
  | @supersStep pathLabel path baseLabel site override hchain hoverride ihChain ihOverride =>
      obtain ⟨ihOverrideMain, ihOverrideHost⟩ := ihOverride
      refine ⟨?_, ?_⟩
      · rcases ihChain with hchainDecomposed | ⟨hbase, hchainParts⟩
        · rcases ihOverrideMain with hoverrideDecomposed | ⟨suffix, hsuffix, rfl, hwritten, hparts⟩
          · exact Or.inl (Fact.supersStep hchainDecomposed hoverrideDecomposed)
          · exact Or.inr (Or.inr ⟨suffix, hsuffix, rfl, hwritten,
              fun part hscope => Fact.supersStep hchainDecomposed (hparts part hscope)⟩)
        · have hoverrideMixin := D.mixin_sole_definition _ (hbase ▸ hoverride)
          simp only [List.cons.injEq] at hbase
          obtain ⟨rfl, rfl⟩ := hbase
          exact Or.inr (Or.inl ⟨hoverrideMixin, rfl,
            fun part => Fact.supersStep (hchainParts part) (D.overrides_partPath_self part)⟩)
      · intro label suffix hoverrideEq
        have hbaseNe : baseLabel :: site ≠ D.mixinPath := by
          intro hbase
          have := D.mixin_sole_definition _ (hbase ▸ hoverride)
          rw [hoverrideEq] at this
          have := congrArg List.length this
          simp at this
          omega
        have hchainDecomposed : BasesStar D.decomposed (pathLabel :: path) (baseLabel :: site) :=
          ihChain.resolve_right (fun h => hbaseNe h.1)
        have hlabel : baseLabel = label := by
          rw [hoverrideEq] at hoverride
          exact overrides_innermost_label hoverride
        subst hlabel
        refine ⟨?_, ?_, ?_⟩
        · rcases ihOverrideHost baseLabel suffix hoverrideEq with hself | hhost
          · rw [hoverrideEq] at hself
            simp only [List.cons.injEq] at hself
            exact Or.inl hself.2
          · exact Or.inr hhost
        · intro hwritten hhost
          obtain ⟨site', hsupers⟩ := hhost
          rw [hoverrideEq] at hwritten ⊢
          exact Fact.supersStep hchainDecomposed
            (Fact.overridesBranch hsupers (D.dom_decomposed_of_original hwritten))
        · intro part hscope hhost
          obtain ⟨site', hsupers⟩ := hhost
          exact Fact.supersStep hchainDecomposed
            (Fact.overridesBranch hsupers (by
              simpa using D.dom_decomposed_part hscope))
  | overridesRoot =>
      exact ⟨Or.inl Fact.overridesRoot, fun label suffix h => absurd h (by simp)⟩
  | @overridesSelf path site branch label hsupers hdom ih =>
      obtain ⟨ihMain, -⟩ := ih
      refine ⟨Or.inl ?_, fun _ _ _ => Or.inl rfl⟩
      rcases ihMain with hsupersDecomposed | ⟨rfl, -, hparts⟩ | ⟨suffix, -, rfl, -, hparts⟩
      · exact Fact.overridesSelf hsupersDecomposed (D.dom_decomposed_of_original hdom)
      · obtain ⟨part, hscope⟩ := D.scope_cover [label] (by simpa using hdom)
        exact Fact.overridesSelf (hparts part) (by simpa using D.dom_decomposed_part hscope)
      · obtain ⟨part, hscope⟩ := D.scope_cover (label :: suffix) (by simpa using hdom)
        exact Fact.overridesSelf (hparts part (D.scope_prefix part label suffix hscope))
          (by simpa using D.dom_decomposed_part hscope)
  | @overridesBranch path site branch label hsupers hdom ih =>
      obtain ⟨ihMain, -⟩ := ih
      refine ⟨?_, ?_⟩
      · rcases ihMain with hsupersDecomposed | ⟨rfl, -, hparts⟩ | ⟨suffix, -, rfl, -, hparts⟩
        · exact Or.inl (Fact.overridesBranch hsupersDecomposed (D.dom_decomposed_of_original hdom))
        · exact Or.inr ⟨[label], by simp, by simp, hdom, fun part hscope =>
            Fact.overridesBranch (hparts part) (by simpa using D.dom_decomposed_part hscope)⟩
        · exact Or.inr ⟨label :: suffix, by simp, by simp, hdom, fun part hscope =>
            Fact.overridesBranch (hparts part (D.scope_prefix part label suffix hscope))
              (by simpa using D.dom_decomposed_part hscope)⟩
      · intro label' suffix hoverrideEq
        simp only [List.cons.injEq] at hoverrideEq
        obtain ⟨rfl, rfl⟩ := hoverrideEq
        rcases ihMain with hsupersDecomposed | ⟨hbranch, -, hparts⟩ |
            ⟨suffix', -, hbranch, -, hparts⟩
        · exact Or.inr (Or.inl ⟨site, hsupersDecomposed⟩)
        · have hsuffix : suffix = [] := by
            by_contra hne
            exact D.mixinPath_ne_append hne hbranch.symm
          subst hsuffix
          exact Or.inr (Or.inr fun part _ => ⟨D.reservedRoot, by simpa using hparts part⟩)
        · obtain rfl := List.append_cancel_right hbranch
          exact Or.inr (Or.inr fun part hscope => ⟨site, hparts part hscope⟩)
  | @basesStep path current label overrideLabel overrideRest index projection
      hoverride hreference hthis ihOverride ihThis =>
      obtain ⟨ihOverrideMain, -⟩ := ihOverride
      obtain ⟨ihOutside, ihInside⟩ := ihThis
      have hoverrideWritten := hreference.mem_dom
      by_cases hsubtree : D.InSubtree (overrideLabel :: overrideRest)
      · obtain ⟨suffix, hsuffixEq⟩ := hsubtree
        cases suffix with
        | nil =>
            simp only [List.nil_append, List.cons.injEq] at hsuffixEq
            obtain ⟨rfl, rfl⟩ := hsuffixEq
            have hoverrideDecomposed : Overrides D.decomposed (label :: path) D.mixinPath :=
              ihOverrideMain.resolve_right (fun ⟨suffix, hne, heq, _⟩ => D.mixinPath_ne_append hne heq)
            have hthisDecomposed := ihOutside D.not_inSubtree_enclosing
            have hreferenceDecomposed := D.memRef_decomposed_of_original hreference
              (D.carrier_ne_inSubtree ⟨[], rfl⟩)
            refine ⟨Or.inl (Fact.basesStep hoverrideDecomposed hreferenceDecomposed hthisDecomposed), ?_⟩
            intro hpath
            simp only [List.cons.injEq] at hpath
            obtain ⟨rfl, rfl⟩ := hpath
            obtain ⟨part, hassigned⟩ := D.assigned_cover [] (index, projection) (by simpa using hreference)
            have hshifted := D.memRef_decomposed_shift hassigned
            simp only [shift, List.length_nil, Nat.zero_le, if_true, List.nil_append] at hshifted
            exact ⟨part, Fact.basesStep (D.overrides_partPath_self part) hshifted
              (Fact.thisSucc D.supers_reservedRoot_self hthisDecomposed)⟩
        | cons suffixLabel suffixRest =>
            simp only [List.cons_append, List.cons.injEq] at hsuffixEq
            obtain ⟨hlabelEq, rfl⟩ := hsuffixEq
            subst overrideLabel
            obtain ⟨part, hassigned⟩ := D.assigned_cover (suffixLabel :: suffixRest) (index, projection)
              (by simpa using hreference)
            have hscope := D.assigned_scope part _ _ hassigned
            have hshifted := D.memRef_decomposed_shift hassigned
            have hlabel : label = suffixLabel := overrides_innermost_label hoverride
            subst hlabel
            refine ⟨Or.inl ?_, ?_⟩
            · cases index with
              | zero =>
                  rw [(this_zero_iff D.original).mp hthis]
                  rcases ihOverrideMain with hoverrideDecomposed | ⟨suffix, -, heq, -, hparts⟩
                  · exact Fact.basesStep hoverrideDecomposed
                      (D.memRef_decomposed_of_original hreference
                        (D.carrier_ne_inSubtree ⟨label :: suffixRest, rfl⟩))
                      (Fact.thisZero _ _)
                  · have hsuffix : suffix = label :: suffixRest :=
                      (List.append_cancel_right (by simpa using heq)).symm
                    subst hsuffix
                    have hoverrideParts := hparts part hscope
                    simp only [shift, List.length_cons] at hshifted
                    rw [if_neg (by omega)] at hshifted
                    exact Fact.basesStep (by simpa using hoverrideParts) (by simpa using hshifted)
                      (Fact.thisZero _ _)
              | succ index =>
                  rcases ihInside suffixRest rfl (D.prefix_closed _ _ hoverrideWritten) with
                    horiginal | hparts
                  · obtain ⟨site, hsupers⟩ := this_succ_supers horiginal
                    exact Fact.basesStep
                      (Fact.overridesBranch hsupers (D.dom_decomposed_of_original hoverrideWritten))
                      (D.memRef_decomposed_of_original hreference
                        (D.carrier_ne_inSubtree ⟨label :: suffixRest, rfl⟩))
                      horiginal
                  · have hthisParts := hparts part (D.scope_prefix part label suffixRest hscope)
                    have hsteps : (if suffixRest.length < index + 1 then index + 1 + 1 else index + 1) =
                        (if suffixRest.length < index + 1 then index + 1 else index) + 1 := by
                      split_ifs <;> rfl
                    rw [hsteps] at hthisParts
                    obtain ⟨site, hsupers⟩ := this_succ_supers hthisParts
                    have hindex : shift (label :: suffixRest) (index + 1, projection) =
                        ((if suffixRest.length < index + 1 then index + 1 else index) + 1,
                          projection) := by
                      simp only [shift, List.length_cons]
                      split_ifs <;> first | rfl | omega
                    rw [hindex] at hshifted
                    exact Fact.basesStep
                      (Fact.overridesBranch hsupers (by simpa using D.dom_decomposed_part hscope))
                      (by simpa using hshifted) hthisParts
            · intro hpath
              rw [hpath] at hoverride
              have := D.mixin_sole_definition _ hoverride
              have := congrArg List.length this
              simp at this
              omega
      · have hoverrideDecomposed : Overrides D.decomposed (label :: path) (overrideLabel :: overrideRest) :=
          ihOverrideMain.resolve_right (fun ⟨suffix, _, heq, _⟩ => hsubtree ⟨suffix, heq⟩)
        have hthisDecomposed := ihOutside (D.not_inSubtree_of_cons hsubtree)
        refine ⟨?_, ?_⟩
        · by_cases hcarrierReference : overrideLabel :: overrideRest = D.carrier ∧
              (index, projection) = (D.carrier.tail.length, D.mixinPath)
          · obtain ⟨hcarrier, hreferenceEq⟩ := hcarrierReference
            have hcarrierTail : D.carrier.tail = overrideRest := by rw [← hcarrier]; rfl
            simp only [Prod.mk.injEq] at hreferenceEq
            obtain ⟨rfl, rfl⟩ := hreferenceEq
            rw [hcarrierTail] at hthisDecomposed
            have hcurrentNil := this_full_length_root D.decomposed hoverrideDecomposed hthisDecomposed
            subst hcurrentNil
            refine Or.inr ⟨by simp, fun part => ?_⟩
            have hreferencePart : MemRef D.decomposed (overrideRest.length, D.partPath part)
                (overrideLabel :: overrideRest) := by
              obtain ⟨references, hreferences, -⟩ := D.carrier_reference
              rw [hcarrier]
              exact ⟨_, D.decomposed_carrier references hreferences,
                Or.inr ⟨part, by rw [← hcarrierTail]⟩⟩
            simpa using Fact.basesStep hoverrideDecomposed hreferencePart hthisDecomposed
          · have hreferenceDecomposed : MemRef D.decomposed (index, projection)
                (overrideLabel :: overrideRest) := by
              by_cases hcarrier : overrideLabel :: overrideRest = D.carrier
              · rw [hcarrier] at hreference ⊢
                exact D.memRef_original_carrier hreference
                  (fun heq => hcarrierReference ⟨hcarrier, heq⟩)
              · exact D.memRef_decomposed_of_original hreference hcarrier
            exact Or.inl (Fact.basesStep hoverrideDecomposed hreferenceDecomposed hthisDecomposed)
        · intro hpath
          rw [hpath] at hoverride
          exact (hsubtree ⟨[], D.mixin_sole_definition _ hoverride⟩).elim
  | basesStarRefl path => exact Or.inl (Fact.basesStarRefl _)
  | basesStarTail hchain hstep ihChain ihStep =>
      obtain ⟨ihStepMain, ihStepFromMixin⟩ := ihStep
      rcases ihChain with hchainDecomposed | ⟨rfl, hchainParts⟩
      · rcases ihStepMain with hstepDecomposed | ⟨rfl, hstepParts⟩
        · exact Or.inl (Fact.basesStarTail hchainDecomposed hstepDecomposed)
        · exact Or.inr ⟨rfl, fun part => Fact.basesStarTail hchainDecomposed (hstepParts part)⟩
      · obtain ⟨part, hstepPart⟩ := ihStepFromMixin rfl
        exact Or.inl (Fact.basesStarTail (hchainParts part) hstepPart)
  | thisZero source definitionSite =>
      exact ⟨fun _ => Fact.thisZero _ _, fun _ _ _ => Or.inl (Fact.thisZero _ _)⟩
  | @thisSucc source site target definitionLabel definitionRest steps hsupers hrest
      ihSupers ihRest =>
      obtain ⟨ihSupersMain, ihSupersHost⟩ := ihSupers
      obtain ⟨ihOutside, ihInside⟩ := ihRest
      refine ⟨?_, ?_⟩
      · intro hnot
        have hsupersDecomposed : Supers D.decomposed source site (definitionLabel :: definitionRest) := by
          rcases ihSupersMain with h | ⟨heq, -, -⟩ | ⟨suffix, -, heq, -, -⟩
          · exact h
          · exact absurd ⟨[], heq⟩ hnot
          · exact absurd ⟨suffix, heq⟩ hnot
        exact Fact.thisSucc hsupersDecomposed (ihOutside (D.not_inSubtree_of_cons hnot))
      · intro suffix hdefinitionSite hwritten
        cases suffix with
        | nil =>
            simp only [List.nil_append, List.cons.injEq] at hdefinitionSite
            obtain ⟨rfl, rfl⟩ := hdefinitionSite
            have hrestDecomposed := ihOutside D.not_inSubtree_enclosing
            rcases ihSupersMain with h | ⟨-, hsite, hparts⟩ | ⟨suffix, hne, heq, -, -⟩
            · exact Or.inl (Fact.thisSucc h hrestDecomposed)
            · subst hsite
              refine Or.inr fun part _ => ?_
              simpa using Fact.thisSucc (hparts part)
                (Fact.thisSucc D.supers_reservedRoot_self hrestDecomposed)
            · exact absurd heq (D.mixinPath_ne_append hne)
        | cons suffixLabel suffixRest =>
            simp only [List.cons_append, List.cons.injEq] at hdefinitionSite
            obtain ⟨rfl, rfl⟩ := hdefinitionSite
            have hrestWritten := D.prefix_closed _ _ hwritten
            obtain ⟨hhost, horiginalStep, hpartStep⟩ :=
              ihSupersHost definitionLabel suffixRest rfl
            have hsteps : (if (definitionLabel :: suffixRest).length < steps + 1 then steps + 1 + 1
                else steps + 1) = (if suffixRest.length < steps then steps + 1 else steps) + 1 := by
              simp only [List.length_cons]
              split_ifs <;> first | rfl | omega
            rw [hsteps]
            cases steps with
            | zero =>
                obtain rfl := (this_zero_iff D.original).mp hrest
                rcases hhost with hself | horiginal | hparts
                · subst hself
                  exact Or.inl (Fact.thisSucc
                    (horiginalStep hwritten ⟨_, D.supers_written_self_decomposed
                      (D.dom_decomposed_of_original hrestWritten) (by simp)⟩)
                    (Fact.thisZero _ _))
                · exact Or.inl (Fact.thisSucc (horiginalStep hwritten horiginal) (Fact.thisZero _ _))
                · refine Or.inr fun part hscope => ?_
                  have hstep := hpartStep part hscope
                    (hparts part (D.scope_prefix part definitionLabel suffixRest hscope))
                  simpa using Fact.thisSucc hstep (Fact.thisZero _ _)
            | succ steps =>
                rcases ihInside suffixRest rfl hrestWritten with horiginal | hparts
                · obtain ⟨site', hsupers'⟩ := this_succ_supers horiginal
                  exact Or.inl (Fact.thisSucc (horiginalStep hwritten ⟨site', hsupers'⟩) horiginal)
                · refine Or.inr fun part hscope => ?_
                  have hthisPart := hparts part (D.scope_prefix part definitionLabel suffixRest hscope)
                  have hpositive : (if suffixRest.length < steps + 1 then steps + 1 + 1
                      else steps + 1) = (if suffixRest.length < steps + 1 then steps + 1 else steps) + 1 := by
                    split_ifs <;> rfl
                  rw [hpositive] at hthisPart
                  obtain ⟨site', hsupers'⟩ := this_succ_supers hthisPart
                  have hstep := hpartStep part hscope ⟨site', hsupers'⟩
                  rw [hpositive]
                  exact Fact.thisSucc hstep hthisPart

/-! ## The theorem -/

/-- The image of a written path of `D'` is written in `D`. -/
theorem image_dom {path image : Path Label} (h : D.Image path image)
    (hwritten : path ∈ Dom D.decomposed) : image ∈ Dom D.original := by
  rcases D.image_iff.mp h with ⟨hfree, rfl⟩ | ⟨part, suffix, hsuffix, rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (D.dom_decomposed_iff_of_reserved_free hfree).mp hwritten
  · rcases D.written_reserved hwritten (D.reserved_mem_partPath_append part suffix) with
      hroot | ⟨part', suffix', hscope, heq⟩
    · exact absurd hroot (D.partPath_append_ne_reservedRoot part suffix)
    · obtain ⟨rfl, rfl⟩ := D.partPath_append_inj hsuffix (D.reserved_not_mem_of_scope hscope) heq
      exact D.scope_written part suffix hscope
  · exact D.prefix_closed _ _ D.mixin_written

/-- The inclusion of thm:decomposition (b) from `D` to `D'`: at a path free of
`R`, every override component of `supers` in `D` is one in `D'` or the image
of one, `q_i ⌢ v` for every part `i` that writes `v`. -/
theorem supers_original_to_decomposed {path site override : Path Label}
    (h : Supers D.original path site override) :
    Supers D.decomposed path site override ∨
      (override = D.mixinPath ∧ ∀ part, Supers D.decomposed path D.reservedRoot (D.partPath part)) ∨
      (∃ suffix, override = suffix ++ D.mixinPath ∧ override ∈ Dom D.original ∧
        ∀ part, suffix ∈ D.scope part →
          Supers D.decomposed path site (suffix ++ D.partPath part)) := by
  rcases (D.forward h).1 with h | ⟨heq, -, hparts⟩ | ⟨suffix, -, heq, hwritten, hparts⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨heq, hparts⟩)
  · exact Or.inr (Or.inr ⟨suffix, heq, hwritten, hparts⟩)

/-- **thm:decomposition** (b): at a path `a` free of `R`, the written override
components of `supers_D(a)` are exactly the images of the written override
components of `supers_{D'}(a)`. -/
theorem decomposition {path override : Path Label} (hfree : D.reserved ∉ path) :
    (∃ site, Supers D.original path site override ∧ override ∈ Dom D.original) ↔
      ∃ site decomposedOverride, Supers D.decomposed path site decomposedOverride ∧
        decomposedOverride ∈ Dom D.decomposed ∧ D.Image decomposedOverride override := by
  constructor
  · rintro ⟨site, hsupers, hwritten⟩
    rcases D.supers_original_to_decomposed hsupers with
      h | ⟨rfl, hparts⟩ | ⟨suffix, rfl, -, hparts⟩
    · exact ⟨site, override, h, D.dom_decomposed_of_original hwritten,
        Image.outside (D.reserved_unwritten _ hwritten)⟩
    · obtain ⟨part, hscope⟩ := D.scope_cover [] (by simpa using hwritten)
      exact ⟨D.reservedRoot, D.partPath part, hparts part,
        by simpa using D.dom_decomposed_part hscope, D.image_partPath part⟩
    · obtain ⟨part, hscope⟩ := D.scope_cover suffix hwritten
      exact ⟨site, suffix ++ D.partPath part, hparts part hscope, D.dom_decomposed_part hscope,
        Image.part part (D.reserved_not_mem_of_scope hscope)⟩
  · rintro ⟨site, decomposedOverride, hsupers, hwritten, himage⟩
    obtain ⟨siteImage, overrideImage, -, hoverrideImage, hsupersImage⟩ :=
      D.supers_decomposed_to_original hfree hsupers
    obtain rfl := D.image_functional hoverrideImage himage
    exact ⟨siteImage, hsupersImage, D.image_dom himage hwritten⟩

/-- **thm:decomposition** (b), existence: a path free of `R` exists in `D`
exactly when it exists in `D'`. -/
theorem decomposition_exists {path : Path Label} (hfree : D.reserved ∉ path) :
    (supersSet D.original path).Nonempty ↔ (supersSet D.decomposed path).Nonempty := by
  constructor
  · rintro ⟨⟨site, override⟩, hsupers⟩
    rcases D.supers_original_to_decomposed (hsupers : Supers D.original path site override) with
      h | ⟨-, hparts⟩ | ⟨suffix, hoverrideEq, hwritten, hparts⟩
    · exact ⟨(site, override), h⟩
    · obtain ⟨part, -⟩ := D.scope_cover [] (by simpa using D.mixin_written)
      exact ⟨(D.reservedRoot, D.partPath part), hparts part⟩
    · rw [hoverrideEq] at hwritten
      obtain ⟨part, hscope⟩ := D.scope_cover suffix hwritten
      exact ⟨(site, suffix ++ D.partPath part), hparts part hscope⟩
  · rintro ⟨⟨site, override⟩, hsupers⟩
    obtain ⟨siteImage, overrideImage, -, -, hsupersImage⟩ :=
      D.supers_decomposed_to_original hfree (hsupers : Supers D.decomposed path site override)
    exact ⟨(siteImage, overrideImage), hsupersImage⟩

end Decomposition

end InheritanceCalculus
