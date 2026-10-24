import InheritanceCalculus.PathExistence

/-!
# Monotonicity in the program

`TPfun_mono` (`Lattice.lean`) is monotonicity of the immediate consequence
operator in the *interpretation*, for one fixed primitive `inherits`. This
module proves monotonicity in the *program*: enlarging the primitive itself
(more written paths, more references at a written path) only adds facts. The
paper's statement is Lemma "Monotonicity in the program"
(lem:program-monotonicity, Appendix "Algebraic Properties of Deep Merge").

The proof is one induction over `Fact` derivations: every clause of the five
equations reads the primitive only positively, through `Dom` (in the guards
of eq:overrides) and `MemRef` (in eq:bases), so a derivation over the smaller
primitive is, clause by clause, a derivation over the larger one.

The corollary `fact_upward_closed` is the paper's Proposition "Upward-closed
observation" (prop:upward-closed-observation): no derivable fact, hence no
observation, can disappear when the primitive is extended, so no read point
can depend on the absence of another fact.
-/

set_option warningAsError true

namespace InheritanceCalculus

variable {Label : Type*}

/-- `Extends original extended`: the primitive `extended` contains `original`
pointwise, the paper's inclusion of partial functions
`inherits ⊆ inherits'` (lem:program-monotonicity): every path written in
`original` is written in `extended`, with at least the same references. -/
def Extends (original extended : Path Label → Option (Set (Reference Label))) : Prop :=
  ∀ path references, original path = some references →
    ∃ extendedReferences, extended path = some extendedReferences ∧
      references ⊆ extendedReferences

namespace Extends

variable {original extended : Path Label → Option (Set (Reference Label))}

theorem refl (inheritsFunction : Path Label → Option (Set (Reference Label))) :
    Extends inheritsFunction inheritsFunction :=
  fun _ references h => ⟨references, h, subset_rfl⟩

theorem trans {middle : Path Label → Option (Set (Reference Label))}
    (first : Extends original middle) (second : Extends middle extended) :
    Extends original extended := by
  intro path references h
  obtain ⟨middleReferences, hmiddle, hsubset⟩ := first path references h
  obtain ⟨extendedReferences, hextended, hsubset'⟩ := second path middleReferences hmiddle
  exact ⟨extendedReferences, hextended, hsubset.trans hsubset'⟩

theorem mem_dom (h : Extends original extended) {path : Path Label}
    (hpath : path ∈ Dom original) : path ∈ Dom extended := by
  simp only [Dom, Set.mem_setOf_eq, ne_eq, Option.ne_none_iff_exists'] at hpath ⊢
  obtain ⟨references, hreferences⟩ := hpath
  obtain ⟨extendedReferences, hextended, -⟩ := h path references hreferences
  exact ⟨extendedReferences, hextended⟩

theorem memRef (h : Extends original extended) {reference : Reference Label}
    {path : Path Label} (hreference : MemRef original reference path) :
    MemRef extended reference path := by
  obtain ⟨references, hreferences, hmember⟩ := hreference
  obtain ⟨extendedReferences, hextended, hsubset⟩ := h path references hreferences
  exact ⟨extendedReferences, hextended, hsubset hmember⟩

/-- lem:program-monotonicity: every fact derivable over `original` is
derivable over every extension of it. -/
theorem fact (h : Extends original extended) {atom : Atom Label}
    (hatom : Fact original atom) : Fact extended atom := by
  induction hatom with
  | supersRoot => exact Fact.supersRoot
  | supersStep _ _ ihChain ihOverrides => exact Fact.supersStep ihChain ihOverrides
  | overridesRoot => exact Fact.overridesRoot
  | overridesSelf _ hdom ihSupers => exact Fact.overridesSelf ihSupers (h.mem_dom hdom)
  | overridesBranch _ hdom ihSupers => exact Fact.overridesBranch ihSupers (h.mem_dom hdom)
  | basesStep _ hreference _ ihOverrides ihThis =>
      exact Fact.basesStep ihOverrides (h.memRef hreference) ihThis
  | basesStarRefl path => exact Fact.basesStarRefl path
  | basesStarTail _ _ ihChain ihStep => exact Fact.basesStarTail ihChain ihStep
  | thisZero source definitionSite => exact Fact.thisZero source definitionSite
  | thisSucc _ _ ihSupers ihRecursion => exact Fact.thisSucc ihSupers ihRecursion

/-- lem:program-monotonicity, set form at `supers`: the supers of every path
only grow under extension. -/
theorem supersSet_subset (h : Extends original extended) (path : Path Label) :
    supersSet original path ⊆ supersSet extended path :=
  fun _ hpair => h.fact hpair

/-- lem:program-monotonicity, existence form: a path that exists (in the
sense of Section "Semantic Functions", `supers(q) ≠ ∅`) keeps existing under
extension. -/
theorem supersSet_nonempty (h : Extends original extended) {path : Path Label}
    (hexists : (supersSet original path).Nonempty) :
    (supersSet extended path).Nonempty :=
  hexists.mono (h.supersSet_subset path)

end Extends

/-- prop:upward-closed-observation: for every fact (in particular, every
read point's existence), the class of primitives deriving it is upward closed
under extension. Equivalently, if a fact holds over a primitive and some other
fact fails there, the first fact still holds over every extension in which the
second one has come to hold: no fact can be derived from the absence of
another. -/
theorem fact_upward_closed (atom : Atom Label)
    {original extended : Path Label → Option (Set (Reference Label))}
    (hextends : Extends original extended) (hfact : Fact original atom) :
    Fact extended atom :=
  hextends.fact hfact

end InheritanceCalculus
