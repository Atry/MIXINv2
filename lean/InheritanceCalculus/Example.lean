import InheritanceCalculus.WellDefinedness
import InheritanceCalculus.Kleene
import InheritanceCalculus.PathExistence
import InheritanceCalculus.Interpreter
import InheritanceCalculus.MergeAssociativity
import InheritanceCalculus.MergeCommutativity
import InheritanceCalculus.MergeIdempotence
import InheritanceCalculus.AlgorithmSoundness
import InheritanceCalculus.Substitutability

/-!
# A concrete document, with explicit derivations

Sanity checks instantiating the abstract primitive with a four-node document
over `Label := String`:

```yaml
a:
- x: []
b:
- [a]
```

that is, `a` defines `x`, and `b` inherits `a` through the lexical reference
`[a]` (de-Bruijn-indexed `(0, ["a"])`). The derivations below check the
intended readings of the semantic equations: `b`'s reference resolves to `a`
(`supers_b_a`), the path `b, x` exists through inheritance even though it is
written nowhere (`overrides_bx_ax`, `supersSet_bx_nonempty`), and the unwritten
path `c` does not exist (`supersSet_c_empty`).

Paths follow the reversed representation of `Basic.lean` (innermost label
first), so the paper path `(b, x)` is written `["x", "b"]`.

The development is Prop-level by design (no decidability instances), so the
checks are explicit derivations rather than `decide` calls.
-/

set_option warningAsError true

namespace InheritanceCalculus
namespace Example

/-- The document: `a:` and `a: x:` are written with no references; `b` is
written inheriting the reference `(0, ["a"])`; nothing else is written. Paths
(and reference projection lists) are innermost-label-first. -/
def Inh₀ : Path String → Option (Set (Reference String))
  | [] => some ∅
  | ["a"] => some ∅
  | ["x", "a"] => some ∅
  | ["b"] => some {(0, ["a"])}
  | _ => none

theorem dom_a : (["a"] : Path String) ∈ Dom Inh₀ := by
  simp [Dom, Inh₀]

theorem dom_ax : (["x", "a"] : Path String) ∈ Dom Inh₀ := by
  simp [Dom, Inh₀]

theorem dom_b : (["b"] : Path String) ∈ Dom Inh₀ := by
  simp [Dom, Inh₀]

/-- `b` is written, so it is its own override. -/
theorem overrides_b : Overrides Inh₀ ["b"] ["b"] :=
  Fact.overridesSelf Fact.supersRoot dom_b

/-- `a` is written, so it is its own override. -/
theorem overrides_a : Overrides Inh₀ ["a"] ["a"] :=
  Fact.overridesSelf Fact.supersRoot dom_a

/-- The reference `(0, ["a"])` is written at `b`. -/
theorem memRef_b : MemRef Inh₀ (0, ["a"]) ["b"] :=
  ⟨{(0, ["a"])}, rfl, rfl⟩

/-- eq:bases at `b`: the reference climbs zero scopes from the root and
projects `a`, so `a` is a direct base of `b`. -/
theorem bases_b_a : Bases Inh₀ ["b"] ["a"] :=
  Fact.basesStep overrides_b memRef_b (Fact.thisZero [] [])

/-- eq:supers at `b`: through the one-hop `bases*` chain, `b` inherits `a`
with inheritance-site context the root. -/
theorem supers_b_a : Supers Inh₀ ["b"] [] ["a"] :=
  Fact.supersStep
    (Fact.basesStarTail (Fact.basesStarRefl ["b"]) bases_b_a)
    overrides_a

/-- eq:overrides at the inherited path `b, x`: written nowhere, it exists
because the super mixin `a` of `b` writes `x`. -/
theorem overrides_bx_ax : Overrides Inh₀ ["x", "b"] ["x", "a"] :=
  Fact.overridesBranch supers_b_a dom_ax

/-- lem:path-existence, positively: the path `b, x` exists. -/
theorem supersSet_bx_nonempty :
    (supersSet Inh₀ ["x", "b"]).Nonempty :=
  (supersSet_cons_nonempty_iff Inh₀ "x" ["b"]).mpr
    ⟨[], ["a"], supers_b_a, dom_ax⟩

/-- lem:path-existence, negatively: the unwritten path `c` does not exist. -/
theorem supersSet_c_empty : ¬ (supersSet Inh₀ ["c"]).Nonempty := by
  rw [supersSet_nonempty_iff_existent]
  rintro (habs | ⟨p, ℓ, c, pbr, heq, hsup, hdom⟩)
  · exact absurd habs (by simp)
  · obtain ⟨rfl, rfl⟩ : ℓ = "c" ∧ p = [] := by simpa using heq.symm
    obtain ⟨rfl, rfl⟩ := (supers_nil_iff Inh₀).mp hsup
    simp [Dom, Inh₀] at hdom

/-! ## The certifying interpreter on the same document

The evaluator (`Interpreter.lean`) is untrusted; the `#guard`s below run it at
elaboration time and feed its emitted certificate to the *verified* checker
(`Certificate.lean`), whose acceptance carries, through `checkCert_sound`,
machine-checked `Fact` derivations for every claimed atom. -/

/-- The same document, as the computable primitive of the certifying
interpreter (finite reference lists instead of sets). -/
def inh₀ : Path String → Option (List (Reference String))
  | [] => some []
  | ["a"] => some []
  | ["x", "a"] => some []
  | ["b"] => some [(0, ["a"])]
  | _ => none

/-- Sixteen tabling rounds from the query `supers (b, x)` (reversed
representation: `["x", "b"]`). -/
def demoRun : Interp String := Interp.run inh₀ 16 (.supers ["x", "b"])

-- The verified checker accepts the emitted certificate.
#guard checkCert inh₀ demoRun.certificate

-- The tabled evaluation rediscovers the hand-derived facts above: `b`
-- inherits `a`, and the unwritten path `(b, x)` exists through the
-- inherited override `(a, x)`.
#guard (Atom.supers ["b"] [] ["a"]) ∈ demoRun.facts
#guard (Atom.supers ["x", "b"] ["b"] ["x", "a"]) ∈ demoRun.facts

end Example

/-! ## Axiom guards

The strongest `sorry` check, mirroring `MixinV2Demo.lean`: `#print axioms`
lists `sorryAx` whenever a proof transitively uses `sorry`, and `#guard_msgs`
pins the axiom set of each headline theorem, so a stray `sorry` anywhere in
the dependency cone fails the build. -/

/-- info: 'InheritanceCalculus.lfp_TP_eq_toQAMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lfp_TP_eq_toQAMap

/-- info: 'InheritanceCalculus.lfp_TP_eq_iSup_stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lfp_TP_eq_iSup_stage

/-- info: 'InheritanceCalculus.exists_kleene_rank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_kleene_rank

/-- info: 'InheritanceCalculus.supersSet_nonempty_iff_existent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms supersSet_nonempty_iff_existent

/-- info: 'InheritanceCalculus.AssociativityDocument.merge_associative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AssociativityDocument.merge_associative

/--
info: 'InheritanceCalculus.AssociativityDocument.merge_associative_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AssociativityDocument.merge_associative_exists

/-- info: 'InheritanceCalculus.CommutativityDocument.merge_commutative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CommutativityDocument.merge_commutative

/--
info: 'InheritanceCalculus.CommutativityDocument.merge_commutative_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CommutativityDocument.merge_commutative_exists

/-- info: 'InheritanceCalculus.IdempotenceDocument.merge_idempotent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IdempotenceDocument.merge_idempotent

/--
info: 'InheritanceCalculus.IdempotenceDocument.merge_idempotent_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms IdempotenceDocument.merge_idempotent_exists

/-- info: 'InheritanceCalculus.restrict_lfp_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms restrict_lfp_eq

/-- info: 'InheritanceCalculus.tabled_le_lfp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tabled_le_lfp

/-- info: 'InheritanceCalculus.tabled_stable_eq_lfp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tabled_stable_eq_lfp

/-- info: 'InheritanceCalculus.Extends.fact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Extends.fact

/-- info: 'InheritanceCalculus.fact_upward_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fact_upward_closed

/-- info: 'InheritanceCalculus.inheritance_substitutable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inheritance_substitutable

/-- info: 'InheritanceCalculus.Redirection.simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Redirection.simulation

/-- info: 'InheritanceCalculus.Redirection.supers_written_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Redirection.supers_written_preserved

/-- info: 'InheritanceCalculus.Redirection.supers_written_transferred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Redirection.supers_written_transferred

/-- info: 'InheritanceCalculus.Redirection.exists_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Redirection.exists_preserved

/-- info: 'InheritanceCalculus.Redirection.exists_transferred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Redirection.exists_transferred

/-- info: 'InheritanceCalculus.checkCert_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms checkCert_sound

end InheritanceCalculus
