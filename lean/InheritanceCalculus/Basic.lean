import Mathlib

/-!
# Inheritance-calculus semantic layer: basic vocabulary

Formalizes the metalanguage vocabulary of the paper's semantic layer
(`MIXINv2/paper/inheritance-calculus.tex`, Section 2.2 "Syntactic Helpers" and
Section 3 "Semantics"), *from `inherits` upward*: the syntax layer (YAML AST and
the syntactic helpers of eq:helpers) is deliberately out of scope, and the
primitive query

  `inherits : Path ⇀ 𝒫(Reference)`   (eq:primitives, tex line ~1085)

is an abstract parameter of the whole development.

## Encoding conventions

- A *path* is a list of labels (`Path := List Label`), the paper's
  `Path = Label*` (tex line ~1106), stored **reversed**: innermost label
  first, so the paper's path `(b, x)` is `["x", "b"]`. The paper's snoc
  `p ⌢ ℓ` is `ℓ :: p`, the partial `init`/`last` are the tail/head, and
  every clause of the semantic equations decomposes a path at its innermost
  label, so the decomposition is a constructor pattern: partiality guards
  disappear into pattern matching, `cases` unifies indices directly, and the
  root `[]` is excluded from an `init` read by non-unification (the paper's
  omission convention, tex line ~3339).
- A *reference* `(n, w) ∈ ℕ × Label*` is de-Bruijn-indexed (tex line ~1123).
  The projection list `w` is stored reversed as well (deepest projection
  first), so the paper's downward concatenation `p ⌢⌢ w` is `w ++ p`.
- The partial primitive is encoded as `Inh : Path Label → Option (Set (Reference Label))`:
  `none` means "path not written" (outside `dom(inherits)`), while `some S`
  means "path written, inheriting the references in `S`" — faithfully keeping
  the paper's distinction between a missing key and a written mixin with an
  empty reference collection.
-/

set_option warningAsError true

namespace InheritanceCalculus

/-- A path: a finite sequence of labels identifying a position in the tree
(paper `Path = Label*`, tex line ~1106). The root path is `[]`. -/
abbrev Path (Label : Type*) := List Label

/-- A de-Bruijn-indexed reference `(n, w)`: climb `n` scopes outward, then
project the labels of `w` downward (paper `Reference = ℕ × Label*`, tex
line ~1123). -/
abbrev Reference (Label : Type*) := ℕ × List Label

variable {Label : Type*} (Inh : Path Label → Option (Set (Reference Label)))

/-- `dom(inherits)`: the set of written paths (paper eq:helpers, last line of
the domain equation; here abstract since the syntax layer is out of scope). -/
def Dom : Set (Path Label) := {p | Inh p ≠ none}

/-- Membership of a reference in the value of `inherits` at a written path:
`MemRef Inh r p` renders the paper's `(n, w) ∈ inherits(p)`, which per the
partial-function convention silently fails when `p ∉ dom(inherits)`. -/
def MemRef (r : Reference Label) (p : Path Label) : Prop :=
  ∃ S, Inh p = some S ∧ r ∈ S

theorem MemRef.mem_dom {Inh : Path Label → Option (Set (Reference Label))}
    {r : Reference Label} {p : Path Label} (h : MemRef Inh r p) : p ∈ Dom Inh := by
  obtain ⟨S, hS, -⟩ := h
  simp [Dom, hS]

end InheritanceCalculus
