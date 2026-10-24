# Machine-Checked Metatheory (Lean 4)

This directory is a Lean 4 mechanization of the semantic metatheory of
inheritance-calculus, developed against Mathlib. It is aimed at reviewers who
want to check what exactly is proved without reading every proof line: Lean
checks the proofs; a reviewer only needs to read the *definitions* and the
*theorem statements*, and to run the build once.

## Scope

The mechanization covers the semantic layer, taking the primitive
`inherits : Path ⇀ P(Reference)` as an abstract parameter (the YAML syntax
layer that produces `inherits` is out of scope by design):

- the five semantic equations (`supers`, `overrides`, `bases`, `resolve`,
  `this`) and their least-fixed-point reading;
- the full appendix "Well-Definedness of the Semantic Functions":
  monotonicity of the immediate consequence operator, the Knaster-Tarski
  least fixed point, well-definedness, Kleene iteration and Kleene rank,
  path existence, the dependency restriction lemma, and tabling soundness;
- from the appendix "Algebraic Properties of Deep Merge": associativity,
  commutativity, and idempotence, each comparing the paths of one document
  (associativity and commutativity share the simulation of
  `InheritanceCalculus/MergeSimulation.lean`), monotonicity in the program,
  upward-closed observation, the redirection simulation behind the
  substitutability theorem (its part (ii)) and the behavior-compatibility
  corollary, and the decomposition theorem at the level of `inherits` (its
  surface spelling reads the syntax layer and is a paper remark); the lemmas
  of that appendix that read the syntax layer (composites, nonroot targets)
  are paper proofs;
- a certifying tabled interpreter together with a *verified* certificate
  checker: the interpreter is untrusted, and acceptance by the checker
  carries machine-checked derivations for every claimed fact.

Not mechanized: the appendix "Adequacy for the Lazy λ-Calculus" and the
later appendices are paper proofs only.

## Reading the Statements (the Trusted Base)

To trust a theorem you need to read its statement and the definitions the
statement mentions. In reading order:

1. `InheritanceCalculus/Basic.lean`: paths, references, `Dom`, `MemRef`.
   **Convention:** paths are *reversed* lists, innermost label first, so the
   paper's `p ⌢ ℓ` (append a label at the end) is `ℓ :: p` here. Every
   statement below uses this representation.
2. `InheritanceCalculus/Inductive.lean`: the five semantic functions as a
   mutual inductive family (a least fixed point by construction), the set
   wrappers `supersSet`, `overridesSet`, `basesSet`, `resolveSet`,
   `thisSet`, and equation lemmas that restate the paper's five displayed
   equations verbatim.
3. `InheritanceCalculus/Lattice.lean`: the query lattice and the immediate
   consequence operator `TP`.
4. The statement of each headline theorem in the table below.

Every definition and theorem carries a docstring naming its counterpart in
the paper (the LaTeX label, e.g. `thm:well-defined`), so the correspondence
is checkable by grep.

## Correspondence Table

| Paper result | Lean name(s) | File |
|---|---|---|
| Five semantic equations (eq:supers .. eq:this) | `supersSet_nil`, `supersSet_cons`, `overridesSet_nil`, `overridesSet_cons`, `basesSet_nil`, `basesSet_cons`, `resolveSet_nil`, `resolveSet_cons`, `thisSet_zero`, `thisSet_succ`, `thisSet_nil_succ`, `thisSet_union` | `InheritanceCalculus/Inductive.lean` |
| Immediate consequence operator (def:tp-operator) | `TP`, `TPfun` | `InheritanceCalculus/Lattice.lean` |
| Monotonicity (lem:monotonicity) | `TPfun_mono` | `InheritanceCalculus/Lattice.lean` |
| Least fixed point exists (thm:lfp-exists) | `TP_map_lfp`, `TP_isLeast_lfp` | `InheritanceCalculus/Lattice.lean` |
| Well-definedness (thm:well-defined) | `lfp_TP_eq_toQAMap`; per-function corollaries `lfp_TP_supers` .. `lfp_TP_this` | `InheritanceCalculus/WellDefinedness.lean` |
| Kleene iteration (lem:kleene-iteration) | `lfp_TP_eq_iSup_stage`, `mem_lfp_iff_exists_stage`, `exists_kleene_rank`, `mem_stage_succ_iff` | `InheritanceCalculus/Kleene.lean` |
| Path existence (lem:path-existence) | `supersSet_nonempty_iff_existent` | `InheritanceCalculus/PathExistence.lean` |
| Dependency restriction (lem:dependency-restriction) | `restrict_lfp_eq` | `InheritanceCalculus/Restriction.lean` |
| Tabling soundness (thm:tabling-soundness) | `tabled_le_lfp` (no wrong answers), `tabled_stable_eq_lfp` (a stable accumulator is exact on reachable queries) | `InheritanceCalculus/Algorithm.lean`, `InheritanceCalculus/AlgorithmSoundness.lean` |
| Merge associativity (thm:merge-associative) | `AssociativityDocument.merge_associative`, `AssociativityDocument.merge_associative_exists` | `InheritanceCalculus/MergeAssociativity.lean`, `InheritanceCalculus/MergeSimulation.lean` |
| Merge commutativity (thm:merge-commutative) | `CommutativityDocument.merge_commutative`, `CommutativityDocument.merge_commutative_exists` | `InheritanceCalculus/MergeCommutativity.lean`, `InheritanceCalculus/MergeSimulation.lean` |
| Merge idempotence (thm:merge-idempotent) | `IdempotenceDocument.merge_idempotent`, `IdempotenceDocument.merge_idempotent_exists` | `InheritanceCalculus/MergeIdempotence.lean` |
| Monotonicity in the program (lem:program-monotonicity) | `Extends.fact`, `Extends.supersSet_subset`, `Extends.supersSet_nonempty` | `InheritanceCalculus/ProgramMonotonicity.lean` |
| Upward-closed observation (prop:upward-closed-observation) | `fact_upward_closed` | `InheritanceCalculus/ProgramMonotonicity.lean` |
| Redirection simulation (lem:redirection-simulation) | `Redirection.simulation`, `Redirection.supers_written_preserved`, `Redirection.supers_written_transferred`, `Redirection.exists_preserved`, `Redirection.exists_transferred` | `InheritanceCalculus/Substitutability.lean` |
| Substitutability of inheritance, part (b2) (thm:inheritance-substitutability) | `inheritance_substitutable` | `InheritanceCalculus/Substitutability.lean` |
| Behavior compatibility (cor:behavior-compatibility) | `Redirection.supers_written_preserved`, `Redirection.supers_written_transferred` | `InheritanceCalculus/Substitutability.lean` |
| Decomposition (thm:decomposition) | (a) `Decomposition.prefix_closed_decomposed`; (b) `Decomposition.decomposition`, `Decomposition.decomposition_exists`; the clauses (B1) to (B4) are `Decomposition.backward`, (F1) to (F4) `Decomposition.forward` | `InheritanceCalculus/Decomposition.lean` |
| Certificate checker soundness | `checkCert_sound` | `InheritanceCalculus/Certificate.lean` |
| Certifying tabled interpreter (untrusted, checked at build time) | `Interp.run`, `#guard checkCert ...` demo | `InheritanceCalculus/Interpreter.lean`, `InheritanceCalculus/Example.lean` |

`InheritanceCalculus/Example.lean` additionally derives the paper's small
worked examples by hand (positive and negative uses of path existence) and
runs the certifying interpreter at elaboration time, feeding its certificate
to the verified checker via `#guard`.

## Building

The toolchain is pinned by `lean-toolchain` (Lean 4, v4.30.0) and Mathlib is
pinned in `lakefile.lean` (tag `v4.30.0`). With [elan](https://github.com/leanprover/elan)
installed:

```
cd lean
lake exe cache get   # download prebuilt Mathlib binaries
lake build           # checks every proof in this directory
```

In the source repository the same library is also built by a fully pinned,
offline Nix derivation (`nix build -L .#mixinv2-lean-demo`); the archive
build above is the equivalent reviewer-facing path.

## Verifying There Is No `sorry` and No Extra Axiom

A successful `lake build` is already the verification; two mechanisms make
it strict:

1. Every file sets `set_option warningAsError true`, so the "declaration
   uses 'sorry'" warning is a hard build error.
2. `InheritanceCalculus/Example.lean` (section "Axiom guards") and
   `MixinV2Demo.lean` pin the axiom set of every headline theorem with
   `#guard_msgs in #print axioms <theorem>`: the build fails unless the
   theorem depends on exactly the pinned axioms, and every pinned set is
   contained in the three standard axioms `propext`, `Classical.choice`,
   `Quot.sound` (the certificate checker uses only `propext` and
   `Quot.sound`). Since `#print axioms` reports `sorryAx` for any proof
   that transitively uses `sorry`, a `sorry` anywhere in a headline
   theorem's dependency cone cannot pass the build.

To inspect independently, open any theorem in the table and run
`#print axioms <name>` in an editor, or grep the sources for `sorry`.
