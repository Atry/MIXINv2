import InheritanceCalculus.Kleene

/-!
# Dependency restriction

This module proves the paper's Lemma "Dependency restriction"
(lem:dependency-restriction, tex line ~4041): for a set `R` of queries closed
under the dependency edges of the dependency graph, the Kleene stages, and
hence the least fixed point, of the restricted operator agree with the
restrictions of the global ones.

- `Reads Inh M q` is the set of sub-queries the right-hand side of `q`'s
  equation reads under the approximation `M` (the dependency edges of the
  paper's Definition "Dependency graph", made approximation-explicit: the
  `bases*` chain of the `supers` coordinate reads one `bases` and one
  `overrides` query per chain node, and the sub-queries of `bases` and `this`
  are selected by answers of `M`). `Reads` is monotone in `M`
  (`Reads_mono`), so closure under reads at `lfp(T_P)` implies closure at
  every stage.
- The locality lemma `TPfun_le_of_reads` renders the paper's "evaluating the
  equation of a query `q ∈ R` reads only values at sub-queries in `R`": a map
  that dominates `M` on `Reads Inh M q` produces at least as much at `q`.
- `QAMap.restrict R M` empties every coordinate outside `R`; `TPr Inh R` is
  the paper's `T_P ↾ R` (restriction of `T_P` to maps on `R`, encoded in the
  full lattice with vacuous coordinates outside `R`).
- `restrict_stage_eq` is the stagewise equality
  `T_Pⁱ(∅) ↾ R = (T_P ↾ R)ⁱ(∅)` (same Kleene rank on both sides), and
  `restrict_lfp_eq` the fixed-point equality `lfp(T_P) ↾ R = lfp(T_P ↾ R)`.
-/

set_option warningAsError true

namespace InheritanceCalculus

variable {Label : Type*} (Inh : Path Label → Option (Set (Reference Label)))

/-- The sub-queries the right-hand side of `q`'s equation reads under the
approximation `M` (the dependency edges out of `q`). -/
def Reads (M : QAMap Label) : Query Label → Set (Query Label)
  | .supers [] => ∅
  | .supers (ℓq :: q) =>
      {qy | ∃ r, Relation.ReflTransGen (fun a b => b ∈ M (.bases a)) (ℓq :: q) r ∧
        (qy = .bases r ∨ qy = .overrides r)}
  | .overrides [] => ∅
  | .overrides (_ :: p) => {Query.supers p}
  | .bases [] => ∅
  | .bases (ℓ :: p) =>
      insert (Query.overrides (ℓ :: p))
        {qy | ∃ pov n w, pov ∈ M (.overrides (ℓ :: p)) ∧
          MemRef Inh (n, w) pov ∧ qy = .resolve p pov n w}
  | .resolve site (_ :: pd) n _ => {Query.this site pd n}
  | .resolve _ [] _ _ => ∅
  | .this _ _ 0 => ∅
  | .this _ [] _ => ∅
  | .this s (ℓd :: pd) (n + 1) =>
      insert (Query.supers s)
        {qy | ∃ psite, (psite, ℓd :: pd) ∈ M (.supers s) ∧ qy = .this psite pd n}

/-- `Reads` is monotone in the approximation: a larger map only lengthens the
`bases*` chains and enlarges the answer sets that select sub-queries. -/
theorem Reads_mono {M M' : QAMap Label} (h : M ≤ M') (q : Query Label) :
    Reads Inh M q ⊆ Reads Inh M' q := by
  cases q with
  | supers q =>
      cases q with
      | nil => exact Set.Subset.rfl
      | cons ℓq q =>
          rintro qy ⟨r, hchain, hor⟩
          exact ⟨r, hchain.mono fun a b hb => h (.bases a) hb, hor⟩
  | overrides q => cases q <;> exact Set.Subset.rfl
  | bases q =>
      cases q with
      | nil => exact Set.Subset.rfl
      | cons ℓ p =>
          rintro qy hqy
          rcases Set.mem_insert_iff.mp hqy with rfl | ⟨pov, n, w, hov, href, rfl⟩
          · exact Set.mem_insert _ _
          · exact Set.mem_insert_of_mem _
              ⟨pov, n, w, h (.overrides (ℓ :: p)) hov, href, rfl⟩
  | resolve site pdef n w => cases pdef <;> exact Set.Subset.rfl
  | this s pdef n =>
      cases n with
      | zero => exact Set.Subset.rfl
      | succ n =>
          cases pdef with
          | nil => exact Set.Subset.rfl
          | cons ℓd pd =>
              rintro qy hqy
              rcases Set.mem_insert_iff.mp hqy with rfl | ⟨psite, hsup, rfl⟩
              · exact Set.mem_insert _ _
              · exact Set.mem_insert_of_mem _ ⟨psite, h (.supers s) hsup, rfl⟩

/-- Locality (the paper's "`T_P(M)(q)` depends only on `M ↾ R`"): a map that
dominates `M` on the sub-queries `q` reads produces at least as much at `q`.
Together with plain monotonicity this pins `T_P(M)(q)` to the reads. -/
theorem TPfun_le_of_reads {M M' : QAMap Label} {q : Query Label}
    (h : ∀ q' ∈ Reads Inh M q, M q' ⊆ M' q') :
    TPfun Inh M q ⊆ TPfun Inh M' q := by
  cases q with
  | supers q =>
      cases q with
      | nil =>
          rintro x (⟨-, hx⟩ | ⟨habs, -⟩)
          · exact Or.inl ⟨rfl, hx⟩
          · exact absurd rfl habs
      | cons ℓq q =>
          rintro x (⟨habs, -⟩ | ⟨-, ℓb, hchain, hov⟩)
          · exact absurd habs (by simp)
          · have chain_imp : ∀ {r : Path Label},
                Relation.ReflTransGen (fun a b => b ∈ M (.bases a)) (ℓq :: q) r →
                Relation.ReflTransGen (fun a b => b ∈ M' (.bases a)) (ℓq :: q) r := by
              intro r hr
              induction hr with
              | refl => exact Relation.ReflTransGen.refl
              | @tail b c hab hbc ih =>
                  exact Relation.ReflTransGen.tail ih
                    (h (.bases b) ⟨b, hab, Or.inl rfl⟩ hbc)
            exact Or.inr ⟨by simp, ℓb, chain_imp hchain,
              h (.overrides (ℓb :: x.1)) ⟨ℓb :: x.1, hchain, Or.inr rfl⟩ hov⟩
  | overrides q =>
      cases q with
      | nil =>
          rintro pov (⟨-, hpov⟩ | ⟨p, ℓ, c, pbr, habs, -⟩)
          · exact Or.inl ⟨rfl, hpov⟩
          · exact absurd habs (by simp)
      | cons ℓ₀ p₀ =>
          rintro pov (⟨habs, -⟩ | ⟨p, ℓ, c, pbr, heq, hsup, hdom, hor⟩)
          · exact absurd habs (by simp)
          · obtain ⟨rfl, rfl⟩ : ℓ₀ = ℓ ∧ p₀ = p := by simpa using heq
            exact Or.inr ⟨p₀, ℓ₀, c, pbr, rfl, h (.supers p₀) rfl hsup, hdom, hor⟩
  | bases q =>
      cases q with
      | nil =>
          rintro t ⟨p, ℓ, pov, n, w, habs, -⟩
          exact absurd habs (by simp)
      | cons ℓ₀ p₀ =>
          rintro t ⟨p, ℓ, pov, n, w, heq, hov, href, ht⟩
          obtain ⟨rfl, rfl⟩ : ℓ₀ = ℓ ∧ p₀ = p := by simpa using heq
          exact ⟨p₀, ℓ₀, pov, n, w, rfl,
            h (.overrides (ℓ₀ :: p₀)) (Set.mem_insert _ _) hov, href,
            h (.resolve p₀ pov n w)
              (Set.mem_insert_of_mem _ ⟨pov, n, w, hov, href, rfl⟩) ht⟩
  | resolve site pdef n w =>
      cases pdef with
      | nil =>
          rintro t ⟨ℓd, pd, habs, -⟩
          exact absurd habs (by simp)
      | cons ℓd₀ pd₀ =>
          rintro t ⟨ℓd, pd, heq, pcur, hthis, ht⟩
          obtain ⟨rfl, rfl⟩ : ℓd₀ = ℓd ∧ pd₀ = pd := by simpa using heq
          exact ⟨ℓd₀, pd₀, rfl, pcur, h (.this site pd₀ n) rfl hthis, ht⟩
  | this s pdef n =>
      rintro t (⟨hn, ht⟩ | ⟨m, hn, ℓd, pd, heq, psite, hsup, ht⟩)
      · exact Or.inl ⟨hn, ht⟩
      · subst hn
        subst heq
        exact Or.inr ⟨m, rfl, ℓd, pd, rfl, psite,
          h (.supers s) (Set.mem_insert _ _) hsup,
          h (.this psite pd m) (Set.mem_insert_of_mem _ ⟨psite, hsup, rfl⟩) ht⟩

/-- If `N` is bounded by `M` on the sub-queries `M` reads at `q`, then `N`
reads no more than `M` at `q`: the `N`-chains stay inside the `M`-chains, and
the selector answers only shrink. Used by the stable-accumulator theorem
(thm:tabling-soundness (3)) with `M` the pinned snapshot of a computed query
and `N` a Kleene stage. -/
theorem Reads_sub_of_le_on {M N : QAMap Label} {q : Query Label}
    (h : ∀ q' ∈ Reads Inh M q, N q' ⊆ M q') :
    Reads Inh N q ⊆ Reads Inh M q := by
  cases q with
  | supers q =>
      cases q with
      | nil => exact Set.Subset.rfl
      | cons ℓq q =>
          have chain_imp : ∀ {r : Path Label},
              Relation.ReflTransGen (fun a b => b ∈ N (.bases a)) (ℓq :: q) r →
              Relation.ReflTransGen (fun a b => b ∈ M (.bases a)) (ℓq :: q) r := by
            intro r hr
            induction hr with
            | refl => exact Relation.ReflTransGen.refl
            | @tail b c hab hbc ih =>
                exact Relation.ReflTransGen.tail ih
                  (h (.bases b) ⟨b, ih, Or.inl rfl⟩ hbc)
          rintro qy ⟨r, hchain, hor⟩
          exact ⟨r, chain_imp hchain, hor⟩
  | overrides q => cases q <;> exact Set.Subset.rfl
  | bases q =>
      cases q with
      | nil => exact Set.Subset.rfl
      | cons ℓ p =>
          rintro qy hqy
          rcases Set.mem_insert_iff.mp hqy with rfl | ⟨pov, n, w, hov, href, rfl⟩
          · exact Set.mem_insert _ _
          · exact Set.mem_insert_of_mem _
              ⟨pov, n, w, h (.overrides (ℓ :: p)) (Set.mem_insert _ _) hov,
                href, rfl⟩
  | resolve site pdef n w => cases pdef <;> exact Set.Subset.rfl
  | this s pdef n =>
      cases n with
      | zero => exact Set.Subset.rfl
      | succ n =>
          cases pdef with
          | nil => exact Set.Subset.rfl
          | cons ℓd pd =>
              rintro qy hqy
              rcases Set.mem_insert_iff.mp hqy with rfl | ⟨psite, hsup, rfl⟩
              · exact Set.mem_insert _ _
              · exact Set.mem_insert_of_mem _
                  ⟨psite, h (.supers s) (Set.mem_insert _ _) hsup, rfl⟩

/-- Restriction of a query–answer map: the value inside `R`, empty outside
(the paper's `M ↾ R`, encoded in the full lattice). -/
def QAMap.restrict (R : Set (Query Label)) (M : QAMap Label) : QAMap Label :=
  fun q => {x | q ∈ R ∧ x ∈ M q}

theorem QAMap.restrict_le (R : Set (Query Label)) (M : QAMap Label) :
    QAMap.restrict R M ≤ M :=
  fun _ _ hx => hx.2

theorem QAMap.restrict_mono (R : Set (Query Label)) {M M' : QAMap Label}
    (h : M ≤ M') : QAMap.restrict R M ≤ QAMap.restrict R M' :=
  fun q _ hx => ⟨hx.1, h q hx.2⟩

theorem QAMap.restrict_idem (R : Set (Query Label)) (M : QAMap Label) :
    QAMap.restrict R (QAMap.restrict R M) = QAMap.restrict R M := by
  funext q
  ext x
  exact ⟨fun hx => hx.2, fun hx => ⟨hx.1, hx⟩⟩

theorem QAMap.restrict_apply_of_mem {R : Set (Query Label)} {M : QAMap Label}
    {q : Query Label} (hq : q ∈ R) : QAMap.restrict R M q = M q := by
  ext x
  exact ⟨fun hx => hx.2, fun hx => ⟨hq, hx⟩⟩

/-- `R` is closed under the dependency edges read at the approximation `M`. -/
def ReadsClosed (R : Set (Query Label)) (M : QAMap Label) : Prop :=
  ∀ q ∈ R, Reads Inh M q ⊆ R

/-- On a dependency-closed `R`, evaluating one round at `q ∈ R` against the
restricted map gives exactly the unrestricted round (the induction step of
the paper's proof). -/
theorem TPfun_restrict_eq {R : Set (Query Label)} {M : QAMap Label}
    (hcl : ReadsClosed Inh R M) {q : Query Label} (hq : q ∈ R) :
    TPfun Inh (QAMap.restrict R M) q = TPfun Inh M q := by
  apply Set.Subset.antisymm
  · exact TPfun_mono Inh (QAMap.restrict_le R M) q
  · exact TPfun_le_of_reads Inh fun q' hq' x hx => ⟨hcl q hq hq', hx⟩

/-- The paper's `T_P ↾ R`: produce with `T_P` from the restricted input and
restrict the output, so every coordinate outside `R` is vacuous. -/
def TPr (R : Set (Query Label)) : QAMap Label →o QAMap Label :=
  ⟨fun M => QAMap.restrict R (TPfun Inh (QAMap.restrict R M)),
    fun _ _ h => QAMap.restrict_mono R (TPfun_mono Inh (QAMap.restrict_mono R h))⟩

/-- The Kleene stages of the restricted operator. -/
def stageR (R : Set (Query Label)) (n : ℕ) : QAMap Label := (⇑(TPr Inh R))^[n] ⊥

theorem stageR_succ (R : Set (Query Label)) (n : ℕ) :
    stageR Inh R (n + 1) = TPr Inh R (stageR Inh R n) :=
  Function.iterate_succ_apply' _ _ _

theorem stageR_restrict (R : Set (Query Label)) (n : ℕ) :
    QAMap.restrict R (stageR Inh R n) = stageR Inh R n := by
  cases n with
  | zero =>
      funext q
      ext x
      simp [QAMap.restrict, stageR]
  | succ n =>
      rw [stageR_succ]
      exact QAMap.restrict_idem R _

theorem stageR_le_lfp (R : Set (Query Label)) (n : ℕ) :
    stageR Inh R n ≤ OrderHom.lfp (TPr Inh R) := by
  induction n with
  | zero => exact bot_le
  | succ n ih =>
      rw [stageR_succ]
      calc TPr Inh R (stageR Inh R n) ≤ TPr Inh R (OrderHom.lfp (TPr Inh R)) :=
            (TPr Inh R).monotone ih
        _ = OrderHom.lfp (TPr Inh R) := OrderHom.map_lfp _

/-- lem:dependency-restriction, stagewise: `T_Pⁱ(∅) ↾ R = (T_P ↾ R)ⁱ(∅)`, so
a fact at a query in `R` enters both iterations at the same stage index (the
same Kleene rank). -/
theorem restrict_stage_eq {R : Set (Query Label)}
    (hcl : ReadsClosed Inh R (OrderHom.lfp (TP Inh))) (i : ℕ) :
    QAMap.restrict R (stage Inh i) = stageR Inh R i := by
  have hcl_stage : ∀ j, ReadsClosed Inh R (stage Inh j) := fun j q hq =>
    (Reads_mono Inh (stage_le_lfp Inh j) q).trans (hcl q hq)
  induction i with
  | zero =>
      funext q
      ext x
      simp [QAMap.restrict, stage, stageR]
  | succ i ih =>
      have hinner : QAMap.restrict R (stageR Inh R i) =
          QAMap.restrict R (stage Inh i) := by
        rw [stageR_restrict, ← ih]
      funext q
      ext x
      constructor
      · rintro ⟨hq, hx⟩
        rw [stageR_succ]
        refine ⟨hq, ?_⟩
        rw [hinner, TPfun_restrict_eq Inh (hcl_stage i) hq]
        rw [stage_succ] at hx
        exact hx
      · intro hx
        rw [stageR_succ] at hx
        obtain ⟨hq, hx⟩ := hx
        rw [hinner, TPfun_restrict_eq Inh (hcl_stage i) hq] at hx
        rw [stage_succ]
        exact ⟨hq, hx⟩

/-- lem:dependency-restriction, fixed points:
`lfp(T_P) ↾ R = lfp(T_P ↾ R)` for `R` dependency-closed at `lfp(T_P)`. -/
theorem restrict_lfp_eq {R : Set (Query Label)}
    (hcl : ReadsClosed Inh R (OrderHom.lfp (TP Inh))) :
    QAMap.restrict R (OrderHom.lfp (TP Inh)) = OrderHom.lfp (TPr Inh R) := by
  apply le_antisymm
  · intro q x hx
    obtain ⟨hq, hx⟩ := hx
    rw [lfp_TP_eq_iSup_stage] at hx
    obtain ⟨i, hxi⟩ := mem_iSup_apply_iff.mp hx
    have hmem : x ∈ stageR Inh R i q := by
      rw [← restrict_stage_eq Inh hcl i]
      exact ⟨hq, hxi⟩
    exact stageR_le_lfp Inh R i q hmem
  · apply OrderHom.lfp_le
    intro q x hx
    obtain ⟨hq, hx⟩ := hx
    rw [QAMap.restrict_idem, TPfun_restrict_eq Inh hcl hq] at hx
    refine ⟨hq, ?_⟩
    rw [← TP_map_lfp Inh]
    exact hx

end InheritanceCalculus
