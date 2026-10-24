import InheritanceCalculus.Algorithm

/-!
# Tabling soundness, part (1): no false positives

This module proves clause (1) of the paper's Theorem "Tabling soundness"
(thm:tabling-soundness): every fact the tabled evaluation of Algorithm
alg:tabled accumulates, reads through a re-entrant call, or returns belongs
to `lfp(T_P)`.

The proof is the paper's induction on the assignments to the accumulator: the
read snapshot `M` of a `compute` step is bounded by the accumulator after the
sub-calls (`hub`), which lies below `lfp(T_P)` by the induction hypothesis, so
one production `TPfun Inh M q` lands below `TPfun` at `lfp(T_P)` by
monotonicity (lem:monotonicity), which is `lfp(T_P)` itself by the fixed-point
equation (thm:lfp-exists).
-/

set_option warningAsError true

namespace InheritanceCalculus

variable {Label : Type*} (Inh : Path Label → Option (Set (Reference Label)))

/-- Match-motive for `run_le_lfp`: a call entered with the accumulator below
`lfp(T_P)` exits with the accumulator below `lfp(T_P)`. -/
def soundMotive : RunGoal Label → Prop
  | .resolve s _ sExit =>
      s.approx ≤ OrderHom.lfp (TP Inh) → sExit.approx ≤ OrderHom.lfp (TP Inh)
  | .calls s sExit =>
      s.approx ≤ OrderHom.lfp (TP Inh) → sExit.approx ≤ OrderHom.lfp (TP Inh)

/-- thm:tabling-soundness (1), algorithm level: the accumulator stays below
`lfp(T_P)` along any run, so every fact a re-entrant call reads and every fact
returned belongs to `lfp(T_P)`. -/
theorem run_le_lfp {g : RunGoal Label} (h : Run Inh g) : soundMotive Inh g := by
  induction h with
  | cached _ => exact id
  | reentry _ _ => exact id
  | @compute s s₁ q M hc hs hcalls hlb hub hcover ih =>
      intro hA
      have h₁ : s₁.approx ≤ OrderHom.lfp (TP Inh) := ih hA
      have hM : M ≤ OrderHom.lfp (TP Inh) := fun q' x hx => h₁ q' (hub q' hx).2
      intro q' x hx
      rcases hx with hx | ⟨heq, hx⟩
      · exact h₁ q' hx
      · subst heq
        rw [← TP_map_lfp Inh]
        exact TPfun_mono Inh hM _ hx
  | callsNil _ => exact id
  | callsCons _ _ ihHead ihTail => exact fun hA => ihTail (ihHead hA)

theorem rounds_le_lfp {q₀ : Query Label} {A final : QAMap Label}
    (h : Rounds Inh q₀ A final) (hA : A ≤ OrderHom.lfp (TP Inh)) :
    final ≤ OrderHom.lfp (TP Inh) := by
  induction h with
  | stable hrun _ => exact run_le_lfp Inh hrun hA
  | unstable hrun _ _ ih => exact ih (run_le_lfp Inh hrun hA)

/-- thm:tabling-soundness (1): `Tabled` iterates from the empty accumulator,
so every fact of the final accumulator, in particular every returned answer,
belongs to `lfp(T_P)`. -/
theorem tabled_le_lfp {q₀ : Query Label} {final : QAMap Label}
    (h : Tabled Inh q₀ final) : final ≤ OrderHom.lfp (TP Inh) :=
  rounds_le_lfp Inh h bot_le

/-! ## Part (3): a stable accumulator is exact on the reachable queries -/

theorem mergeAt_eq_of_subset {A : QAMap Label} {q : Query Label}
    {P : Set (Ans q)} (h : P ⊆ A q) : mergeAt A q P = A := by
  funext q'
  by_cases hq : q' = q
  · subst hq
    rw [mergeAt_self]
    exact Set.union_eq_self_of_subset_right h
  · exact mergeAt_of_ne A P hq

/-- Match-motive for `run_stack_eq`: pushes are popped in pairs, so the stack
is restored across any call. -/
def stackMotive : RunGoal Label → Prop
  | .resolve s _ sExit => sExit.stack = s.stack
  | .calls s sExit => sExit.stack = s.stack

theorem run_stack_eq {g : RunGoal Label} (h : Run Inh g) : stackMotive g := by
  induction h with
  | cached _ => rfl
  | reentry _ _ => rfl
  | @compute s s₁ q M hc hs hcalls hlb hub hcover ih =>
      show s₁.stack \ {q} = s.stack
      rw [show s₁.stack = insert q s.stack from ih]
      exact Set.insert_diff_self_of_notMem hs
  | callsNil _ => rfl
  | callsCons _ _ ihHead ihTail => exact ihTail.trans ihHead

/-- Match-motive for `run_cover_mono`: the called set `cache ∪ stack` only
grows along a run (a popped query is cached in the same step). -/
def coverMotive : RunGoal Label → Prop
  | .resolve s _ sExit => s.cache ∪ s.stack ⊆ sExit.cache ∪ sExit.stack
  | .calls s sExit => s.cache ∪ s.stack ⊆ sExit.cache ∪ sExit.stack

theorem cover_le_exit {s₁ : TState Label} {q : Query Label} :
    s₁.cache ∪ s₁.stack ⊆ (insert q s₁.cache) ∪ (s₁.stack \ {q}) := by
  rintro x (hx | hx)
  · exact Or.inl (Set.mem_insert_of_mem _ hx)
  · by_cases hxq : x = q
    · exact Or.inl (hxq ▸ Set.mem_insert _ _)
    · exact Or.inr ⟨hx, hxq⟩

theorem run_cover_mono {g : RunGoal Label} (h : Run Inh g) : coverMotive g := by
  induction h with
  | cached _ => exact Set.Subset.rfl
  | reentry _ _ => exact Set.Subset.rfl
  | @compute s s₁ q M hc hs hcalls hlb hub hcover ih =>
      intro x hx
      refine cover_le_exit (ih ?_)
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (Set.mem_insert_of_mem _ hx)
  | callsNil _ => exact Set.Subset.rfl
  | callsCons _ _ ihHead ihTail => exact ihHead.trans ihTail

/-- A witness that the equation of `q` was fully evaluated against the stable
accumulator `A` over a called set `C ⊆ R`: the snapshot is `A` restricted to
`C`, its reads stay inside `C`, and its production is absorbed by `A`. -/
def StableWitness (A : QAMap Label) (R : Set (Query Label))
    (q : Query Label) : Prop :=
  ∃ C ⊆ R, Reads Inh (QAMap.restrict C A) q ⊆ C ∧
    TPfun Inh (QAMap.restrict C A) q ⊆ A q

/-- Match-motive for `run_stable`: in a round whose exit `changed` flag is
clear, the accumulator never moves, and every newly cached query carries a
stable witness over the called queries. -/
def stableMotive (A : QAMap Label) : RunGoal Label → Prop
  | .resolve s _ sExit =>
      s.approx = A → ¬ sExit.changed →
        sExit.approx = A ∧
        ∀ q'' ∈ sExit.cache, q'' ∉ s.cache →
          StableWitness Inh A (sExit.cache ∪ sExit.stack) q''
  | .calls s sExit =>
      s.approx = A → ¬ sExit.changed →
        sExit.approx = A ∧
        ∀ q'' ∈ sExit.cache, q'' ∉ s.cache →
          StableWitness Inh A (sExit.cache ∪ sExit.stack) q''

theorem run_stable {g : RunGoal Label} (h : Run Inh g) {A : QAMap Label} :
    stableMotive Inh A g := by
  induction h with
  | cached _ => exact fun hA _ => ⟨hA, fun _ h1 h2 => absurd h1 h2⟩
  | reentry _ _ => exact fun hA _ => ⟨hA, fun _ h1 h2 => absurd h1 h2⟩
  | @compute s s₁ q M hc hs hcalls hlb hub hcover ih =>
      intro hA hch
      have hch₁ : ¬ s₁.changed := fun h₁ => hch (Or.inl h₁)
      have hprod : TPfun Inh M q ⊆ s₁.approx q := by
        by_contra hcon
        exact hch (Or.inr hcon)
      obtain ⟨hA₁, hwit₁⟩ := ih hA hch₁
      have hM : M = QAMap.restrict (s₁.cache ∪ s₁.stack) A := by
        apply le_antisymm
        · exact hA₁ ▸ hub
        · exact hA ▸ hlb
      have happrox : mergeAt s₁.approx q (TPfun Inh M q) = A := by
        rw [mergeAt_eq_of_subset hprod, hA₁]
      refine ⟨happrox, ?_⟩
      intro q'' hq'' _
      rcases Set.mem_insert_iff.mp hq'' with rfl | hq''mem
      · refine ⟨s₁.cache ∪ s₁.stack, cover_le_exit, ?_, ?_⟩
        · rw [← hM]
          exact hcover
        · rw [← hM]
          exact hA₁ ▸ hprod
      · by_cases hold : q'' ∈ s.cache
        · exact absurd hold (by assumption)
        · obtain ⟨C, hCsub, hreads, hprod''⟩ := hwit₁ q'' hq''mem hold
          exact ⟨C, hCsub.trans cover_le_exit, hreads, hprod''⟩
  | callsNil _ => exact fun hA _ => ⟨hA, fun _ h1 h2 => absurd h1 h2⟩
  | @callsCons s s' s'' q' hhead htail ihHead ihTail =>
      intro hA hch
      have hch' : ¬ s'.changed := fun h => hch ((run_growth Inh htail).2.2 h)
      obtain ⟨hA', hwit'⟩ := ihHead hA hch'
      obtain ⟨hA'', hwit''⟩ := ihTail hA' hch
      refine ⟨hA'', ?_⟩
      intro q'' hq'' hnew
      by_cases hmem : q'' ∈ s'.cache
      · obtain ⟨C, hCsub, hreads, hprod⟩ := hwit' q'' hmem hnew
        exact ⟨C, hCsub.trans (run_cover_mono Inh htail), hreads, hprod⟩
      · exact hwit'' q'' hq'' hmem

/-! ## The lattice half of part (3) -/

/-- Kleene stages stay below the stable accumulator on the witnessed set: by
induction on the stage, the stage is bounded by the pinned snapshot on the
snapshot's own reads (locality via `Reads_sub_of_le_on`), so one production
step stays inside what the stable round already absorbed. -/
theorem stable_stage_le {A : QAMap Label} {R : Set (Query Label)}
    (hw : ∀ q ∈ R, StableWitness Inh A R q) (i : ℕ) :
    ∀ q ∈ R, stage Inh i q ⊆ A q := by
  induction i with
  | zero =>
      intro q _ x hx
      exact absurd hx (by simp [stage])
  | succ i ih =>
      intro q hq x hx
      obtain ⟨C, hCR, hreads, hprod⟩ := hw q hq
      have hle : ∀ q' ∈ Reads Inh (QAMap.restrict C A) q,
          stage Inh i q' ⊆ QAMap.restrict C A q' := by
        intro q' hq' x' hx'
        exact ⟨hreads hq', ih q' (hCR (hreads hq')) hx'⟩
      have hsub : Reads Inh (stage Inh i) q ⊆ Reads Inh (QAMap.restrict C A) q :=
        Reads_sub_of_le_on Inh hle
      have hstep : TPfun Inh (stage Inh i) q ⊆ TPfun Inh (QAMap.restrict C A) q :=
        TPfun_le_of_reads Inh fun q' hq' => hle q' (hsub hq')
      rw [stage_succ] at hx
      exact hprod (hstep hx)

/-- The lattice half of thm:tabling-soundness (3): an accumulator below
`lfp(T_P)` that absorbs one full round over every query of `R` agrees with
`lfp(T_P)` on `R`. -/
theorem stable_restrict_eq_lfp {A : QAMap Label} {R : Set (Query Label)}
    (hA : A ≤ OrderHom.lfp (TP Inh))
    (hw : ∀ q ∈ R, StableWitness Inh A R q) :
    QAMap.restrict R A = QAMap.restrict R (OrderHom.lfp (TP Inh)) := by
  funext q
  ext x
  constructor
  · rintro ⟨hq, hx⟩
    exact ⟨hq, hA q hx⟩
  · rintro ⟨hq, hx⟩
    rw [lfp_TP_eq_iSup_stage] at hx
    obtain ⟨i, hxi⟩ := mem_iSup_apply_iff.mp hx
    exact ⟨hq, stable_stage_le Inh hw i q hq hxi⟩

/-- thm:tabling-soundness (3): when the iteration stabilizes, the returned
accumulator agrees with `lfp(T_P)` on the reachable queries, this round's memo
table, which contains the initial query. -/
theorem tabled_stable_eq_lfp {q₀ : Query Label} {final : QAMap Label}
    (h : Tabled Inh q₀ final) :
    ∃ R : Set (Query Label), q₀ ∈ R ∧
      QAMap.restrict R final = QAMap.restrict R (OrderHom.lfp (TP Inh)) := by
  suffices haux : ∀ {A final : QAMap Label}, Rounds Inh q₀ A final →
      A ≤ OrderHom.lfp (TP Inh) →
      ∃ R : Set (Query Label), q₀ ∈ R ∧
        QAMap.restrict R final = QAMap.restrict R (OrderHom.lfp (TP Inh)) from
    haux h bot_le
  intro A final h
  induction h with
  | @stable A sExit hrun hstable =>
      intro hA
      obtain ⟨happrox, hwit⟩ := run_stable Inh hrun (A := A) rfl hstable
      have hstack : sExit.stack = (∅ : Set (Query Label)) :=
        run_stack_eq Inh hrun
      have hq₀ : q₀ ∈ sExit.cache := by
        cases hrun with
        | cached hq => exact absurd hq (Set.notMem_empty _)
        | reentry _ hq => exact absurd hq (Set.notMem_empty _)
        | compute _ _ _ _ _ _ => exact Set.mem_insert _ _
      have hw : ∀ q' ∈ sExit.cache, StableWitness Inh A sExit.cache q' := by
        intro q' hq'
        obtain ⟨C, hCsub, hreads, hprod⟩ := hwit q' hq' (Set.notMem_empty _)
        refine ⟨C, ?_, hreads, hprod⟩
        rw [hstack, Set.union_empty] at hCsub
        exact hCsub
      refine ⟨sExit.cache, hq₀, ?_⟩
      rw [happrox]
      exact stable_restrict_eq_lfp Inh hA hw
  | @unstable A final sExit hrun hchanged hrest ih =>
      intro hA
      exact ih (run_le_lfp Inh hrun hA)

end InheritanceCalculus
