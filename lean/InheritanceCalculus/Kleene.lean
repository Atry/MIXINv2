import InheritanceCalculus.WellDefinedness

/-!
# Kleene iteration

This module proves the paper's Lemma "Kleene iteration" (lem:kleene-iteration,
tex line ~3755):

- `T_P` is ω-continuous: it commutes with suprema of nonempty directed
  families (`TP_sSup_directed`); the proof is the paper's finite-premise
  argument, with the `bases*` chain of the `supers` coordinate collapsed into
  a single family member by directedness (`reflTransGen_sSup_directed`).
- Consequently `lfp(T_P) = ⋃_{i<ω} T_Pⁱ(∅)` (`lfp_TP_eq_iSup_stage`, with
  `stage` the Kleene stages).
- Every fact of `lfp(T_P)` has a finite Kleene rank `n + 1 ≥ 1` (no fact lies
  in `stage 0 = ∅`), and a fact of `stage (n+1)` is produced by the right-hand
  side of its query's equation from facts of `stage n` (last-step inversion):
  `exists_kleene_rank` and `mem_stage_succ_iff`.
-/

set_option warningAsError true

namespace InheritanceCalculus

variable {Label : Type*}

/-- Membership in a pointwise supremum of query–answer maps. -/
theorem mem_iSup_apply_iff {ι : Sort*} {F : ι → QAMap Label} {q : Query Label}
    {x : Ans q} : x ∈ iSup F q ↔ ∃ i, x ∈ F i q := by
  simp [iSup_apply, Set.iSup_eq_iUnion, Set.mem_iUnion]

/-- Membership in a pointwise supremum over a set of query–answer maps. -/
theorem mem_sSup_apply_iff {D : Set (QAMap Label)} {q : Query Label}
    {x : Ans q} : x ∈ sSup D q ↔ ∃ M ∈ D, x ∈ M q := by
  rw [sSup_eq_iSup]
  simp [iSup_apply, Set.iSup_eq_iUnion, Set.mem_iUnion]

variable (Inh : Path Label → Option (Set (Reference Label)))

/-- Membership in the pointwise supremum of the `T_P`-images of a set of
query–answer maps. -/
theorem mem_biSup_TP_iff {D : Set (QAMap Label)} {q : Query Label}
    {x : Ans q} :
    x ∈ (⨆ M ∈ D, TP Inh M) q ↔ ∃ M ∈ D, x ∈ TP Inh M q := by
  rw [← sSup_image, mem_sSup_apply_iff]
  constructor
  · rintro ⟨N, ⟨M, hM, rfl⟩, hx⟩
    exact ⟨M, hM, hx⟩
  · rintro ⟨M, hM, hx⟩
    exact ⟨TP Inh M, ⟨M, hM, rfl⟩, hx⟩

/-- The paper's "a pair of the closure `bases*` is witnessed by a finite chain
of `bases` facts": a chain over the supremum of a nonempty directed family
lives in a single member, by directedness and induction on the chain. -/
theorem reflTransGen_sSup_directed {D : Set (QAMap Label)} (hne : D.Nonempty)
    (hdir : DirectedOn (· ≤ ·) D) {q pb : Path Label}
    (h : Relation.ReflTransGen (fun a b => b ∈ sSup D (.bases a)) q pb) :
    ∃ M ∈ D, Relation.ReflTransGen (fun a b => b ∈ M (.bases a)) q pb := by
  induction h with
  | refl =>
      obtain ⟨M, hM⟩ := hne
      exact ⟨M, hM, Relation.ReflTransGen.refl⟩
  | tail _ hbc ih =>
      obtain ⟨M₁, hM₁, hchain₁⟩ := ih
      obtain ⟨M₂, hM₂, hb₂⟩ := mem_sSup_apply_iff.mp hbc
      obtain ⟨M₃, hM₃, h13, h23⟩ := hdir M₁ hM₁ M₂ hM₂
      exact ⟨M₃, hM₃,
        Relation.ReflTransGen.tail
          (hchain₁.mono fun a b hb => h13 (.bases a) hb)
          (h23 _ hb₂)⟩

/-- lem:kleene-iteration, ω-continuity: `T_P` commutes with suprema of
nonempty directed families. Each fact is produced by one instance of a
comprehension binding finitely many premise facts; by directedness a single
member contains them all. -/
theorem TP_sSup_directed {D : Set (QAMap Label)} (hne : D.Nonempty)
    (hdir : DirectedOn (· ≤ ·) D) :
    TP Inh (sSup D) = ⨆ M ∈ D, TP Inh M := by
  apply le_antisymm
  · intro q
    cases q with
    | supers p =>
        rintro x (⟨hp, hx⟩ | ⟨hp, ℓb, hchain, hov⟩)
        · obtain ⟨M₀, hM₀⟩ := hne
          exact (mem_biSup_TP_iff Inh).mpr ⟨M₀, hM₀, Or.inl ⟨hp, hx⟩⟩
        · obtain ⟨M₁, hM₁, hchain₁⟩ :=
            reflTransGen_sSup_directed hne hdir hchain
          obtain ⟨M₂, hM₂, hov₂⟩ := mem_sSup_apply_iff.mp hov
          obtain ⟨M₃, hM₃, h13, h23⟩ := hdir M₁ hM₁ M₂ hM₂
          refine (mem_biSup_TP_iff Inh).mpr ⟨M₃, hM₃, Or.inr
            ⟨hp, ℓb, ?_, h23 _ hov₂⟩⟩
          exact hchain₁.mono fun a b hb => h13 (.bases a) hb
    | overrides p =>
        rintro pov (⟨hp, hpov⟩ | ⟨p', ℓ, c, pbr, heq, hsup, hdom, hor⟩)
        · obtain ⟨M₀, hM₀⟩ := hne
          exact (mem_biSup_TP_iff Inh).mpr ⟨M₀, hM₀, Or.inl ⟨hp, hpov⟩⟩
        · obtain ⟨M₁, hM₁, hsup₁⟩ := mem_sSup_apply_iff.mp hsup
          exact (mem_biSup_TP_iff Inh).mpr ⟨M₁, hM₁, Or.inr
            ⟨p', ℓ, c, pbr, heq, hsup₁, hdom, hor⟩⟩
    | bases p =>
        rintro t ⟨p', ℓ, pov, n, w, heq, hov, href, ht⟩
        obtain ⟨M₁, hM₁, hov₁⟩ := mem_sSup_apply_iff.mp hov
        obtain ⟨M₂, hM₂, ht₂⟩ := mem_sSup_apply_iff.mp ht
        obtain ⟨M₃, hM₃, h13, h23⟩ := hdir M₁ hM₁ M₂ hM₂
        exact (mem_biSup_TP_iff Inh).mpr ⟨M₃, hM₃,
          ⟨p', ℓ, pov, n, w, heq, h13 _ hov₁, href, h23 _ ht₂⟩⟩
    | resolve site pdef n w =>
        rintro t ⟨ℓd, pd, heq, pcur, hthis, ht⟩
        obtain ⟨M₁, hM₁, hthis₁⟩ := mem_sSup_apply_iff.mp hthis
        exact (mem_biSup_TP_iff Inh).mpr ⟨M₁, hM₁,
          ⟨ℓd, pd, heq, pcur, hthis₁, ht⟩⟩
    | this s pdef n =>
        rintro t (⟨hn, ht⟩ | ⟨m, hn, ℓd, pd, heq, psite, hsup, ht⟩)
        · obtain ⟨M₀, hM₀⟩ := hne
          exact (mem_biSup_TP_iff Inh).mpr ⟨M₀, hM₀, Or.inl ⟨hn, ht⟩⟩
        · obtain ⟨M₁, hM₁, hsup₁⟩ := mem_sSup_apply_iff.mp hsup
          obtain ⟨M₂, hM₂, ht₂⟩ := mem_sSup_apply_iff.mp ht
          obtain ⟨M₃, hM₃, h13, h23⟩ := hdir M₁ hM₁ M₂ hM₂
          exact (mem_biSup_TP_iff Inh).mpr ⟨M₃, hM₃, Or.inr
            ⟨m, hn, ℓd, pd, heq, psite, h13 _ hsup₁, h23 _ ht₂⟩⟩
  · exact iSup₂_le fun M hM => (TP Inh).monotone (le_sSup hM)

/-! ## The Kleene stages -/

/-- The Kleene stages `T_Pⁱ(∅)`. -/
def stage (n : ℕ) : QAMap Label := (⇑(TP Inh))^[n] ⊥

theorem stage_zero : stage Inh 0 = (⊥ : QAMap Label) := rfl

/-- Last-step production: `stage (n+1) = T_P(stage n)`. -/
theorem stage_succ (n : ℕ) : stage Inh (n + 1) = TP Inh (stage Inh n) :=
  Function.iterate_succ_apply' _ _ _

theorem stage_mono : Monotone (stage Inh) :=
  (TP Inh).monotone.monotone_iterate_of_le_map bot_le

theorem stage_le_lfp (n : ℕ) : stage Inh n ≤ OrderHom.lfp (TP Inh) := by
  induction n with
  | zero => exact bot_le
  | succ n ih =>
      rw [stage_succ]
      calc TP Inh (stage Inh n) ≤ TP Inh (OrderHom.lfp (TP Inh)) :=
            (TP Inh).monotone ih
        _ = OrderHom.lfp (TP Inh) := TP_map_lfp Inh

/-- lem:kleene-iteration, Kleene chain: `lfp(T_P) = ⋃_{i<ω} T_Pⁱ(∅)`. -/
theorem lfp_TP_eq_iSup_stage :
    OrderHom.lfp (TP Inh) = ⨆ n, stage Inh n := by
  apply le_antisymm
  · apply OrderHom.lfp_le
    have hd : DirectedOn (· ≤ ·) (Set.range (stage Inh)) :=
      directedOn_range.mpr (stage_mono Inh).directed_le
    have hne : (Set.range (stage Inh)).Nonempty := Set.range_nonempty _
    calc TP Inh (⨆ n, stage Inh n)
        = TP Inh (sSup (Set.range (stage Inh))) := by rw [sSup_range]
      _ = ⨆ M ∈ Set.range (stage Inh), TP Inh M := TP_sSup_directed Inh hne hd
      _ = ⨆ n, TP Inh (stage Inh n) := by rw [iSup_range]
      _ = ⨆ n, stage Inh (n + 1) := by simp_rw [← stage_succ]
      _ ≤ ⨆ n, stage Inh n := iSup_le fun n => le_iSup (stage Inh) (n + 1)
  · exact iSup_le (stage_le_lfp Inh)

/-- Every fact of `lfp(T_P)` lies in some finite stage, and conversely. -/
theorem mem_lfp_iff_exists_stage {q : Query Label} {x : Ans q} :
    x ∈ OrderHom.lfp (TP Inh) q ↔ ∃ n, x ∈ stage Inh n q := by
  rw [lfp_TP_eq_iSup_stage]
  exact mem_iSup_apply_iff

/-- lem:kleene-iteration, last-step inversion: a fact of `T_P^{i+1}(∅)` is
produced by the right-hand side of its query's equation from facts of
`T_Pⁱ(∅)`. -/
theorem mem_stage_succ_iff {q : Query Label} {x : Ans q} {n : ℕ} :
    x ∈ stage Inh (n + 1) q ↔ x ∈ TP Inh (stage Inh n) q := by
  rw [stage_succ]

/-- lem:kleene-iteration, finite Kleene rank: every fact of `lfp(T_P)` has a
least stage index; it is a successor `n + 1` (so the rank is at least 1, since
`T_P⁰(∅) = ∅`), the fact is produced from `stage n` by one application of its
equation's right-hand side, and no stage up to `n` contains it. -/
theorem exists_kleene_rank {q : Query Label} {x : Ans q}
    (h : x ∈ OrderHom.lfp (TP Inh) q) :
    ∃ n, x ∈ TP Inh (stage Inh n) q ∧ ∀ m ≤ n, x ∉ stage Inh m q := by
  have hne : {n | x ∈ stage Inh n q}.Nonempty :=
    (mem_lfp_iff_exists_stage Inh).mp h
  have hmem : sInf {n | x ∈ stage Inh n q} ∈ {n | x ∈ stage Inh n q} :=
    Nat.sInf_mem hne
  have hzero : x ∉ stage Inh 0 q := fun hx => hx
  have hpos : sInf {n | x ∈ stage Inh n q} ≠ 0 := by
    intro h0
    rw [h0] at hmem
    exact hzero hmem
  obtain ⟨n, hn⟩ : ∃ n, sInf {n | x ∈ stage Inh n q} = n + 1 :=
    ⟨sInf {n | x ∈ stage Inh n q} - 1, by omega⟩
  refine ⟨n, ?_, ?_⟩
  · have hx : x ∈ stage Inh (n + 1) q := by
      rw [← hn]
      exact hmem
    exact (mem_stage_succ_iff Inh).mp hx
  · intro m hm hx
    have hle : sInf {n | x ∈ stage Inh n q} ≤ m := Nat.sInf_le hx
    omega

end InheritanceCalculus
