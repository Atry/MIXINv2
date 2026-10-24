import InheritanceCalculus.Inductive

/-!
# Certificates and the verified checker

This module is the *checker* half of a certifying interpreter for the five
semantic equations, following the architecture of CertifyingDatalog
(Tantow–Gerlach–Mennicke–Krötzsch, "Verifying Datalog Reasoning with Lean",
ITP 2025): an untrusted evaluator emits a *certificate* for the facts it
derives, and only the certificate checker is verified. Nothing about the
evaluator (tabling strategy, memoization, termination) needs a proof; a
wrong certificate is rejected, and an accepted certificate carries a
machine-checked derivation.

- The computable primitive is `inh : Path Label → Option (List (Reference
  Label))` (finite reference lists); `toInh` reads it back as the abstract
  set-valued primitive of `Basic.lean`.
- A certificate is a list of entries in dependency order (a topologically
  ordered proof DAG, so shared sub-derivations are checked once): each entry
  claims one `Atom` and lists the premise atoms it is produced from, which
  must have appeared earlier in the certificate.
- `checkStep` decides whether one claimed atom follows from its premise atoms
  by a single constructor of `Fact` (one instance of one equation's
  right-hand side); `checkCert` folds it over the certificate.
- `checkCert_sound`: every atom of an accepted certificate is a `Fact` of the
  abstract semantics instantiated at `toInh inh`. This is the only theorem an
  interpreter's caller needs.
-/

set_option warningAsError true

namespace InheritanceCalculus

deriving instance DecidableEq for Atom

variable {Label : Type*}

/-- Read a computable primitive (finite reference lists) back as the abstract
set-valued primitive of the semantics. -/
def toInh (inh : Path Label → Option (List (Reference Label))) :
    Path Label → Option (Set (Reference Label)) :=
  fun p => (inh p).map fun refs => {r | r ∈ refs}

theorem toInh_dom {inh : Path Label → Option (List (Reference Label))}
    {p : Path Label} (h : (inh p).isSome) : p ∈ Dom (toInh inh) := by
  obtain ⟨refs, hrefs⟩ := Option.isSome_iff_exists.mp h
  simp [Dom, toInh, hrefs]

theorem toInh_memRef {inh : Path Label → Option (List (Reference Label))}
    {p : Path Label} {refs : List (Reference Label)} {r : Reference Label}
    (hrefs : inh p = some refs) (hr : r ∈ refs) : MemRef (toInh inh) r p :=
  ⟨{r' | r' ∈ refs}, by simp [toInh, hrefs], hr⟩

variable [DecidableEq Label]

/-- One certificate entry: a claimed atom together with the premise atoms it
is produced from (which must appear earlier in the certificate). -/
structure CertEntry (Label : Type*) where
  atom : Atom Label
  premises : List (Atom Label)

/-- A certificate: entries in dependency order (topologically ordered proof
DAG). -/
abbrev Certificate (Label : Type*) := List (CertEntry Label)

variable (inh : Path Label → Option (List (Reference Label)))

/-- Does `atom` follow from the premise atoms by one constructor of `Fact`
(one instance of one equation's right-hand side)? One arm per constructor;
every guard reads only the fixed primitive `inh` and the atoms themselves. -/
def checkStep : Atom Label → List (Atom Label) → Bool
  | .supers [] site pov, [] => decide (site = [] ∧ pov = [])
  | .supers (ℓq :: q) site pov,
      [.basesStar q₁ (ℓb :: site₁), .overrides q₂ pov₂] =>
      decide (q₁ = ℓq :: q ∧ site₁ = site ∧ q₂ = ℓb :: site ∧ pov₂ = pov)
  | .overrides [] pov, [] => decide (pov = [])
  | .overrides (ℓ :: p) pov, [.supers p₁ _c pbr] =>
      (inh (ℓ :: pbr)).isSome &&
        decide (p₁ = p ∧ (pov = ℓ :: p ∨ pov = ℓ :: pbr))
  | .bases (ℓ :: p) t, [.overrides q₁ (ℓov :: povt), .this p₂ pd n pcur] =>
      decide (q₁ = ℓ :: p ∧ p₂ = p ∧ pd = povt) &&
        (match inh (ℓov :: povt) with
          | some refs => refs.any fun r => decide (r.1 = n ∧ t = r.2 ++ pcur)
          | none => false)
  | .basesStar q t, [] => decide (t = q)
  | .basesStar q s, [.basesStar q₁ r, .bases r₂ s₂] =>
      decide (q₁ = q ∧ r₂ = r ∧ s₂ = s)
  | .this s _pdef 0 t, [] => decide (t = s)
  | .this s (ℓd :: pd) (n + 1) t, [.supers s₁ psite pdef₁, .this psite₂ pd₂ n₂ t₂] =>
      decide (s₁ = s ∧ pdef₁ = ℓd :: pd ∧ psite₂ = psite ∧ pd₂ = pd ∧
        n₂ = n ∧ t₂ = t)
  | _, _ => false

/-- One `checkStep` acceptance is one `Fact` constructor: if the premise
atoms are facts, the claimed atom is a fact. -/
theorem checkStep_sound {a : Atom Label} {prems : List (Atom Label)}
    (h : checkStep inh a prems = true)
    (hp : ∀ b ∈ prems, Fact (toInh inh) b) : Fact (toInh inh) a := by
  unfold checkStep at h
  split at h
  · -- supersRoot
    obtain ⟨rfl, rfl⟩ := of_decide_eq_true h
    exact Fact.supersRoot
  · -- supersStep
    obtain ⟨rfl, rfl, rfl, rfl⟩ := of_decide_eq_true h
    exact Fact.supersStep (hp _ (List.Mem.head _))
      (hp _ (List.Mem.tail _ (List.Mem.head _)))
  · -- overridesRoot
    obtain rfl := of_decide_eq_true h
    exact Fact.overridesRoot
  · -- overridesSelf / overridesBranch
    simp only [Bool.and_eq_true] at h
    obtain ⟨hsome, hdec⟩ := h
    obtain ⟨rfl, hor⟩ := of_decide_eq_true hdec
    have hsup := hp _ (List.Mem.head _)
    have hdom := toInh_dom (inh := inh) hsome
    rcases hor with rfl | rfl
    · exact Fact.overridesSelf hsup hdom
    · exact Fact.overridesBranch hsup hdom
  · -- basesStep
    simp only [Bool.and_eq_true] at h
    obtain ⟨hdec, hany⟩ := h
    obtain ⟨rfl, rfl, rfl⟩ := of_decide_eq_true hdec
    split at hany
    · rename_i refs hrefs
      obtain ⟨r, hr, hrdec⟩ := List.any_eq_true.mp hany
      obtain ⟨rfl, rfl⟩ := of_decide_eq_true hrdec
      exact Fact.basesStep (hp _ (List.Mem.head _)) (toInh_memRef hrefs hr)
        (hp _ (List.Mem.tail _ (List.Mem.head _)))
    · exact absurd hany (by simp)
  · -- basesStarRefl
    obtain rfl := of_decide_eq_true h
    exact Fact.basesStarRefl _
  · -- basesStarTail
    obtain ⟨rfl, rfl, rfl⟩ := of_decide_eq_true h
    exact Fact.basesStarTail (hp _ (List.Mem.head _))
      (hp _ (List.Mem.tail _ (List.Mem.head _)))
  · -- thisZero
    obtain rfl := of_decide_eq_true h
    exact Fact.thisZero _ _
  · -- thisSucc
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := of_decide_eq_true h
    exact Fact.thisSucc (hp _ (List.Mem.head _))
      (hp _ (List.Mem.tail _ (List.Mem.head _)))
  · -- fallback arm
    exact absurd h (by simp)

/-- Check a certificate against the atoms validated so far: each entry's
premises must already be validated, and the entry must pass `checkStep`. -/
def checkEntries : List (Atom Label) → Certificate Label → Bool
  | _, [] => true
  | done, e :: rest =>
      (decide (∀ b ∈ e.premises, b ∈ done) && checkStep inh e.atom e.premises)
        && checkEntries (e.atom :: done) rest

/-- Check a whole certificate from an empty validated set. -/
def checkCert (cert : Certificate Label) : Bool := checkEntries inh [] cert

theorem checkEntries_sound {done : List (Atom Label)}
    {cert : Certificate Label}
    (hdone : ∀ b ∈ done, Fact (toInh inh) b)
    (h : checkEntries inh done cert = true) :
    ∀ e ∈ cert, Fact (toInh inh) e.atom := by
  induction cert generalizing done with
  | nil => intro e he; simp at he
  | cons e rest ih =>
      simp only [checkEntries, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hprem, hstep⟩, hrest⟩ := h
      have hfact : Fact (toInh inh) e.atom :=
        checkStep_sound inh hstep fun b hb => hdone b (hprem b hb)
      intro e' he'
      rcases List.mem_cons.mp he' with rfl | he'
      · exact hfact
      · refine ih (done := e.atom :: done) ?_ hrest e' he'
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hfact
        · exact hdone b hb

/-- **Soundness of the checker** (the certifying-interpreter contract): every
atom claimed by an accepted certificate is a fact of the abstract semantics
at `toInh inh`. -/
theorem checkCert_sound {cert : Certificate Label}
    (h : checkCert inh cert = true) :
    ∀ e ∈ cert, Fact (toInh inh) e.atom :=
  checkEntries_sound inh (fun b hb => by simp at hb) h

end InheritanceCalculus
