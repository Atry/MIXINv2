import InheritanceCalculus.Certificate
import InheritanceCalculus.Lattice

/-!
# A certifying tabled interpreter

The *evaluator* half of the certifying interpreter: a bottom-up, tabled
saturation of the five equations over the queries reachable from an initial
query, emitting one certificate entry per newly derived fact. Nothing here is
verified, and nothing needs to be: the emitted certificate is validated by the
verified checker of `Certificate.lean`, whose `checkCert_sound` transfers every
claimed atom into the abstract semantics. This is the certifying-computation
split of CertifyingDatalog (Tantow et al., ITP 2025): verify the checker, not
the engine.

- The table is the pair of a fact list (derived `Atom`s, deduplicated: the
  accumulator of the paper's Algorithm alg:tabled restricted to atoms) and a
  query list (the reachable sub-queries discovered so far).
- `produce` computes one right-hand-side round of one query's equation against
  the current facts, returning each produced atom with the premise atoms of
  the instance that produced it (the certificate entry).
- `subQueries` reads off the sub-queries an equation instance binds, which
  seeds the reachable-query table (the dependency edges of the paper's
  Definition "Dependency graph").
- `Interp.run` iterates rounds under a fuel bound; on cyclic inheritance
  hierarchies the accumulator converges exactly as in Algorithm alg:tabled,
  and exhausted fuel merely truncates the fact set, never falsifies it, since
  every emitted entry is checked independently.
- The `resolve` coordinate is inlined into `bases` production (as in the
  `Fact` constructor `basesStep`), so `resolve` queries produce nothing.
-/

set_option warningAsError true

namespace InheritanceCalculus

deriving instance DecidableEq for Query

variable {Label : Type*} [DecidableEq Label]

/-- The interpreter state: derived facts (newest first), certificate entries
in *reverse* derivation order, and the reachable queries discovered so far. -/
structure Interp (Label : Type*) where
  facts : List (Atom Label)
  certRev : Certificate Label
  queries : List (Query Label)

/-- The emitted certificate, in derivation order (premises precede uses). -/
def Interp.certificate (st : Interp Label) : Certificate Label :=
  st.certRev.reverse

/-- Record a produced fact with the premises of the instance that produced
it; a fact already in the table keeps its first derivation. -/
def Interp.addFact (st : Interp Label) :
    Atom Label × List (Atom Label) → Interp Label :=
  fun (a, prems) =>
    if a ∈ st.facts then st
    else { st with facts := a :: st.facts, certRev := ⟨a, prems⟩ :: st.certRev }

/-- Register a reachable sub-query. -/
def Interp.addQuery (st : Interp Label) (qy : Query Label) : Interp Label :=
  if qy ∈ st.queries then st else { st with queries := qy :: st.queries }

variable (inh : Path Label → Option (List (Reference Label)))

/-- One production round of one query's equation against the current facts:
every instance of the right-hand side whose bound sub-query facts are already
in the table, each paired with those premise facts. -/
def produce (facts : List (Atom Label)) : Query Label →
    List (Atom Label × List (Atom Label))
  | .supers [] => [(.supers [] [] [], [])]
  | .supers (ℓq :: q) =>
      let qp := ℓq :: q
      (.basesStar qp qp, ([] : List (Atom Label))) ::
        facts.flatMap fun a => match a with
          | .basesStar q₀ r =>
              if q₀ = qp then
                (facts.flatMap fun b => match b with
                  | .bases r₂ s =>
                      if r₂ = r then
                        [(.basesStar qp s, [.basesStar qp r, .bases r s])]
                      else []
                  | _ => []) ++
                (match r with
                  | _ :: site =>
                      facts.flatMap fun c => match c with
                        | .overrides q₂ pov =>
                            if q₂ = r then
                              [(.supers qp site pov,
                                [.basesStar qp r, .overrides r pov])]
                            else []
                        | _ => []
                  | [] => [])
              else []
          | _ => []
  | .overrides [] => [(.overrides [] [], [])]
  | .overrides (ℓ :: p) =>
      facts.flatMap fun a => match a with
        | .supers p₀ c pbr =>
            if p₀ = p ∧ (inh (ℓ :: pbr)).isSome then
              [(.overrides (ℓ :: p) (ℓ :: p), [.supers p c pbr]),
               (.overrides (ℓ :: p) (ℓ :: pbr), [.supers p c pbr])]
            else []
        | _ => []
  | .bases [] => []
  | .bases (ℓ :: p) =>
      facts.flatMap fun a => match a with
        | .overrides q₀ (ℓov :: povt) =>
            if q₀ = ℓ :: p then
              match inh (ℓov :: povt) with
              | some refs =>
                  refs.flatMap fun (n, w) =>
                    facts.flatMap fun b => match b with
                      | .this p₂ pd n₂ pcur =>
                          if p₂ = p ∧ pd = povt ∧ n₂ = n then
                            [(.bases (ℓ :: p) (w ++ pcur),
                              [.overrides (ℓ :: p) (ℓov :: povt),
                               .this p povt n pcur])]
                          else []
                      | _ => []
              | none => []
            else []
        | _ => []
  | .resolve _ _ _ _ => []
  | .this s pdef 0 => [(.this s pdef 0 s, [])]
  | .this _ [] (_ + 1) => []
  | .this s (ℓd :: pd) (n + 1) =>
      facts.flatMap fun a => match a with
        | .supers s₀ psite pov =>
            if s₀ = s ∧ pov = ℓd :: pd then
              facts.flatMap fun b => match b with
                | .this psite₂ pd₂ n₂ t =>
                    if psite₂ = psite ∧ pd₂ = pd ∧ n₂ = n then
                      [(.this s (ℓd :: pd) (n + 1) t,
                        [.supers s psite (ℓd :: pd), .this psite pd n t])]
                    else []
                | _ => []
            else []
        | _ => []

/-- The sub-queries one query's equation reads (the dependency edges of the
paper's Definition "Dependency graph"), against the current facts. -/
def subQueries (facts : List (Atom Label)) : Query Label → List (Query Label)
  | .supers [] => []
  | .supers (ℓq :: q) =>
      facts.flatMap fun a => match a with
        | .basesStar q₀ r =>
            if q₀ = ℓq :: q then [.bases r, .overrides r] else []
        | _ => []
  | .overrides [] => []
  | .overrides (_ :: p) => [.supers p]
  | .bases [] => []
  | .bases (ℓ :: p) =>
      Query.overrides (ℓ :: p) ::
        facts.flatMap fun a => match a with
          | .overrides q₀ (ℓov :: povt) =>
              if q₀ = ℓ :: p then
                match inh (ℓov :: povt) with
                | some refs => refs.map fun (n, _) => Query.this p povt n
                | none => []
              else []
          | _ => []
  | .resolve _ _ _ _ => []
  | .this _ _ 0 => []
  | .this _ [] (_ + 1) => []
  | .this s (ℓd :: pd) (n + 1) =>
      Query.supers s ::
        facts.flatMap fun a => match a with
          | .supers s₀ psite pov =>
              if s₀ = s ∧ pov = ℓd :: pd then [Query.this psite pd n] else []
          | _ => []

/-- One tabling round: produce every reachable query's equation once against
the accumulated facts, then grow the reachable-query table. -/
def Interp.round (st : Interp Label) : Interp Label :=
  st.queries.foldl
    (fun st qy =>
      let st := (produce inh st.facts qy).foldl Interp.addFact st
      (subQueries inh st.facts qy).foldl Interp.addQuery st)
    st

/-- Run `fuel` tabling rounds from an initial query. The accumulator only
grows, so extra rounds are harmless; too few rounds truncate the fact set but
never falsify it (each emitted entry is independently validated by
`checkCert`). -/
def Interp.run (fuel : ℕ) (initial : Query Label) : Interp Label :=
  (Interp.round inh)^[fuel] ⟨[], [], [initial]⟩

end InheritanceCalculus
