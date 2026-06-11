---
name: claim-audit
description: "Adversarially check that a paper's claims actually hold and are sufficiently argued. Hand the FULL text to a hostile expert referee that tries to break each claim and reports unsupported claims, proof gaps, overclaims, undischarged assumptions, non-sequiturs, definitional equivocation, and concrete counterexamples, then iterate by proving the gap or weakening the claim until a fresh independent skeptic finds no blocker. This is the complement of blind-read: blind-read checks whether prose is understandable; claim-audit checks whether it is TRUE and EARNED. Use for substantive / soundness / referee review of a paper, proof, theorem, or technical argument. Trigger when the user asks to 审查论证 / 实质审查 / 红队 / referee / check the claims hold / is the argument sound / 论证是否充分."
---

# Claim Audit

The author reads charitably, filling every gap as well as they wrote it; that is exactly why their
own argument looks airtight to them. A hostile expert reading adversarially, disbelieving each claim
until it is earned, exposes the steps that do not actually follow. Run that referee as a subagent and
loop until the argument stands on its own.

This is the opposite posture to **blind-read**. There the reviewer is a *naive* reader given *only*
the target, checking *comprehensibility* and forbidden to use outside knowledge. Here the reviewer is
an *expert* given the *whole* paper plus its background, checking *soundness*, and required to use
outside knowledge to attack. Do not conflate the two: a passage can be perfectly clear and perfectly
wrong, or rigorous and unreadable. Run both; they catch disjoint defects.

## What it checks, and what it does not

- **Checks:** does each claim hold? Is it argued at the strength it is stated? Is every premise it
  leans on either proven, assumed-and-flagged, or cited correctly? Does the proof have gaps, missing
  cases, or hidden assumptions? Does any claim overrun what its proof or experiment actually delivers?
  Is a counterexample available? Do the parts contradict each other?
- **Does NOT check:** comprehensibility (that is blind-read), prose style, notation aesthetics, or
  whether the work is *interesting*. Novelty is in scope only as a factual claim ("first to", "unlike
  prior work X") to be checked against what is cited, not as a taste judgment.

## Hard rules

1. **Hostile expert, full context, default-disbelieve.** Give the reviewer the entire paper (and the
   relevant prior sections / cited-result statements it needs), tell it the assumed expert audience,
   and tell it to treat every claim as *unestablished until the text earns it*. Never tell it what you
   *meant*, never defend a claim, never hand it the author's intent. Unlike blind-read, it MAY and
   SHOULD use domain knowledge and targeted lookups to find counterexamples or verify a cited result.
2. **Every defect must be concrete.** A defect is a counterexample, an exact step that does not follow
   ("line L infers B from A, but A allows ¬B because ..."), an undischarged assumption named, or a
   citation shown not to support the claim attributed to it. A doubt the reviewer cannot verify
   from the text and domain knowledge is a **QUESTION**, not a defect. Do not pad the
   ledger with questions dressed as defects.
3. **Judge the claim at its stated strength.** The defect is the gap between what is *written* and
   what is *earned*. Read the quantifiers and modifiers literally: *any / every / unique / optimal /
   minimal / iff / decidable / efficient / for all*. A proof of "for some" under a claim of "for all"
   is an overclaim even when the proof is correct. Conversely, do not invent a stronger claim than the
   text makes and then fault it.
4. **No charity, but no nitpitting either.** Do not silently repair a gap the way the author would;
   report it. But a defect must change whether a claim *holds* or *is earned* — typos, looseness that
   any expert auto-corrects, and matters of taste are out of scope (note at most once, as MINOR).
5. **A brand-new subagent each round, blind to every earlier round.** One that saw a prior round,
   the prior ledger, the author's rebuttal, or the diff is spoiled. This binds the RE-AUDIT after a
   fix hardest, because that is when the temptation to prime is strongest: do **not** tell the new
   skeptic what the last round found, what you changed, or which claims to "verify are now fixed."
   Naming the prior defect turns an independent attack into a confirmation pass — the skeptic
   rationalises the repair (hunting for the disclaimer you mention, agreeing it is "now resolved")
   instead of trying to break the claim from scratch. Hand the new skeptic ONLY the revised text and
   the audience, framed as a first audit, exactly as round one. If a specific claim worries you, let
   the skeptic re-derive it from the text; never flag it as previously-defective or already-patched.

## The unit of review: a claim

Enumerate the claims before auditing, so none is skipped and each gets a verdict. Claims live in:

- **Stated results** — every theorem, lemma, proposition, corollary, and the proof obligations they carry.
- **Abstract and introduction promises** — every "we show / prove / give / guarantee", every
  superlative ("optimal", "the most any procedure can"), every "any / all / never". These are claims
  even when no theorem is attached, and they are where overclaim hides.
- **Definitions' implied properties** — a definition that asserts existence, uniqueness, well-definedness,
  or decidability ("the least fixpoint", "decidable identity") carries a claim that must be discharged.
- **Examples and instances** — each claim that an example *instantiates* the general construction
  (it must actually satisfy the definitions, not merely resemble them).
- **Evaluation claims** — every empirical assertion ("runs in O(mn)", "folds to a finite graph",
  "self-hosts"): does the experiment as described actually measure it, with a fair baseline and no confound?

## Defect taxonomy (hunt these)

- **Unsupported claim** — asserted with no proof, evidence, or citation; the burden is never discharged.
- **Proof gap** — a step that does not follow, or real work hidden behind "clearly / obviously / it
  follows / one checks / by a standard argument". Name the inference and why it fails.
- **Missing case** — a proof by cases that omits one; an induction missing a base or a step; a claim
  "for all X" whose argument silently assumes X is finite / non-empty / well-founded / deterministic.
- **Undischarged assumption** — the argument needs a hypothesis (continuity, monotonicity, decidability,
  totality, a side condition on M or F) that is used but never stated or never shown to hold.
- **Overclaim / scope creep** — the proof or experiment establishes strictly less than the claim's
  quantifier or modifier ("optimal", "any coalgebra", "uniquely", "iff") asserts.
- **Non-sequitur** — the conclusion does not follow from the stated premises even granting them.
- **Counterexample** — an instance satisfying the hypotheses but violating the conclusion. The strongest
  defect; state it explicitly and minimally.
- **Circularity** — the argument assumes (a consequence of) what it sets out to prove.
- **Equivocation / definitional drift** — one term used with two meanings across the argument, or used
  differently from its definition (e.g. "identity", "solution", "rational", "least") shifting mid-proof.
- **Quantifier error** — wrong order (∀∃ vs ∃∀), or a bound variable smuggling a dependence.
- **Citation misuse** — a cited result does not state what it is invoked for, or is invoked outside its
  hypotheses; a "well known" fact that is false or folklore-misremembered.
- **Internal inconsistency** — two passages (abstract vs theorem, definition vs use, two theorems)
  that cannot both hold.
- **Vacuity** — technically true but says nothing, or true only because a hypothesis is never satisfiable.
- **Empirical defect** — the measurement does not isolate the claimed quantity; unfair or missing
  baseline; a confound; a benchmark that does not exercise the claimed regime; an asymptotic claim
  read off too few points.

## Severity

- **BLOCKER** — the claim is false (counterexample), or a central argument is broken with no evident repair.
- **MAJOR** — a real gap, overclaim, undischarged assumption, or unsupported load-bearing claim that
  must be fixed before the claim can stand.
- **MINOR** — a local imprecision, easily patched, that does not threaten the claim (a missing side
  condition that clearly holds, a loose quantifier in prose the theorem states correctly).
- **QUESTION** — the reviewer cannot verify from the text and domain knowledge; needs the author to
  point at the discharging argument. Not yet a defect.

## Loop

1. Write the prose under audit, plus whatever context the reviewer needs to judge it (the prior
   sections, the statements of any cited results it must check against), into a throwaway temp file
   via `mktemp /tmp/claim-audit.XXXXXX.txt`. Unlike blind-read, **more context is better**: give the
   reviewer the full paper if the claims span it, so it can catch inconsistency and trace each premise
   to where it is discharged. State the assumed expert audience (e.g. "a PL theorist who knows
   coalgebra, domain theory, and the λ-calculus"). The temp file holds the paper and its background
   ONLY — never the prior round's ledger, your fix notes, or a diff (hard rule 5).
2. Spawn one fresh `Agent` (general-purpose) with the prompt below. For a thorough audit of a paper
   with many claims, fan out: one skeptic per claim (or per lens — proof-validity, claim-vs-evidence,
   assumptions/edge-cases, consistency, citation-accuracy), then an intra-round verification pass that
   tries to *refute each reported defect* — keep only defects that survive a majority of independent
   skeptics, because a hostile reader can hallucinate a gap as easily as an author can hide one. These
   intra-round refutation subagents may be told the specific defect they are tasked to refute; this
   exemption is intra-round only. The blind rule (hard rule 5) binds the RE-AUDIT across rounds: never
   prime a re-audit subagent with prior findings.
3. Read the ledger. For each defect decide, **as a judgment to surface to the author, not to make
   silently** (changing a paper's claims is the author's call): prove the gap, *weaken the claim to
   exactly what is earned*, state and discharge the missing assumption, add the missing case, supply
   evidence or a fair baseline, fix the citation, or — if the defect is the reviewer's error — record
   why it is not real. Weakening to match the proof is usually the honest fix and the project's house
   style; resist patching by adding hand-waving.
4. Re-audit with a new skeptic after fixes, since each fix changes the argument the next reviewer
   sees. Give it the revised paper and the audience and NOTHING about the prior round — no findings,
   no diff, no "a prior audit found X, confirm it is now resolved." It must attack the new text from
   scratch, framed as a first audit; a primed re-audit returns a confirmation, not a test (hard rule 5).

**Pass only when** a fresh independent skeptic, given the full text, returns no BLOCKER and no MAJOR,
every theorem's obligations discharged, every abstract/intro superlative matched by a result, and every
open QUESTION either answered in the text or consciously accepted. If you must excuse a gap ("an expert
would see it holds"), make the text *show* it holds or weaken the claim; the excuse is the author's
charity, the very bias this test exists to defeat.

## Subagent prompt

```
You are a hostile expert referee for a top venue, reviewing for SOUNDNESS, not clarity. Assumed
expert audience / your own expertise: <AUDIENCE>. Read the file <PATH> (the paper, with any context
it needs). You MAY use your domain knowledge and may look up a cited result or a counterexample;
you may NOT assume anything the text does not earn, and no one will tell you what the authors meant.

Treat every claim as UNESTABLISHED until the text earns it at the strength it is stated.

1. CLAIM LEDGER. Enumerate the claims (theorems/lemmas/propositions; every "we show/prove/guarantee"
   and every superlative or "any/all/unique/optimal/iff/decidable/efficient" in the abstract and intro;
   existence/uniqueness/well-definedness/decidability asserted by definitions; that each example
   instantiates the construction; every empirical assertion). For EACH claim give:
   - the claim, quoted, with its exact quantifiers/modifiers;
   - where it is argued (proof / evidence / citation / nowhere);
   - VERDICT: SUPPORTED | GAP | UNSUPPORTED | OVERCLAIMED | FALSE | QUESTION;
   - if not SUPPORTED, the CONCRETE defect: a counterexample (state it minimally), or the exact step
     that does not follow ("infers B from A at <loc>, but A permits ¬B because ..."), or the named
     undischarged assumption, or the citation shown not to support it;
   - SEVERITY: BLOCKER | MAJOR | MINOR | QUESTION.
2. CROSS-CUTTING. Internal inconsistencies (abstract vs theorem, definition vs use, theorem vs
   theorem); a term used with two meanings (equivocation); an assumption used in several places but
   stated in none.
3. STRONGEST ATTACK. The single defect most likely to sink the paper, with your best attempt to make
   it concrete (a counterexample or an irreparable step).
4. VERDICT: would you accept the claims as proven? (yes / no, with the blockers.)

Rules: every defect must be concrete — a doubt you cannot make concrete is a QUESTION, not a defect.
Judge each claim at its WRITTEN strength: a correct proof of less than is claimed is an OVERCLAIM.
Do not silently repair gaps the way an author would, and do not nitpick typos or taste. Be adversarial:
your job is to break the claims, not to appreciate them.
```

## Scaling to a panel

For a high-stakes or claim-dense paper, one reviewer under-covers. Fan out a finder per claim (or
per lens above), then run the intra-round defect-refutation pass described in Loop Step 2. Diverse
lenses (proof-validity vs claim-vs-evidence vs citation-accuracy) catch failure modes a single pass
misses. The Workflow tool's pipeline / adversarial-verify patterns are built for exactly this scale.

## Notes

- Run rounds serially once you start fixing (each fix changes the argument); fan out only within a round.
- **Do not re-run a subagent on the same unchanged text.** Multiple subagents on unchanged text add
  no new signal — only cost. Re-run only after the text was actually revised.
  A trivial edit (wording, punctuation) does not justify a new round; re-run when a claim was
  strengthened, weakened, or a proof step was added or removed.
- **The re-audit must be blind, or it proves nothing.** A fix is validated only by a skeptic that
  rediscovers, from the text alone, that the claim is now sound — without being told it was ever in
  doubt. The moment you write "a prior audit flagged X; check it is fixed," "the disclaimer is now
  present," or paste the old ledger, the skeptic confirms your repair instead of re-breaking the
  claim, and a real residual defect (or a new one the fix introduced) slips through. Frame every
  re-audit as a first audit on the current text; if it returns "sound," that means an unprimed expert
  could not break it, which is the only verdict worth having.
- Keep the audience fixed across rounds, and pitch it at the real venue's expertise — too naive an
  expert manufactures false gaps (it lacks the knowledge to see the step), too generous a one waves
  real gaps through. When unsure, err toward the more demanding referee.
- The honest fix for most overclaims is to weaken the claim to what is proven, not to bolt on a
  hand-waving argument for the stronger one. Surface the choice to the author; do not make it silently.
- Soundness only. Pair with blind-read for comprehensibility; the two are independent gates and a
  paper must pass both.
