---
name: paper-writing
description: "LaTeX style and conventions for the inheritance-calculus / first-order paper: section/subsection Title Case, paragraph sentence case with no trailing period, American spelling kept consistent across the paper, forward references forbidden by default (except deliberate roadmaps), an honest register that prefers first-person 'we' and 'recall' over impersonal universals that overclaim, how to build the paper (latexmk on preprint.tex / submission.tex, not the shared body fragment), adding TeXLive packages in modules/texlive.nix, and paper variable-naming rules (no single-letter or abbreviated names except fixed formal notation). Use when editing the paper's .tex files, building the PDF, or adding LaTeX packages."
---

# Paper Writing (inheritance-calculus / first-order paper)

## Author-Side Notes (Chinese comments) — mandatory, never omit

This convention, and the distribution rule below, come from the current session's discussion. Treat it
as a hard requirement when editing the paper: it is **not** optional, and the notes are **not** to be
dropped to save space.

Keep two strictly separated registers, marked by language:

- **Reader-facing prose is English.** Anything the reader sees (section and paragraph bodies, captions,
  anything outside a `%` comment) is English.
- **Author-side notes are Chinese `%` comments.** The author's perspective — the thinking that guides how
  you write, the constraints in force, the decisions taken and *why* — goes in Chinese comments. A Chinese
  line is a note to the author and must never reach the reader; an English line is reader-facing. The
  language itself marks which side a line belongs to.

What the user tells you (a correction, a lesson, a framing, a constraint, a decision and its reason)
defaults to an author-side Chinese comment, **not** body text (see the general rule in `CLAUDE.md`).
Record every constraint and decision, with its reason, as such a note: the comments are how the next
editor, and you later, recover why the prose is shaped as it is. Omitting them is a defect.

**Distribute the notes; do not concentrate them.** Each author-side note lives next to the paragraph,
figure, or `\input` it informs, as a margin note at its site, never as one big block at the top of the
section. A single concentrated block is wrong (this was the specific mistake corrected in this session):
split it so each constraint or decision sits beside the text it governs. For example, the figure's note
goes by the figure, a generation gotcha by the `\input` that depends on it, and a paragraph's framing
just above that paragraph.

## LaTeX Style (inheritance-calculus paper)

### Heading capitalization

- `\section` and `\subsection`: **Title Case** (capitalize all major words; lowercase articles, prepositions, and conjunctions unless they are the first word).
- `\paragraph`: **Sentence case** (capitalize only the first word and proper nouns).

### No overuse of parentheses

Parentheses in prose interrupt the main line and signal that content was not woven in. Two rules:

1. **Do not use parentheses for defensive or clarifying asides** that break the sentence's flow — move them to a footnote or rewrite them into the sentence instead.
2. **Parentheses for citation keys and cross-references are fine** (`\cite{...}`, `\ref{...}`).

```latex
% ✗ BAD — defensive aside breaks flow
The solver halts (when finitely many states are reachable) and returns a finite graph.

% ✓ GOOD — woven in
The solver halts when finitely many states are reachable and returns a finite graph.
```

### Honest register: prefer "we" and "recall"

Use first-person "we" and the verb "recall" to keep claims honest about whose they are and where they come from. The failure mode they prevent is the impersonal universal that reads as objective truth, so overclaims, and invites a skeptical reader to ask "prove it". As one author put it, "we" is good precisely because it is honest: it does not disguise our own work as truth.

**Prefer "we" for our choices, observations, definitions, and reasoning.** First-person "we" marks a claim as something the authors do, want, observe, define, or conclude, not as a fact of the world: "we want to understand X", "we observe that Y", "we require Z", "we define W", "we conclude V", "we prove U". An impersonal proclamation ("X solves them all", "any Y is Z") disguises our claim as truth; the reader's instinct is then to ask why it holds and where the proof is, and the sentence overclaims whenever the support is weaker than the universal it states. Plainly narrating what we did, what we want, and what our reasoning is, is the antidote to the boastful register. Keep it textbook-plain while doing so: "we" earns honesty, not a license for literary flourish (no rhetorical questions, no "the code is telling", no anthropomorphism).

```latex
% ✗ BAD — impersonal universal disguised as truth, invites "prove it"
This one interpreter solves every computable coalgebra.

% ✓ GOOD — honest about whose claim it is and how far we have earned it
We observe that the same algorithm applies to every computable coalgebra, and we
prove this in Appendix~\ref{sec:tabling}.
```

**Prefer "recall" for prior or standard results we lean on but do not claim.** When the prose invokes a known result, a cited theorem, or a standard fact that the argument depends on but that is not a contribution of this paper, say "we recall" or "recall that". This is honest about provenance: it marks the result as established elsewhere, separates the load-bearing prior work we rely on from the new results we prove, and keeps a reader from either crediting a borrowed result to this paper or doubting it as though we were asserting it unsupported.

```latex
% ✗ BAD — states a known result as if it were ours to assert here
Tabled evaluation faithfully computes the least fixpoint.

% ✓ GOOD — marked as recalled prior work, with the citation
We recall that tabled evaluation faithfully computes the least fixpoint~\cite{tamaki-sato}.
```

The two split the labor cleanly: "we recall" is what we take from others, "we prove" or "we show" is what we add. Keeping them lexically distinct lets a reader see at a glance which claims rest on cited prior work and which the paper earns for itself.

**A menu of honest first-person verbs, grouped by what each one marks.** The honesty is in choosing the verb whose strength equals what we have actually earned. Reaching for a stronger verb than the support warrants is the overclaim to avoid.

- **Prior work we lean on, not ours:** we recall, we use, we rely on, we build on, we adopt, we follow; "following \cite{...}, we ...".
- **Stipulations, which are choices and not truth claims:** we define, we call $X$ a ..., we write $X$ for ..., we take $X$ to be ..., we let, we fix, we choose, we restrict to, we consider. A definition or a choice cannot overclaim, so these are honest by construction.
- **What we are after (motivation):** we want, we aim to, we seek, we ask (a question we then go on to address).
- **Modest observations, not deep theorems:** we observe, we note, we remark, we find.
- **Results we have actually earned, and only then:** we prove, we show, we establish, we derive, we verify.
- **Inferences from what precedes:** we conclude, we infer.
- **Things we have not proven, said as such:** we conjecture, we expect, we believe, we suspect; "we do not prove $X$, but ..."; "we leave $X$ to future work"; for evidence short of proof, "the tests confirm $X$" or "we observe empirically that $X$", never "we show".

The verb is a promise about provenance and strength. Use "we recall" or "we use" for what is not ours; "we define" or "we take" or "we fix" for what we merely stipulate; "we observe" or "we note" for what is easy; "we prove" or "we show" or "we establish" only for what we have earned; and "we conjecture" or "we expect", or an explicit "we do not prove this", for what we have not. The most common single dishonesty is a proof verb ("we show", "this establishes") for something only illustrated or expected, but the opposite, a timid verb for a result actually proven, is just as inaccurate: it buries an earned contribution and understates the paper. When in doubt, do not guess in either direction: verify the support and match the verb to it.

**This matters especially for an agent writing across compressed contexts, and the error cuts both ways.** After a context is summarized, an agent may no longer hold a claim's provenance: whether it was proven here, recalled from a citation, only illustrated, or merely expected. Forgetting that a claim is unproven, the agent reaches for a fluent strong verb and overclaims. Forgetting that a result was in fact proven earlier, the agent hedges it as "we observe" or "we expect" and underclaims. Both misrepresent strength, and fluency is evidence of neither. So the countermeasure is not to default to the weaker verb, which only trades one error for the other, but to re-verify at the moment of writing: locate the theorem, the citation, or the experiment, and match the verb to what you find. Only when you genuinely cannot resolve it should you flag the uncertainty rather than silently pick a strength. A compressed context must launder neither an unearned claim into a strong verb nor an earned one into a timid one.

### No casual forward references

By **default, do not forward-reference** later theorems, sections, or definitions from earlier text (a `\ref{thm:...}` / `\ref{sec:...}` pointing forward, "proved in Section N below", "see Theorem M"). Forward references make earlier text lean on results the reader has not seen yet, read as self-justification, and often duplicate a roadmap the introduction already gives. State each claim where it stands and let later sections refer back to earlier ones, not the reverse.

Two failure modes to avoid:

1. **Justifying a present choice by a future proof** ("we restrict to X because Theorem N, later, needs it") — give the reason self-contained, without the numbered pointer.
2. **Dumping a contributions roadmap mid-text** ("the paper proves A (Thm 1), B (Thm 2), C (Thm 3)") — the introduction already lists contributions; do not repeat the forward pointers inside a definitions or background section.

**Exception:** a *deliberate* roadmap or preview, where signposting what is coming is the explicit purpose of the passage (the closing paragraph of an introduction, or a sentence opening a section that announces what it will establish). There the forward reference is intentional and earns its place.

```latex
% ✗ BAD — earlier text leans on a later result
We restrict to the deterministic effect, on which the metric argument of
Theorem~\ref{thm:unique} (Section~\ref{sec:order}) relies.

% ✓ GOOD — self-contained reason, no forward pointer
We restrict to the deterministic effect: a layer then exposes a single
operation at the root, which the uniqueness of the solution requires.
```

### No hard line breaks within prose paragraphs

Do not insert hard line breaks inside a prose paragraph; rely on the editor's soft wrapping. A blank line still ends a paragraph; structural commands (`\paragraph`, `\begin`, `\end`, etc.) still go on their own lines.

### No trailing periods in headings

`\paragraph` headings must **not** end with a period:

```latex
% ✗ BAD
\paragraph{Church-encoded Nats are tries.}

% ✓ GOOD
\paragraph{Church-encoded Nats are tries}
```

### American spelling

Use **American English spelling** throughout reader-facing prose, and keep it **consistent across the whole paper** (consistency is the hard requirement; ACM does not mandate a variant, but a single paper must not mix them). Examples:

- `behavior` not `behaviour`, `behavioral` not `behavioural`
- `memoization` not `memoisation`, and the `-ize` / `-ization` family generally: `recognize`, `minimize`, `optimization`, `characterize`, `serialize`, `canonicalize`
- `labeled` / `labeling` not `labelled` / `labelling`, `neighbors` not `neighbours`

When unifying spelling, do **not** run a blind global `-ise → -ize` substitution. Instead replace an **explicit word list**, word-bounded and case-preserving. Two traps:

1. **Words spelled `-ise` in both variants stay unchanged**: `otherwise`, `comprise`, `exercise`, `surprise`, `arise`, `advertise`; and `-wise` suffixes (`pointwise`, `pairwise`, `levelwise`) are not `-ize` verbs.
2. **`analogue` stays** when it means "an analogue of": American usage keeps it there; `analog` skews to signals.

`references.bib` is **exempt**: cited titles must stay faithful to their originals, so never re-spell inside bibliography entries.

### Building the paper

The paper entry points are `preprint.tex` and `submission.tex`, which `\input` the shared body `inheritance-calculus.tex`. Build via:

```bash
cd inheritance-calculus && direnv exec . latexmk -pdf preprint.tex
```

Do **not** run `latexmk` directly on `inheritance-calculus.tex` — it is a fragment without a `\documentclass`.

## Adding TeXLive Packages

TeXLive packages are declared in `modules/texlive.nix`. Note that package names in nixpkgs may differ from CTAN names (e.g., `zi4` is `inconsolata`, `newtxmath` is `newtx`).

## Naming Conventions

- **Do not use single-letter variable names.** Use descriptive names that convey the purpose of the variable.
- **Do not use abbreviated or truncated English words** (e.g., `expr` for `expression`, `env` for `environment`, `val` for `value`). Write out the full word. The fact that an abbreviation is widely used in the industry does not justify its use here.
- **Exception:** established notations that are part of a fixed formal system are permitted, but these are limited to very few cases (e.g., `T` for a type variable in a typing judgment, `Γ` for a typing context). When in doubt, spell it out.
