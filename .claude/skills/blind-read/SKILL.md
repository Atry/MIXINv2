---
name: blind-read
description: "Verify that a piece of prose (a paper introduction/abstract, README, doc, or any explanation) is understandable to a reader with no background, by handing the text to fresh context-free subagents that read ONLY that text, restate it, and list every confusion, then iterating until a fresh subagent understands it. Use to combat the curse of knowledge when you wrote (or read source material for) the very text you are checking, or whenever the user asks to blind-read / 盲读 / check that writing is clear to a newcomer."
---

# Blind Read

A fresh reader with no background exposes the leaps you wrote unconsciously (the curse of
knowledge). Run that reader as a subagent and loop until the text stands on its own.

## Two hard rules

1. **Reviewer sees only what a real reader would have seen by this point, and never your intent.**
   For a standalone piece that is the TARGET text alone. For a section read in sequence, it is the
   TARGET plus the earlier sections as CONTEXT (see below) — but never the *later* sections, the
   codebase, the prior chat, or any explanation of what you *meant*. If the meaning is not on the
   page (TARGET, resolved against CONTEXT at most), the test must show it.
2. **A brand-new subagent each round.** One that saw a prior round is spoiled.

## CONTEXT vs TARGET: testing a section read in sequence

A reader of Section 3 has already read Sections 1–2. Handing the reviewer Section 3 *alone* then
manufactures **false confusions**: every term the earlier sections defined ("the solver", "rational",
a symbol) gets flagged, drowning the genuine leaps. To test a later section faithfully, split the
input into two layers:

- **CONTEXT** — everything a linear reader has already read before the TARGET (the prior sections).
  The reviewer may use it freely to resolve any reference. It is *not* under test.
- **TARGET** — the section you are evaluating now. All confusions, obvious-cuts, and the verdict
  are about the TARGET only.

A confusion counts only if it survives the TARGET *and* the CONTEXT combined: a term the CONTEXT
already defined is not a confusion. This keeps the signal on what the TARGET itself fails to carry.
The first section of a document (abstract, intro) has no CONTEXT and is tested as a standalone
TARGET. The ban in hard rule 1 still holds for everything else: never include later sections, the
codebase, or your intent — those are exactly the curse-of-knowledge channels the test exists to close.

## Loop

1. Extract the exact prose into a **unique** throwaway temp file, one per round, so rounds never
   collide and a fresh subagent can't read a stale or parallel version. Get the path with
   `mktemp /tmp/blind-read.XXXXXX.txt`, then fill it. **Strip author-side comments first** so the
   subagent sees only what a real reader sees: pipe the slice through `strip-comments.py` (next to
   this skill), e.g. `sed -n '100,160p' src.tex | python3 .claude/skills/blind-read/strip-comments.py --style latex > "$f"`.
   The TARGET file must hold ONLY the prose under test, nothing from later in the document. When
   the prose is a section read in sequence, also write a separate **CONTEXT** file with the earlier
   sections (e.g. `sed -n '1,99p' src.tex | python3 .claude/skills/blind-read/strip-comments.py --style latex > "$ctx"`)
   and pass both paths; for a standalone or first section, pass the TARGET alone. State the assumed
   audience (e.g. "general CS reader, no coalgebra").
   Passing paths, not pasted text, keeps the full prose out of the parent context every round.
2. Spawn one fresh `Agent` (Explore / general-purpose) with the prompt below (the standalone prompt,
   or the CONTEXT/TARGET prompt when you split the input).
3. Compare its restatement to your intent; note every flagged confusion.
4. **Fix the text in place**, in both directions: add what is missing (gloss jargon on first
   use, a plain-language bridge, replace notation with words) *and* cut what the audience already
   knows (over-narrated obvious steps read as filler). Do not answer the subagent; change the prose.
   **Preserve narrative flow:** clarify in the fewest words possible; if an inline clarification
   would break the main line, move it to a footnote instead of bloating the body.
5. Repeat with a new subagent.

**Pass only when** one fresh subagent restates the claim, each example, and the takeaway
matching your intent, with an empty confusion list. If you must excuse a gap ("they'd get it
if they knew X"), that excuse is the curse of knowledge: fix and rerun.

## Common curses (flag these)

- **Forward reference** to a concept/section/result used before it is introduced.
- **Undefined term or jargon**; **unexplained symbol/notation**; **unexpanded acronym** on first use.
- **Assumed prior knowledge** ("it is well known", folklore, a cited result's content the reader lacks).
- **Suppressed step** behind "clearly / obviously / it follows / trivially".
- **Missing why**: states what happens but not the motivation or why it matters.
- **Dangling referent**: "this / that / it" with no clear antecedent.
- **Overloaded name**: one symbol or word for two things in the same passage.
- **Inconsistent terminology**: one concept, multiple names, never equated.
- **Untyped thing**: unclear what something *is* (a function? a set? a value? a step?).
- **Insider comparison** to an alternative the reader does not know ("unlike call-by-need ...").
- **Unreachable pointer**: "see the code / the figure" the reader cannot consult.
- **Self-loading example**: the illustration needs the very concept being introduced.
- **Definite article on first mention**: "*the* interpreter / *the* structure map" for something
  not yet introduced, presupposing the reader already knows it (use "a ..." or introduce it first).
- **Over-narration of the obvious** (the inverse curse): spelling out in ten sentences what the
  audience can infer from one. The reader fills gaps as well as you do; obvious steps read as
  filler. Separate obvious from non-obvious, keep the non-obvious, cut the obvious.
- **Parenthesis overuse**: a parenthetical aside that interrupts the main line, or defensive
  clarifying content crammed into parentheses. Flag it; the fix is either to weave it into the
  sentence or to move it to a footnote.

## Subagent prompt

### Standalone (no CONTEXT)

```
You are a first-time reader. Background: <AUDIENCE>. Read ONLY the file <PATH> and nothing else:
do not open any other file, search the repo, or infer from outside knowledge or look anything up.
Report: 1. RESTATEMENT (plain words: main claim, each example and why it supports the claim,
the takeaway). 2. CONFUSIONS (numbered: every term/symbol/step you can't follow from the text
alone; quote it, say what's missing). Watch for: forward references, undefined terms/notation/
acronyms, assumed prior knowledge, suppressed steps ("clearly"), missing motivation, unclear
"this/it", overloaded names, inconsistent terminology (one concept under multiple names, never
equated), untyped things, comparisons to things you don't know, pointers you can't follow,
examples needing the concept itself, "the X" for an X not yet introduced, parenthesis overuse
(defensive or clarifying content crammed into parentheses that breaks the sentence's flow).
3. OBVIOUS (numbered: passages a reader of this background already knows, that spell out the
inferable and could be cut; quote them). 4. VERDICT (yes/no a reader of that background
understands). Be literal, not charitable: anything only guessable is a confusion, and anything
you already knew before reading is obvious.
```

### CONTEXT/TARGET (section read in sequence)

```
You are a first-time reader of a document, reading it in order. Background: <AUDIENCE>. You will
read TWO files and nothing else (do not open any other file, search the repo, or look anything up):
- CONTEXT (already read; use it freely to resolve any reference, NOT under test): <CONTEXT_PATH>
- TARGET (the part you are evaluating now): <TARGET_PATH>
Report ONLY about the TARGET. Report a CONFUSION only if it survives the TARGET *and* the CONTEXT
combined: if the CONTEXT already defines a term/symbol, it is NOT a confusion.
1. RESTATEMENT (plain words: main claim of the TARGET, each example and why it supports the claim,
the takeaway). 2. CONFUSIONS (numbered: every term/symbol/step in the TARGET you can't follow even
after using the CONTEXT; quote it, say what's missing). Watch for: undefined terms/notation/acronyms,
suppressed steps ("clearly"), missing motivation, unclear "this/it", overloaded names, untyped
things, inconsistent terminology (one concept under multiple names across CONTEXT and TARGET,
never equated), comparisons to things you don't know, pointers you can't follow, examples needing
the concept itself, "the X" for an X introduced in neither file, parenthesis overuse (defensive or
clarifying content crammed into parentheses that breaks the sentence's flow). Note a forward reference to a *later*
part you were not given only if it blocks understanding the TARGET itself. 3. OBVIOUS (numbered:
passages a reader of this background, having read the CONTEXT, already knows and that could be cut;
quote them). 4. VERDICT (yes/no a reader of that background, having read the CONTEXT, understands
the TARGET). Be literal, not charitable about the TARGET, but DO use the CONTEXT to resolve
references: anything only guessable from the two files is a confusion, anything you already knew is obvious.
```

## Notes

- **Always strip comments before a subagent reads the prose** (`strip-comments.py`, used in step 1).
  Author-side notes (LaTeX `%` comments, which in this project are Chinese margin notes recording the
  author's intent and reasoning, and HTML/Markdown `<!-- ... -->` comments) are exactly the
  curse-of-knowledge channel hard rule 1 forbids: a reader never sees them, so neither may the
  reviewer. The script removes them; run `python3 .claude/skills/blind-read/strip-comments.py --help`
  for usage and `--style {latex,html}` / auto-detection details.
- Run rounds serially (each fix changes what the next reader sees); keep the audience fixed.
- **One subagent per round; skip the round if the change is trivial.** Re-run only after a real
  edit to the prose — a trivial change (fixing a typo, adjusting punctuation) does not justify a
  new round; re-run when a confusion was addressed or a passage was rewritten. Multiple subagents
  on the same unchanged text add no new signal.
- Checks comprehensibility only, not correctness or style.
