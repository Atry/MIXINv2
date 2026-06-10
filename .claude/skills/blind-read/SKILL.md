---
name: blind-read
description: "Verify that a piece of prose (a paper introduction/abstract, README, doc, or any explanation) is understandable to a reader with no background, by handing the text to fresh context-free subagents that read ONLY that text, restate it, and list every confusion, then iterating until a fresh subagent understands it. Use to combat the curse of knowledge when you wrote (or read source material for) the very text you are checking, or whenever the user asks to blind-read / 盲读 / check that writing is clear to a newcomer."
---

# Blind Read

A fresh reader with no background exposes the leaps you wrote unconsciously (the curse of
knowledge). Run that reader as a subagent and loop until the text stands on its own.

## Two hard rules

1. **Reviewer gets ONLY the target text.** No rest of the paper, no codebase, no prior chat,
   and never tell it what you *meant*. If the meaning is not on the page, the test must show it.
2. **A brand-new subagent each round.** One that saw a prior round is spoiled.

## Loop

1. Extract the exact prose into a **unique** throwaway temp file, one per round, so rounds never
   collide and a fresh subagent can't read a stale or parallel version. Get the path with
   `mktemp /tmp/blind-read.XXXXXX.txt`, then fill it (e.g. `sed -n '100,160p' src.tex > "$f"`).
   The file must hold ONLY the target prose, nothing from the rest of the document. State the
   assumed audience (e.g. "general CS reader, no coalgebra"). Passing a path, not the pasted
   text, keeps the full prose out of the parent context every round.
2. Spawn one fresh `Agent` (Explore / general-purpose) with the prompt below.
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
- **Untyped thing**: unclear what something *is* (a function? a set? a value? a step?).
- **Insider comparison** to an alternative the reader does not know ("unlike call-by-need ...").
- **Unreachable pointer**: "see the code / the figure" the reader cannot consult.
- **Self-loading example**: the illustration needs the very concept being introduced.
- **Definite article on first mention**: "*the* interpreter / *the* structure map" for something
  not yet introduced, presupposing the reader already knows it (use "a ..." or introduce it first).
- **Over-narration of the obvious** (the inverse curse): spelling out in ten sentences what the
  audience can infer from one. The reader fills gaps as well as you do; obvious steps read as
  filler. Separate obvious from non-obvious, keep the non-obvious, cut the obvious.

## Subagent prompt

```
You are a first-time reader. Background: <AUDIENCE>. Read ONLY the file <PATH> and nothing else:
do not open any other file, search the repo, or infer from outside knowledge or look anything up.
Report: 1. RESTATEMENT (plain words: main claim, each example and why it supports the claim,
the takeaway). 2. CONFUSIONS (numbered: every term/symbol/step you can't follow from the text
alone; quote it, say what's missing). Watch for: forward references, undefined terms/notation/
acronyms, assumed prior knowledge, suppressed steps ("clearly"), missing motivation, unclear
"this/it", overloaded names, untyped things, comparisons to things you don't know, pointers you
can't follow, examples needing the concept itself, "the X" for an X not yet introduced.
3. OBVIOUS (numbered: passages a reader of this background already knows, that spell out the
inferable and could be cut; quote them). 4. VERDICT (yes/no a reader of that background
understands). Be literal, not charitable: anything only guessable is a confusion, and anything
you already knew before reading is obvious.
```

## Notes

- Run rounds serially (each fix changes what the next reader sees); keep the audience fixed.
- Checks comprehensibility only, not correctness or style.
