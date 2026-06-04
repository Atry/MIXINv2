---
name: paper-writing
description: "LaTeX style and conventions for the inheritance-calculus / first-order paper: section/subsection Title Case, paragraph sentence case with no trailing period, how to build the paper (latexmk on preprint.tex / submission.tex, not the shared body fragment), adding TeXLive packages in modules/texlive.nix, and paper variable-naming rules (no single-letter or abbreviated names except fixed formal notation). Use when editing the paper's .tex files, building the PDF, or adding LaTeX packages."
---

# Paper Writing (inheritance-calculus / first-order paper)

## LaTeX Style (inheritance-calculus paper)

### Heading capitalization

- `\section` and `\subsection`: **Title Case** (capitalize all major words; lowercase articles, prepositions, and conjunctions unless they are the first word).
- `\paragraph`: **Sentence case** (capitalize only the first word and proper nouns).

### No trailing periods in headings

`\paragraph` headings must **not** end with a period:

```latex
% ✗ BAD
\paragraph{Church-encoded Nats are tries.}

% ✓ GOOD
\paragraph{Church-encoded Nats are tries}
```

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
