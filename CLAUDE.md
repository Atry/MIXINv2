## Domain-Specific Skills

Detailed, language- and domain-specific guidance has been split into auto-triggered
skills under `.claude/skills/`. They load on demand based on the task:

- **python-conventions** — Python coding style and dataclass/typing rules. Triggers when editing `.py` code.
- **mixinv2** — MIXINv2 language conventions (`.mixin.yaml`, FFI modules, references). Triggers on MIXINv2 work.
- **paper-writing** — LaTeX style, building the paper, TeXLive packages. Triggers when editing the paper.
- **dependency-management** — uv + direnv dependency management. Triggers when adding/updating dependencies.
- **nix-commands** — running Nix commands with `-L`. Triggers when invoking `nix`.
- **jupyter-debugging** — Jupyter Lab + jupyter MCP for interactive debugging. Triggers when debugging interactively.

The rules below apply to all work regardless of language or domain.

## Mindset: Assistant When Writing Prose, Agent When Writing Code

Adopt a different posture depending on what you are producing.

**When writing documentation or any prose** (papers, READMEs, docs, Markdown, LaTeX), act as an
**assistant**, not an autonomous agent:

- Discuss with the user often. Treat writing as a collaboration, not a task to finish unattended.
- Prefer open discussion over the question tool. Instead of firing `AskUserQuestion` with
  multiple-choice options, talk it through: offer concrete suggestions and recommendations in
  plain conversation and let the user steer.
- Always tell the user your own judgment. If you think something is wrong, weak, or over/under
  detailed, say so with reasons, rather than silently complying.
- Never mechanically transcribe the user's opinions that are not instructions. A statement of
  fact, framing, or preference is context to weigh, not a directive to copy into the artifact
  (and not a cue to add or delete content reflexively).
- Default the user's input to the author's perspective, not reader-facing copy. What the user
  tells you (a correction, a lesson, a framing, a piece of context) is by default a note for
  *you*: record it as a comment that reminds you how to write, not as text to drop into the body.
  Promoting any of it into the body is never automatic. It requires deliberate reasoning about
  narrative logic: what the reader needs at this point, in what order, and why this belongs in the
  prose rather than the margin. Only move something into the body once you have worked that out;
  otherwise it stays a comment. Dumping user input straight into the body is the failure mode this
  rule exists to prevent. (For the paper, the language and placement of these author-side notes are
  governed by the **paper-writing** skill, which is mandatory there.)
- No boilerplate, filler, or clichés. Every sentence must carry content.

**When writing code**, act as an **agent**, not an assistant: take ownership and drive the task
through to completion.

## Verify Before Agreeing

When the user corrects you or disputes a claim, do NOT open with "you're right" (or any
agreement) before you have checked the evidence. Affirming first and verifying second is
dishonest: at that moment you do not yet hold the evidence, and the subsequent "check" tends to
hunt for confirmation instead of testing the claim.

Required order:

1. Say you are going to verify (e.g. "let me check the source").
2. Read the relevant files / run the relevant commands.
3. Only then state the conclusion, with the evidence: "checked X; your correction holds
   because ..." or, equally, "checked X; the original text is actually correct because ...".

Agreement is only ever a *result* of verification, never an opener. If verification shows the
user is mistaken, say so directly with the evidence.

## Git Workflow

### Code Rollback Policy

**NEVER** use `git checkout` to discard changes or revert files. Always use **named `git stash`** instead.

**Why this rule exists:**
- `git checkout` permanently destroys uncommitted work with no recovery option
- Named stashes preserve the context and allow recovery if needed
- Stash names document why changes were saved, making it easier to find and restore work later
- This enforces a "safety first" approach where you can always undo mistakes

**Correct workflow for reverting changes:**

```bash
# ✗ FORBIDDEN - Never use git checkout to discard changes
git checkout mixinv2/src/mixinv2
git checkout .

# ✓ REQUIRED - Use named git stash with descriptive message
git stash push -m "refactoring: move _outer_mixin to StaticScope - testing if failure exists before refactor"

# Later, if you need to restore the stashed changes:
git stash list  # Find your stash
git stash apply stash@{0}  # Restore without removing from stash
git stash pop stash@{0}    # Restore and remove from stash
```

**Stash naming convention:**

Use descriptive names that explain:
1. What changes were stashed
2. Why they were stashed (e.g., testing, comparing, temporary work)

Examples:
- `"refactoring: testing original behavior before applying changes"`
- `"experiment: trying alternative implementation approach"`
- `"backup: preserving working state before major refactor"`
- `"debugging: isolating issue by reverting recent changes"`

**Viewing and managing stashes:**

```bash
# List all stashes with names
git stash list

# Show what's in a specific stash
git stash show stash@{0}
git stash show -p stash@{0}  # Show full diff

# Drop a stash when you're sure you don't need it
git stash drop stash@{0}

# Clear all stashes (use with caution)
git stash clear
```

**Exception:**

The only acceptable use of `git checkout` is for switching branches:

```bash
# ✓ ACCEPTABLE - Switching branches
git checkout main
git checkout -b feature-branch

# But prefer git switch for clarity:
git switch main
git switch -c feature-branch
```

## IMPORTANT: ⚔️ Offensive Programming

This project follows **Offensive Programming** principles: fail fast, fail loud, and let bugs crash the program immediately rather than hiding them. The goal is to make bugs impossible to ignore by crashing early with clear error messages.

1. **Crash on postcondition violations**: If function A calls function B, function A MUST `assert` every condition it relies on about B's return value (type/shape/non-empty/key presence/order, etc.). If the assertion fails, let the program crash—this exposes bugs in B immediately.
2. **Crash on invalid input**: Invalid external/user input MUST raise `ValueError("reason")` immediately. No sentinel returns, no fallback values—crash and tell the caller exactly what went wrong.
3. **No error recovery unless explicitly requested**: Do NOT add any `try/except` unless the user explicitly asks for it. Error recovery hides bugs and makes debugging harder.
4. **Let it crash**: Never use `try/except` to hide, swallow, or silence errors. If something fails, let the crash expose the root cause. Suppressing errors is the enemy of bug discovery.
5. **Ask before adding error handling**: If you believe an error is genuinely recoverable and a `try/except` handler is needed, STOP and ask the user for confirmation—do not add it autonomously.
6. **Self-explanatory code over comments**: Replace comments with self-documenting code using `logger.debug()` statements or extracting logic into well-named functions that explain the intent (e.g., `def perform_initialization(): ...` instead of `# perform initialization`).
7. **Crash on wrong assumptions**: NEVER use hardcoded indices like `my_sequence[0]`. If a sequence contains exactly one element, use unpacking syntax `single_item, = my_sequence` instead of indexing. This crashes immediately if the assumption is violated, exposing the bug.

**Why Offensive Programming?**
- Silent failures are worse than crashes—they corrupt data and hide bugs
- A crash with a stack trace tells you exactly where the bug is
- "Fail fast" means bugs are caught in development, not production
- Recovery code often masks the real problem and introduces new bugs

Do NOT write redundant asserts for facts already guaranteed by parameter or return type annotations (e.g. avoid `assert isinstance(count, int)` when the signature declares `count: int`). Focus asserts on semantic invariants not encoded in the static types (non-empty, ordering, relationships between values, normalized ranges, cross-field consistency, etc.).

Examples:

```python
def fetch_profile(repo, user_id: str):
    # Crash immediately if user_id is invalid—don't return None or a default
    if not user_id:
        raise ValueError("user_id must be non-empty")
    profile = repo.get(user_id)
    # Crash if repo.get violates its contract—expose the bug in repo
    assert profile is not None, "repo.get must return a profile object"
    assert profile.id == user_id, f"Expected id {user_id}, got {profile.id}"
    return profile

def process_results(results: list[str]):
    # ✅ CORRECT: Unpacking crashes if assumption is wrong—bug exposed immediately
    single_result, = results
    return single_result.upper()

    # ❌ WRONG: Hardcoded index silently succeeds with multiple elements—bug hidden
    # return results[0].upper()

# ❌ FORBIDDEN (suppresses root cause, hides bugs):
# try:
#     data = parse(raw)
# except Exception:
#     data = None  # Bug is now invisible—NEVER do this
```

Use `assert` for internal invariants about trusted code paths; use `ValueError` for invalid caller/user inputs. Let the program crash—crashes are your friend in finding bugs.

### Exceptions with Special Semantics

Some Python exceptions have **special meanings** tied to specific dunder methods or protocols. These exceptions MUST NOT propagate through unrelated methods—they must be caught and converted to appropriate exceptions.

| Exception        | Semantic Owner                                 | Why It's Special                                     |
| ---------------- | ---------------------------------------------- | ---------------------------------------------------- |
| `KeyError`       | `__getitem__`, `__delitem__`                   | Caught by `__contains__`, signals "key not found"    |
| `IndexError`     | `__getitem__` (sequences)                      | Terminates `for` loops, signals "index out of range" |
| `StopIteration`  | `__next__`                                     | Terminates `for` loops, signals iterator exhaustion  |
| `AttributeError` | `__getattr__`, `__getattribute__`, descriptors | Caught by `hasattr()`, `getattr()` with default      |
| `GeneratorExit`  | Generators                                     | Special generator lifecycle, should not escape       |

**Why this matters:**

These exceptions are caught by Python's runtime in specific contexts:
- `hasattr(obj, 'x')` catches `AttributeError` → wrong escape causes incorrect `hasattr()` results
- `for x in seq` catches `IndexError`/`StopIteration` → wrong escape terminates loops early
- `x in mapping` may catch `KeyError` → wrong escape causes incorrect containment checks

**Example: KeyError**

```python
# ✗ BAD - KeyError escaping from non-__getitem__ method
def resolve_path(self, path: tuple[str, ...]) -> Symbol:
    current = self
    for part in path:
        current = current[part]  # KeyError escapes if part not found
    return current

# ✓ GOOD - Use .get() and raise descriptive error
def resolve_path(self, path: tuple[str, ...]) -> Symbol:
    current = self
    for part in path:
        child = current.get(part)
        if child is None:
            raise ValueError(
                f"Cannot navigate path {path!r}: '{current.key}' has no child '{part}'"
            )
        current = child
    return current
```

**Example: AttributeError**

```python
# ✗ BAD - AttributeError escaping from property (breaks hasattr)
@property
def config(self) -> Config:
    return self.parent.settings  # AttributeError if parent has no settings
    # hasattr(obj, 'config') now returns False incorrectly!

# ✓ GOOD - Convert to descriptive error
@property
def config(self) -> Config:
    parent = self.parent
    if not hasattr(parent, 'settings'):
        raise ValueError(f"Parent {parent!r} has no settings")
    return parent.settings
```

**Example: StopIteration**

```python
# ✗ BAD - StopIteration escaping from non-iterator (Python 3.7+ converts to RuntimeError)
def get_first(items: Iterable[T]) -> T:
    return next(iter(items))  # StopIteration if empty

# ✓ GOOD - Handle explicitly
def get_first(items: Iterable[T]) -> T:
    iterator = iter(items)
    try:
        return next(iterator)
    except StopIteration:
        raise ValueError("Cannot get first item: iterable is empty") from None
```

**Rule:** If you call code that may raise these special exceptions, you MUST either:
1. Use safe alternatives (`.get()`, `hasattr()`, `next(iter, default)`)
2. Catch and convert to an appropriate exception with context


## Handling Test Failures After Code Changes

When code modifications cause tests to fail, consider **three possible scenarios** before making any changes:

### 1. Tests Need to Be Updated

The test expectations are outdated and need to reflect the new, correct behavior.

**When this applies:**
- The code change was intentional and the new behavior is correct
- The test was written for the old behavior that is no longer valid
- The test assertions need to match the new expected output

**Action:** Update the test to reflect the new behavior.

### 2. Source Code Has a Trivial Bug

There's a simple, obvious bug in the source code that can be fixed without changing the design.

**When this applies:**
- The fix is a typo, missing import, or obvious logic error
- The fix does not change the intended behavior or design
- The fix is unambiguous and doesn't require design decisions

**Action:** Fix the trivial bug in the source code.

### 3. Source Code Design Conflicts with Test Assumptions

The source code's design and the test's assumptions are fundamentally incompatible.

**When this applies:**
- Fixing the test failure would require changing the source code's behavior
- The "fix" would involve adding workarounds, special cases, or design changes
- You are uncertain whether the source code or the test is "correct"

**Action:** **STOP and ask the user.** Do NOT autonomously modify source code behavior.

### 🎉 Discovering Design Conflicts is Valuable

When tests fail and reveal a conflict between source code design and test assumptions, **this is a good thing**. It proves the value of tests:

- Tests caught a real design issue that would otherwise go unnoticed
- The conflict forces explicit design decisions rather than implicit assumptions
- This is exactly what tests are for: exposing problems early

**Do NOT view this as an obstacle to overcome.** View it as valuable information that requires human judgment.

### ☠️ Autonomous Workarounds Are Extremely Harmful

Adding workarounds **without user confirmation** to make tests pass is **catastrophically bad**:

- Workarounds hide the real problem instead of solving it
- They introduce behavior changes outside of the planned design
- They create technical debt that compounds over time
- They break the trust relationship between tests and implementation
- A passing test suite becomes meaningless if tests pass due to workarounds

**Examples of forbidden autonomous workarounds:**
- Adding method overrides (like `__contains__`) just to make tests pass
- Adding special case handling for specific test scenarios
- Modifying return values to match test expectations without understanding why
- Catching and suppressing exceptions that tests don't expect

**Workarounds are acceptable ONLY when explicitly requested by the user.** The user may have valid reasons to accept a workaround as a temporary or permanent solution. But this decision belongs to the user, not to the assistant.

**The correct response to a design conflict is ALWAYS to stop and ask.**

### ⚠️ Critical Rule

**Source code behavior changes MUST only come from:**
1. The original plan approved by the user
2. Explicit user requests

**Source code behavior changes MUST NEVER come from:**
- Attempts to make tests pass
- Assumptions about what the "correct" behavior should be

If you cannot fix a test failure through trivial bug fixes or test updates, you MUST ask the user for guidance. Do NOT add workarounds, override methods, or change behavior just to make tests pass.

```python
# ✗ FORBIDDEN - Adding __contains__ override just to fix a test
def __contains__(self, key: object) -> bool:
    # This changes the class's behavior beyond the original plan
    return any(k == key for k in self)

# ✗ FORBIDDEN - Adding special case handling to pass tests
if isinstance(result, SyntheticSymbol):
    # Workaround to make test pass - violates design
    result = create_workaround_symbol()

# ✓ CORRECT - Ask the user when design conflicts with tests
# "The test expects X but the code does Y. Should I:
#  (a) Update the test to expect Y, or
#  (b) Change the code design to produce X?"
```

## Logging Best Practices

### Use `logging`, NOT `print`

**Do NOT** use `print()` for output in application code. Use `logging` instead:

### Adding Debug Logs

Use `%(funcName)s` in the log format to automatically include function names. Do not manually prefix log messages with function names.

Use named placeholders instead of positional arguments for better readability:

```python
# Good - named placeholders
logger.debug("bytes=%(bytes)d preview=%(preview)r", {"bytes": len(data), "preview": data[:100]})

# Bad - positional arguments
logger.debug("read returned %d bytes: %r", len(data), data[:100])

# Bad - redundant manual prefix
logger.debug("[read] read returned %d bytes: %r", len(data), data[:100])
```

## Snapshot Testing with Syrupy

1. Do not assert variables against hard-coded literal constants directly; instead assert them against a Syrupy snapshot and always supply an explicit snapshot name via name="<descriptive_name>" to keep snapshots readable.
2. When a Syrupy snapshot assertion fails, first re-run the test suite with --snapshot-update to regenerate the snapshot, then you MUST review the updated snapshot contents to confirm they match the intended change, then re-run the tests without --snapshot-update to ensure the updated snapshot passes reproducibly.
3. Do not use a snapshot when comparing a value to another variable produced within the same test (variable-to-variable logic) or when asserting a trivially obvious outcome such as a boolean success flag that should simply be True.

```python
from syrupy.assertion import SnapshotAssertion

def test_compute(snapshot: SnapshotAssertion):
	result = expensive_or_complex_compute()
	# Instead of: assert result == {"status": "ok", "value": 3}
	assert result == snapshot(name="compute_result")
```


## Documentation Writing Style

### No dashes in prose

**Do NOT** use dashes as punctuation in documentation prose (Markdown and the English inside LaTeX). This covers the em dash (`—`), punctuation en dashes (`–`), and the double-hyphen (`--`). Use a comma, colon, parentheses, or split into two sentences instead. Hyphens in compound words (`Church-encoded`) and numeric ranges (`pages 10–20`) are fine. Use a dash only when the user explicitly asks; never introduce one autonomously.

