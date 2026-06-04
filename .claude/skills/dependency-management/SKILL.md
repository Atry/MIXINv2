---
name: dependency-management
description: "Managing Python dependencies in this Nix + uv2nix project: always direnv exec . uv add/remove/lock (never pip, never uv sync), why direnv exec . is required to reach the Nix-managed venv, and direnv reload to refresh a stale dev shell after uv.lock / flake.nix changes. Use when adding, removing, or updating dependencies, or when the environment seems stale."
---

# Dependency Management

This project uses Nix + uv2nix for Python dependency management. **Do not** use `pip`.

### Adding/Managing Dependencies

```bash
direnv exec . uv add <package>
direnv exec . uv remove <package>
direnv exec . uv lock
```

> **IMPORTANT:** Do NOT run `uv sync`. This project uses Nix-managed virtual environments, and `uv sync` will interfere with it. Use `uv lock` to update the lockfile only.

### Why `direnv exec .` is Required

The project creates a development environment via Nix flake, and `direnv` is responsible for activating it. Directly calling `uv` or `python` in Claude Code may not correctly access the Nix-managed virtual environment, so `direnv exec .` is needed to ensure commands run in the correct environment.

> **Warning:** After updating dependencies (including changes to `flake.nix` or Python packages), you must use `direnv exec .` to access the new virtual environment. Without it, you will get the old/stale environment and the changes will not be available.

### Refreshing the Nix Development Environment

When `uv.lock` or `flake.nix` changes, `direnv` may still use a cached (stale) Nix development shell. Run `direnv reload` to force `nix-direnv` to re-evaluate the flake and rebuild the virtual environment:

```bash
direnv reload
```

This is necessary when you see errors caused by stale packages (e.g., plugin conflicts from outdated dependency versions).
