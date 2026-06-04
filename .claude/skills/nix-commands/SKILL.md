---
name: nix-commands
description: "Running Nix commands in this project: always pass -L / --print-build-logs (e.g. nix build -L, nix develop -L, nix flake update -L) so build logs are shown for debugging. Use when invoking any nix command."
---

# Nix Commands

When running Nix commands (e.g., `nix build`, `nix develop`, `nix flake update`), always use `--print-build-logs` (or `-L`) to display build logs:

```bash
nix build --print-build-logs
nix develop -L
nix flake update --print-build-logs
```

This helps with debugging build failures and understanding what's happening during the build process.
