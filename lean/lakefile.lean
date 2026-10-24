import Lake
open Lake DSL

-- Mirror Mathlib's own dependency-declaration form (scope + `@ git`). nixpkgs
-- `buildLakePackage` redirects this require to the prebuilt `leanPackages.mathlib`
-- in the Nix store via `lake build --packages=...`, so the git ref is never
-- actually fetched in the sandbox. A bare/Reservoir-scoped require would instead
-- trigger a Reservoir metadata lookup (a `curl` call) that fails offline.
require "leanprover-community" / "mathlib" @ git "v4.30.0"

package MixinV2Demo where

@[default_target]
lean_lib MixinV2Demo where

@[default_target]
lean_lib InheritanceCalculus where
