import Mathlib
import InheritanceCalculus

/-!
# MIXINv2 Lean4 + Mathlib environment demo

A placeholder DEMO theorem that genuinely depends on Mathlib. Building this file
with `nix build .#mixinv2-lean-demo` exercises the whole Lean4 + Mathlib toolchain
wired up by `MIXINv2/modules/lean.nix`.
-/

-- Elevate the "declaration uses 'sorry'" warning to a hard error, so any `sorry`
-- in this file fails `lake build` / `nix build` instead of silently producing an
-- `.olean`.
set_option warningAsError true

/-- DEMO theorem: the square root of two is irrational.

`Irrational`, `Real.sqrt`, and the theorem `irrational_sqrt_two` all live in
Mathlib (not in Lean core or batteries), so a successful build certifies that
Mathlib is linked and usable. -/
theorem mixinv2_demo_irrational_sqrt_two : Irrational (Real.sqrt 2) :=
  irrational_sqrt_two

-- Strongest `sorry` check: `#print axioms` lists `sorryAx` whenever the proof
-- term (transitively) uses `sorry`. `#guard_msgs` asserts the axiom set is exactly
-- the standard ones, so a stray `sorry` anywhere in the dependency chain makes the
-- captured message mismatch and fails the build.
/-- info: 'mixinv2_demo_irrational_sqrt_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mixinv2_demo_irrational_sqrt_two
