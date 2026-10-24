{ ... }: {
  # Build the Lean4 + Mathlib demo (MIXINv2/lean) as a Nix artifact, mirroring the
  # module shape of python.nix / texlive.nix: a flake-parts perSystem module that
  # exposes `packages.*`. The monorepo surfaces it via modules/artifacts.nix.
  #
  # Lean and Mathlib come straight from nixpkgs `leanPackages` (the native
  # `buildLakePackage` + prebuilt `mathlib`, added in nixpkgs PR #497946), so no
  # extra flake input or lean4-nix overlay is needed and Mathlib's `.olean` tree is
  # fetched from the binary cache rather than recompiled locally.
  config.perSystem = { pkgs, ... }: {
    packages.mixinv2-lean-demo = pkgs.leanPackages.buildLakePackage {
      pname = "mixinv2-lean-demo";
      version = "0.1.0";
      src = ../lean;

      # Must match the package/lean_lib name declared in lean/lakefile.toml.
      leanPackageName = "MixinV2Demo";

      # Inject prebuilt Mathlib; buildLakePackage wires it into LEAN_PATH and
      # redirects the lakefile's `require mathlib` to the Nix store path via
      # `lake build --packages=...`. This requires the source to ship an empty
      # `lake/lake-manifest.json`, otherwise Lake tries to materialize the require
      # from Reservoir (a network `curl`) and fails in the sandbox. See the
      # nixpkgs `weak-minimax` test for the same pattern.
      leanDeps = [ pkgs.leanPackages.mathlib ];
    };
  };
}
