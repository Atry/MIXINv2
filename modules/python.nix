{ inputs, flake-parts-lib, ... }: {
  # Expose the reusable uv2nix build-system overrides as a per-system option so the
  # monorepo development environment composes the same package fixes into its editable
  # virtualenv. This subrepo only produces the build artifacts (supplementary material);
  # the editable dev env and dev shell live in the monorepo.
  options.perSystem = flake-parts-lib.mkPerSystemOption ({ lib, ... }: {
    options.mixinv2PyprojectOverrides = lib.mkOption {
      type = lib.types.raw;
      description = "Reusable uv2nix overlay (final: prev: {...}) of MIXINv2's build-system fixes.";
    };
  });
  config.perSystem = { config, pkgs, lib, system, ... }:
    let
      workspace =
        inputs.uv2nix.lib.workspace.loadWorkspace { workspaceRoot = ../.; };

      # Reusable, repo-agnostic build-system fixes (exposed via the option above).
      genericPyprojectOverrides = final: prev: {
        pyflyby = prev.pyflyby.overrideAttrs (old: {
          nativeBuildInputs = old.nativeBuildInputs
            ++ final.resolveBuildSystem { meson-python = [ ]; pybind11 = [ ]; };
          propagatedBuildInputs = (old.buildInputs or [ ]) ++ [ pkgs.ninja ];
        });
        uv-dynamic-versioning = prev.uv-dynamic-versioning.overrideAttrs (old: {
          nativeBuildInputs = old.nativeBuildInputs
            ++ final.resolveBuildSystem { hatchling = [ ]; };
        });
      };

      # Repo-specific: the virtual workspace-root package has no sources to install.
      localOverrides = final: prev: {
        mixinv2-workspace = prev.mixinv2-workspace.overrideAttrs (_: {
          buildPhase = "mkdir -p $out";
          installPhase = "true";
          nativeBuildInputs = [ ];
        });
      };

      python = pkgs.python313;

      pythonSet = (pkgs.callPackage inputs.pyproject-nix.build.packages {
        inherit python;
      }).overrideScope (lib.composeManyExtensions [
        inputs.pyproject-build-systems.overlays.wheel
        (workspace.mkPyprojectOverlay {
          sourcePreference = "wheel";
          dependencies = workspace.deps.default;
        })
        (inputs.uv2nix_hammer_overrides.overrides pkgs)
        genericPyprojectOverrides
        localOverrides
      ]);

      # --- Supplementary material for double-blind review ---

      # Identity anonymization shared by every supplementary bundle. The from/to pairs are
      # rendered into substituteInPlace arguments; the leak check fails the build if any
      # de-anonymized identity survives.
      identityReplacements = [
        { from = "yang-bo@yang-bo.com"; to = "anonymous@example.com"; }
        { from = "Yang, Bo"; to = "Anonymous, Author"; }
        { from = "Bo Yang"; to = "Anonymous Author"; }
        { from = "Figure AI Inc."; to = "Anonymous Institution"; }
        { from = "Figure AI"; to = "Anonymous Institution"; }
        {
          from = "github.com/Atry/MIXINv2";
          to = "github.com/anonymous-author/anonymous-repo";
        }
      ];

      mkReplaceArgs = replacements:
        lib.concatMapStringsSep " "
        (replacement: "--replace-warn '${replacement.from}' '${replacement.to}'")
        replacements;

      assertNoIdentityLeak = dir: ''
        for identityNeedle in "Bo Yang" "yang-bo" "Figure AI"; do
          if grep -rli "$identityNeedle" ${dir}; then
            echo "FAIL: identity leak '$identityNeedle'" >&2; exit 1
          fi
        done
        if grep -rl "Atry" ${dir}; then
          echo "FAIL: identity leak 'Atry'" >&2; exit 1
        fi
      '';

      # Positive check that anonymization ran: the author line 'Yang, Bo' becomes
      # 'Anonymous, Author', which every bundle's package metadata carries.
      assertAnonymized = dir: ''
        grep -rl "Anonymous, Author" ${dir} > /dev/null
      '';

      sphinxEnv = (pythonSet.mkVirtualEnv "sphinx-env"
        (builtins.removeAttrs workspace.deps.all
          [ "mixinv2-workspace" ])).overrideAttrs
        (old: { venvIgnoreCollisions = [ "*" ]; });

      supplementarySourceFiles = lib.fileset.toSource {
        root = ../.;
        fileset = lib.fileset.unions [
          ../packages/mixinv2/src
          ../packages/mixinv2/pyproject.toml
          ../packages/mixinv2/README.md
          ../packages/mixinv2/docs
          ../packages/mixinv2-library/src
          ../packages/mixinv2-library/pyproject.toml
          ../packages/mixinv2-examples/src
          ../packages/mixinv2-examples/pyproject.toml
          ../packages/mixinv2-examples/tests
          ../packages/mixinv2-library/tests
          ../packages/mixinv2/tests
          ../mixinv2.schema.json
          ../pyproject.toml
          ../uv.lock
          ../LICENSE
          ../README.md
        ];
      };

      reviewerReadme = pkgs.writeText "README.md" ''
        # MIXINv2 — Supplementary Material

        This archive contains the source code and tests for MIXINv2, the reference
        implementation of inheritance-calculus.

        ## Directory Structure

        - `docs` — Built HTML documentation
        - `ratarmount/` — Union file system implementation (Section 5.2)
        - `packages/mixinv2/src/mixinv2/` — Python implementation of the MIXINv2 runtime
        - `packages/mixinv2-library/src/mixinv2_library/Builtin/` — Standard library (`.mixin.yaml` files):
          Boolean logic, Nat arithmetic, BinNat arithmetic, visitors, equality
        - `packages/mixinv2-examples/` — Example case studies (Fibonacci, function color blindness, DI)
        - `tests/` — Test suite (see below)

        ## Paper Examples in the Test Suite

        The case study examples from the paper are implemented as `.mixin.yaml` files
        and exercised by `pytest` tests:

        | Paper section | `.mixin.yaml` file(s) | Test file |
        |---|---|---|
        | Case Study: Nat arithmetic | `packages/mixinv2-library/.../NatData.mixin.yaml`, `NatPlus.mixin.yaml`, `NatEquality.mixin.yaml`, `NatVisitor.mixin.yaml`, `NatDecrement.mixin.yaml`, `tests/NatConstants.mixin.yaml`, `tests/ArithmeticTest.mixin.yaml` | `tests/test_nat_arithmetic.py` |
        | Case Study: BinNat arithmetic | `packages/mixinv2-library/.../BinNat*.mixin.yaml`, `tests/BinNatArithmeticTest.mixin.yaml` | `tests/test_bin_nat_arithmetic.py` |
        | Case Study: Cartesian product (relational semantics) | `tests/CartesianProductTest.mixin.yaml` | `tests/test_cartesian_product.py` |
        | Boolean logic | `packages/mixinv2-library/.../Boolean*.mixin.yaml`, `tests/ChurchBooleanTest.mixin.yaml` | `tests/test_church_boolean.py` |
        | Fibonacci | `packages/mixinv2-examples/tests/fixtures/FibonacciTest.mixin.yaml`, `packages/mixinv2-examples/src/mixinv2_examples/FibonacciLibrary.mixin.yaml` | `packages/mixinv2-examples/tests/test_fibonacci.py` |
        | Function color blindness | `packages/mixinv2-examples/src/mixinv2_examples/app_mixin/` | `tests/test_stdlib_python_port.py` |
        | Expression Problem | Composition of separate `.mixin.yaml` files without modification | `tests/test_nat_arithmetic.py`, `tests/test_bin_nat_arithmetic.py` |

        ## Running Tests

        Requires Python >= 3.11 and [uv](https://docs.astral.sh/uv/).

        ```
        uv sync
        uv run pytest tests/ packages/mixinv2-examples/tests/
        ```

        ## Running Examples

        After installation (see above), start the stdlib HTTP server demo:

        ```
        uv run mixinv2-example app_mixin Apps memory_app serve_forever
        ```

        Or start the async (uvicorn/starlette) HTTP server demo:

        ```
        uv run mixinv2-example app_mixin AsyncApps memory_app serve_forever
        ```

        The server listens on `http://127.0.0.1:<port>` (port is auto-assigned).
        Press Ctrl-C to stop.

        The `mixinv2-example` command evaluates the MIXINv2 examples package and
        navigates the scope tree along the given path.
      '';

      ratarmountSource = inputs.ratarmount;

      ratarmountPreamble = pkgs.writeText "ratarmount-preamble.md" ''
        > **Note:** This directory contains a patched version of
        > [ratarmount](https://github.com/mxmlnkn/ratarmount) that adds a
        > `--resolve-symbolic-links` flag.  This flag enables late-binding
        > symbolic link resolution within union mounts, the mechanism
        > described in Section 5.2 of the paper (Union file systems).
        >
        > **What the patch adds:**
        >
        > **`link.py`** implements a new compositing layer with two internal
        > abstractions:
        >
        > - **`_FileVersion`** — binds an underlying `MountSource` path to a
        >   union path and stores a physical parent chain for resolving
        >   relative links containing `..`.  This is analogous to lexical
        >   scoping: the meaning of `..` is tied to the link's static
        >   location in the underlying hierarchy rather than the access path
        >   in the merged tree.
        >
        > - **`_UnionPath`** — represents a path in the merged view that may
        >   correspond to multiple `_FileVersion`s.  It provides direct and
        >   transitive link expansion with deduplication to avoid cycles, and
        >   a child-lookup strategy analogous to dynamic dispatch: children
        >   are discovered by searching across all resolved folder versions.
        >
        > When enabled, symlink and hardlink targets are resolved **within the
        > union view**, not constrained to the original source.  This provides
        > the late-binding semantics for layered trees described in the paper.
        >
        > **`MultiMountSourceMixin`** (in `multi.py`) refactors common
        > multi-source patterns out of `UnionMountSource`, centralizing the
        > userdata delegation protocol and merged `statfs` handling.

      '';

      supplementaryMaterial = pkgs.stdenv.mkDerivation {
        name = "supplementary-material.zip";
        src = supplementarySourceFiles;
        nativeBuildInputs = [ pkgs.zip pkgs.unzip sphinxEnv ];

        buildPhase = ''
          cd ..
          mv source supplementary-material
          cd supplementary-material

          # Include ratarmount pull request source
          cp -r ${ratarmountSource} ratarmount
          chmod -R u+w ratarmount
          cat ${ratarmountPreamble} ratarmount/README.md > ratarmount/README.md.tmp
          mv ratarmount/README.md.tmp ratarmount/README.md

          # Replace README with reviewer-oriented version
          cp ${reviewerReadme} README.md

          # Anonymize all text files
          shopt -s globstar nullglob
          substituteInPlace \
            **/*.py **/*.toml **/*.lock **/*.json **/*.md **/*.rst \
            **/*.cfg **/*.txt **/*.yaml **/*.yml **/*.ini \
            ${mkReplaceArgs identityReplacements} \
            --replace-warn 'github.com/Atry/overlay' 'github.com/anonymous-author/anonymous-repo' \
            --replace-warn 'github.com/Atry/MIXIN' 'github.com/anonymous-author/anonymous-repo' \
            --replace-warn "'Atry'" "'anonymous-author'" \
            --replace-warn '"Atry"' '"anonymous-author"' \
            --replace-warn '`inheritance-calculus <https://arxiv.org/abs/2602.16291>`_' 'inheritance-calculus' \
            --replace-warn '[inheritance-calculus](https://arxiv.org/abs/2602.16291)' 'inheritance-calculus'
          shopt -u globstar nullglob

          # Strip overlay-language and overlay-library workspace references
          substituteInPlace pyproject.toml \
            --replace-fail ', overlay-language = { workspace = true }' "" \
            --replace-fail ', overlay-library = { workspace = true }' ""

          # Remove overlay packages from uv.lock
          substituteInPlace uv.lock \
            --replace-fail $'    "overlay-language",\n' "" \
            --replace-fail $'    "overlay-library",\n' "" \
            --replace-fail $'[[package]]\nname = "overlay-language"\nsource = { editable = "packages/overlay-language" }\ndependencies = [\n    { name = "mixinv2" },\n]\n\n[package.metadata]\nrequires-dist = [{ name = "mixinv2", editable = "packages/mixinv2" }]\n' "" \
            --replace-fail $'[[package]]\nname = "overlay-library"\nsource = { editable = "packages/overlay-library" }\ndependencies = [\n    { name = "mixinv2-library" },\n]\n\n[package.metadata]\nrequires-dist = [{ name = "mixinv2-library", editable = "packages/mixinv2-library" }]\n' ""

          # Patch out git rev-parse call (no git repo in sandbox)
          substituteInPlace packages/mixinv2/docs/conf.py \
            --replace-fail \
            "_git_commit = subprocess.check_output(
              [\"git\", \"rev-parse\", \"HEAD\"], text=True
          ).strip()" \
            '_git_commit = "anonymous"'

          # Replace GitHub extlinks with relative paths into the archive
          # (absolute GitHub URLs become dead links after anonymization)
          substituteInPlace packages/mixinv2/docs/conf.py \
            --replace-fail \
              "f'https://github.com/anonymous-author/anonymous-repo/tree/{_git_commit}/%s'" \
              "'../%s'" \
            --replace-fail "'github_banner': True" "'github_banner': False" \
            --replace-fail "'github_button': True" "'github_button': False"

          # Remove installation page (contains PyPI link that leaks identity)
          rm packages/mixinv2/docs/installation.rst
          substituteInPlace packages/mixinv2/docs/index.rst \
            --replace-fail $':doc:`installation`\n   Install the package from PyPI.\n\n' "" \
            --replace-fail $'   installation\n' ""

          # Generate API docs and build HTML in-place
          sphinx-apidoc --implicit-namespaces \
            -o packages/mixinv2/docs/api \
            packages/mixinv2/src/mixinv2
          sphinx-build -b html \
            packages/mixinv2/docs \
            packages/mixinv2/docs/_build/html

          # Copy HTML docs to top-level docs/ directory
          cp -rl packages/mixinv2/docs/_build/html docs

          cd ..
          zip -r --latest-time $TMPDIR/supplementary-material.zip supplementary-material
        '';

        installPhase = ''
          cp $TMPDIR/supplementary-material.zip $out
        '';

        doInstallCheck = true;
        installCheckPhase = ''
          unzip $out -d $TMPDIR/verify

          # No identity leaks
          ${assertNoIdentityLeak "$TMPDIR/verify/supplementary-material/"}
          if grep -rl "2602.16291" $TMPDIR/verify/supplementary-material/; then
            echo "FAIL: Found arxiv self-reference '2602.16291'" >&2; exit 1
          fi

          # HTML docs present
          test -d $TMPDIR/verify/supplementary-material/docs
          test -f $TMPDIR/verify/supplementary-material/docs/index.html
          test -f $TMPDIR/verify/supplementary-material/packages/mixinv2/docs/_build/html/index.html

          # Installation page absent (PyPI link leaks identity)
          if find $TMPDIR/verify/supplementary-material -name 'installation.*' | grep -q .; then
            echo "FAIL: Found installation page" >&2; exit 1
          fi

          # Excluded items absent
          if find $TMPDIR/verify/supplementary-material -path '*inheritance-calculus*' \
            -o -path '*overlay-language*' -o -path '*overlay-library*' | grep -q .; then
            echo "FAIL: Found excluded directory" >&2; exit 1
          fi

          # No overlay references in file contents
          if grep -rl 'overlay-language\|overlay-library' $TMPDIR/verify/supplementary-material/; then
            echo "FAIL: Found overlay-language or overlay-library reference" >&2; exit 1
          fi

          # Anonymization applied
          ${assertAnonymized "$TMPDIR/verify/supplementary-material/"}

          # Integration test (uv sync + pytest) requires network access,
          # so it cannot run in the Nix sandbox. Run manually:
          #   cd /tmp && unzip result && cd supplementary-material
          #   uv sync && uv run pytest tests/ packages/mixinv2-examples/tests/
        '';
      };

    in {
      mixinv2PyprojectOverrides = genericPyprojectOverrides;
      packages.supplementary-material = supplementaryMaterial;
    };
}
