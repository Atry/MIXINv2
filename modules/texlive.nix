{ flake-parts-lib, ... }: {
  # Expose the paper's TeXLive package list as a per-system option so the monorepo
  # development environment can install the same TeX into its dev shell while this
  # subrepo only produces the appendix/arxiv artifacts (no dev shell here).
  options.perSystem = flake-parts-lib.mkPerSystemOption ({ lib, ... }: {
    options.inheritanceCalculusTexlivePackages = lib.mkOption {
      type = lib.types.listOf lib.types.str;
      description = "TeXLive package names for the inheritance-calculus paper build and the dev-shell TeX.";
    };
  });
  config.perSystem = { pkgs, lib, ... }:
    let
      # TeXLive packages shared by the dev-shell paper build and the standalone appendix
      # PDF / arxiv-submission derivations below.
      # Packages beyond pkgs.texliveSmall (scheme-small), the base of paperTexlive below
      # and of the dev shell's languages.texlive. Each one is listed because a build of
      # this paper reads a file of it (the .fls recorder); packages the builds read that
      # scheme-small already carries (pgf, upquote, the expl3 runtime, ...) are not listed.
      texlivePackages = [
        "latexmk"
        # CJKutf8 (from cjk) renders the Chinese preprint (preprint-zh.tex) under
        # pdfLaTeX, like the English entries; arphic supplies the gbsn (SongTi)
        # Type1 font it uses, so the build needs no system fonts.
        "cjk"
        "arphic"
        # The acmart class and its ACM-Reference-Format.bst, which scheme-small lacks.
        "acmart"
        # acmart dependencies not in scheme-small. libertine (with fontaxes and
        # mweights, which it loads), newtx and inconsolata are its text, math and
        # typewriter fonts; newtxmath reads kastrup's binhex.tex; fontname's
        # texfonts.map is read by kpathsea's font name lookups.
        "xstring"
        "totpages"
        "environ"
        "trimspaces"
        "ncctools"
        "comment"
        "hyperxmp"
        "kastrup"
        "ifmtarg"
        "libertine"
        "fontaxes"
        "mweights"
        "inconsolata"
        "newtx"
        "fontname"
        # minted highlights the code listings via Pygments; latex2pydata, catchfile
        # and pgfopts are minted's own dependencies, fvextra (extended fancyvrb) its
        # verbatim engine.
        "minted"
        "fvextra"
        "latex2pydata"
        "catchfile"
        "pgfopts"
        # Type 1 cm-super fonts for the TS1 Computer Modern typewriter glyphs it sets.
        "cm-super"
        # mathrsfs (\mathscr).
        "rsfs"
        # txfonts' txsyc, drawn on by newtxmath's ntxsyc virtual font (symbolsC).
        "txfonts"
        "multirow"
        # braket provides \Set{ e | c }, the auto-sized set-builder whose middle
        # bar scales with its content and carries its own spacing.
        "braket"
        # zref-savepos for the positions recorded on the second pass.
        "zref"
        # algorithm2e for the section 2 weak-head / tabling pseudocode; it loads
        # relsize and ifoddpage.
        "algorithm2e"
        "relsize"
        "ifoddpage"
      ];

      paperTexlive = pkgs.texliveSmall.withPackages
        (ps: map (name: ps.${name}) texlivePackages);

      mkPaperPdf = { name, entry }:
        pkgs.stdenv.mkDerivation {
          inherit name;
          src = inheritanceCalculusSrc;
          nativeBuildInputs = [ paperTexlive (pkgs.python3.withPackages (ps: [ ps.pygments ])) ];
          # Reproducible PDF: fix the timestamp pdftex embeds.
          SOURCE_DATE_EPOCH = "1";
          # The source tree carries the paper plus the real MIXINv2 files the
          # paper \lstinputlistings, at their real relative paths. Build from the
          # paper subdirectory so "../packages/.../X.mixin.yaml" resolves exactly
          # as it does under a plain `cd paper && latexmk`. All preprocessing of
          # the included sources (comment stripping) happens in LaTeX macros, not
          # here, so both build paths are identical.
          buildPhase = ''
            runHook preBuild
            export HOME=$TMPDIR
            export TEXMFVAR=$TMPDIR/texmf-var
            cd paper
            latexmk -pdf -interaction=nonstopmode -halt-on-error ${entry}.tex
            runHook postBuild
          '';
          installPhase = ''
            runHook preInstall
            cp ${entry}.pdf $out
            runHook postInstall
          '';
        };

      inheritanceCalculusPaperSources = lib.fileset.unions [
        ../paper/inheritance-calculus.tex
        ../paper/submission.tex
        ../paper/preprint.tex
        ../paper/preprint-zh.tex
        # The pdfLaTeX stand-in for LaTeXML's latexml package (\iflatexml false).
        ../paper/latexml.sty
        ../paper/references.bib
        ../paper/latexmkrc
        ../paper/generated-evaluation-trace.tex
        ../paper/generated-nat-answers.tex
      ];

      # Real MIXINv2 source files the paper \lstinputlistings at their real
      # relative paths (../packages/..., ../mixinv2.schema.json, relative to the
      # paper directory). Carried in the source tree so both `nix build` and a
      # plain `cd paper && latexmk` resolve them; the LaTeX include macros copy
      # each (stripping comments where appropriate) into the build directory.
      inheritanceCalculusIncludedSources = lib.fileset.unions [
        ../packages/mixinv2-examples/src/mixinv2_examples/ComplexModule.mixin.yaml
        ../packages/mixinv2-library/src/mixinv2_library/Builtin/NatData.mixin.yaml
        ../packages/mixinv2-library/src/mixinv2_library/Builtin/NatDataZero.mixin.yaml
        ../packages/mixinv2-library/src/mixinv2_library/Builtin/NatDataSuccessor.mixin.yaml
        ../packages/mixinv2-library/src/mixinv2_library/Builtin/NatPlus.mixin.yaml
        ../packages/mixinv2-library/src/mixinv2_library/Builtin/NatPlusZero.mixin.yaml
        ../packages/mixinv2-library/src/mixinv2_library/Builtin/NatPlusSuccessor.mixin.yaml
        ../packages/mixinv2-library/src/mixinv2_library/Builtin/NatVisitor.mixin.yaml
        ../packages/mixinv2-library/src/mixinv2_library/Builtin/NatVisitorZero.mixin.yaml
        ../packages/mixinv2-library/src/mixinv2_library/Builtin/NatVisitorSuccessor.mixin.yaml
        ../packages/mixinv2-library/src/mixinv2_library/Builtin/NatEquality.mixin.yaml
        ../packages/mixinv2-library/src/mixinv2_library/Builtin/NatEqualityZero.mixin.yaml
        ../packages/mixinv2-library/src/mixinv2_library/Builtin/NatEqualitySuccessor.mixin.yaml
        ../packages/mixinv2-library/src/mixinv2_library/Builtin/BooleanData.mixin.yaml
        # Case-study test fixtures (the concrete numerals and the FFI-free cores
        # of the arithmetic / Cartesian-product tests), shown in Section
        # "Case Study" via \mixinstrip. The full ArithmeticTest /
        # CartesianProductTest entry points add the ToPython FFI for the test
        # suite and are not shown; the paper shows these pure-calculus cores.
        ../packages/mixinv2-library/tests/NatConstants.mixin.yaml
        ../packages/mixinv2-library/tests/NatArithmeticTest.mixin.yaml
        ../packages/mixinv2-library/tests/NatCartesianProductTest.mixin.yaml
      ];

      # Root at the subrepo so the paper and its included package sources keep
      # their real relative positions in the sandbox; builds cd into paper/.
      inheritanceCalculusSrc = lib.fileset.toSource {
        root = ../.;
        fileset = lib.fileset.unions [
          inheritanceCalculusPaperSources
          inheritanceCalculusIncludedSources
        ];
      };

      inheritanceCalculusSubmissionPdf = mkPaperPdf {
        name = "inheritance-calculus-submission.pdf";
        entry = "submission";
      };

      # The Chinese preprint: the same full document as the English preprint with
      # reader-facing prose in Chinese, built with pdfLaTeX via CJKutf8.
      inheritanceCalculusPreprintZhPdf = mkPaperPdf {
        name = "inheritance-calculus-preprint-zh.pdf";
        entry = "preprint-zh";
      };

      # The arxiv submission bundle: build preprint.pdf, then tar the inputs
      # latexmk recorded (from preprint.fls), dropping generated outputs, .bbl,
      # and the out-of-tree "../" sources the LaTeX include macros read. The
      # comment-stripped basenames those macros write into the paper directory
      # travel instead, alongside the .bib files, so the upload is self-contained
      # and flat. Previously a dev-shell `package-arxiv` script; now a buildable
      # artifact so the subproject owns its packaging logic.
      inheritanceCalculusArxiv = pkgs.stdenv.mkDerivation {
        name = "inheritance-calculus-arxiv-submission.tar.gz";
        src = inheritanceCalculusSrc;
        nativeBuildInputs = [ paperTexlive pkgs.gnutar pkgs.gawk pkgs.gzip (pkgs.python3.withPackages (ps: [ ps.pygments ])) ];
        SOURCE_DATE_EPOCH = "1";
        buildPhase = ''
          runHook preBuild
          export HOME=$TMPDIR
          export TEXMFVAR=$TMPDIR/texmf-var
          cd paper
          # _minted is not committed, so regenerate the highlight cache from
          # scratch: a normal shell-escape compile populates _minted/.
          latexmk -pdf -interaction=nonstopmode -halt-on-error preprint.tex
          # Ship preprint.tex unchanged: it auto-selects minted's frozencache
          # when compiled without -shell-escape, which is exactly how arxiv
          # builds, so the upload compiles against the regenerated _minted cache
          # without any source rewriting here.
          tar -czf "$TMPDIR/arxiv-submission.tar.gz" \
            -C . \
            $(gawk '
              NR==1 && /^PWD /{pwd=$2 "/"; next}
              /^OUTPUT /{gsub(/^OUTPUT \.\//, "OUTPUT "); outputs[$2]=1; next}
              /^INPUT /{
                sub(/^INPUT \.\//, "INPUT ");
                path=$2;
                if (path ~ /^\.\.\//) next;
                if (path ~ /^\//) {
                  if (index(path, pwd)==1) path=substr(path, length(pwd)+1);
                  else next;
                }
                inputs[path]=1;
              }
              # Skip every .minted file: the persistent cache travels via the
              # explicit _minted argument below, and the per-job .config/.data
              # transients no longer exist by the time tar runs.
              END{for (f in inputs) if (!(f in outputs) && f !~ /\.bbl$/ && f !~ /\.minted$/) print f}
            ' preprint.fls | sort -u) \
            _minted *.bib *.mixin.yaml
          runHook postBuild
        '';
        installPhase = ''
          runHook preInstall
          cp "$TMPDIR/arxiv-submission.tar.gz" $out
          runHook postInstall
        '';
      };
    in {
      inheritanceCalculusTexlivePackages = texlivePackages;
      packages.inheritance-calculus-submission = inheritanceCalculusSubmissionPdf;
      packages.inheritance-calculus-preprint-zh = inheritanceCalculusPreprintZhPdf;
      packages.inheritance-calculus-arxiv = inheritanceCalculusArxiv;
    };
}
