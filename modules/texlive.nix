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
      texlivePackages = [
        "scheme-medium"
        "cjk"
        "xpinyin"
        "latexmk"
        # acmart dependencies not in scheme-medium
        "xstring"
        "totpages"
        "environ"
        "trimspaces"
        "ncctools"
        "comment"
        "pbalance"
        # upquote: listings renders straight quotes in the generated code
        "upquote"
        "libertine"
        "inconsolata"
        "newtx"
        "hyperxmp"
        "ifmtarg"
        "draftwatermark"
        "preprint"
        "tex-gyre"
        "multirow"
        "zref"
        # algorithm2e for the section 2 weak-head / tabling pseudocode
        "algorithm2e"
        "relsize"
        "ifoddpage"
        # pgf/tikz for the section 3 edit-distance call-tree / DP-grid figure
        "pgf"
        # breqn auto-breaks the generated edit-distance code listing (long lambda terms).
        # It bundles flexisym/mathstyle but requires expl3, so l3kernel/l3packages come with it.
        "breqn"
        "l3kernel"
        "l3packages"
      ];

      paperTexlive = pkgs.texlive.combine
        (lib.genAttrs texlivePackages (name: pkgs.texlive.${name}));

      # The appendix-only build (supplement.tex) of a paper, for inclusion
      # in its anonymized supplementary-material bundle (see
      # modules/python.nix). POPL 2027 requires appendices to be submitted
      # as separate supplemental material rather than in the main
      # submission PDF. supplement.tex sets the acmart `anonymous' option,
      # so the rendered PDF carries no author identity.
      mkPaperPdf = { name, root, fileset, entry ? "supplement" }:
        pkgs.stdenv.mkDerivation {
          inherit name;
          src = lib.fileset.toSource { inherit root fileset; };
          nativeBuildInputs = [ paperTexlive ];
          # Reproducible PDF: fix the timestamp pdftex embeds.
          SOURCE_DATE_EPOCH = "1";
          buildPhase = ''
            runHook preBuild
            export HOME=$TMPDIR
            export TEXMFVAR=$TMPDIR/texmf-var
            latexmk -pdf -interaction=nonstopmode -halt-on-error ${entry}.tex
            runHook postBuild
          '';
          installPhase = ''
            runHook preInstall
            cp ${entry}.pdf $out
            runHook postInstall
          '';
        };

      inheritanceCalculusSources = lib.fileset.unions [
        ../paper/inheritance-calculus.tex
        ../paper/supplement.tex
        ../paper/supplement-xref.tex
        ../paper/submission.tex
        ../paper/preprint.tex
        ../paper/acmart.cls
        ../paper/ACM-Reference-Format.bst
        ../paper/references.bib
        ../paper/latexmkrc
        ../paper/generated-evaluation-trace.tex
      ];

      inheritanceCalculusSrc = lib.fileset.toSource {
        root = ../paper;
        fileset = inheritanceCalculusSources;
      };

      inheritanceCalculusAppendixPdf = mkPaperPdf {
        name = "inheritance-calculus-appendix.pdf";
        root = ../paper;
        fileset = inheritanceCalculusSources;
      };

      inheritanceCalculusSubmissionPdf = mkPaperPdf {
        name = "inheritance-calculus-submission.pdf";
        root = ../paper;
        fileset = inheritanceCalculusSources;
        entry = "submission";
      };

      # The arxiv submission bundle: build preprint.pdf, then tar the exact set of
      # source files latexmk recorded as inputs (from preprint.fls), dropping generated
      # outputs and .bbl and adding the .bib files. Previously a dev-shell `package-arxiv`
      # script; now a buildable artifact so the subproject owns its packaging logic.
      inheritanceCalculusArxiv = pkgs.stdenv.mkDerivation {
        name = "inheritance-calculus-arxiv-submission.tar.gz";
        src = inheritanceCalculusSrc;
        nativeBuildInputs = [ paperTexlive pkgs.gnutar pkgs.gawk pkgs.gzip ];
        SOURCE_DATE_EPOCH = "1";
        buildPhase = ''
          runHook preBuild
          export HOME=$TMPDIR
          export TEXMFVAR=$TMPDIR/texmf-var
          latexmk -pdf -interaction=nonstopmode -halt-on-error preprint.tex
          tar -czf "$TMPDIR/arxiv-submission.tar.gz" \
            -C . \
            $(gawk '
              NR==1 && /^PWD /{pwd=$2 "/"; next}
              /^OUTPUT /{gsub(/^OUTPUT \.\//, "OUTPUT "); outputs[$2]=1; next}
              /^INPUT /{
                sub(/^INPUT \.\//, "INPUT ");
                path=$2;
                if (path ~ /^\//) {
                  if (index(path, pwd)==1) path=substr(path, length(pwd)+1);
                  else next;
                }
                inputs[path]=1;
              }
              END{for (f in inputs) if (!(f in outputs) && f !~ /\.bbl$/) print f}
            ' preprint.fls | sort -u) \
            *.bib
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
      packages.inheritance-calculus-appendix = inheritanceCalculusAppendixPdf;
      packages.inheritance-calculus-submission = inheritanceCalculusSubmissionPdf;
      packages.inheritance-calculus-arxiv = inheritanceCalculusArxiv;
    };
}
