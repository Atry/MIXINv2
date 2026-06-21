{ ... }: {
  imports = [ ./dev.nix ];
  partitions.dev.module.perSystem = { pkgs, lib, ... }:
    let
      # TeXLive packages shared by the devshell paper build and the
      # standalone appendix PDF derivation below.
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
        ../papers/inheritance-calculus/inheritance-calculus.tex
        ../papers/inheritance-calculus/supplement.tex
        ../papers/inheritance-calculus/supplement-xref.tex
        ../papers/inheritance-calculus/submission.tex
        ../papers/inheritance-calculus/preprint.tex
        ../papers/inheritance-calculus/acmart.cls
        ../papers/inheritance-calculus/ACM-Reference-Format.bst
        ../papers/inheritance-calculus/references.bib
        ../papers/inheritance-calculus/latexmkrc
        ../papers/inheritance-calculus/generated-evaluation-trace.tex
      ];

      inheritanceCalculusAppendixPdf = mkPaperPdf {
        name = "inheritance-calculus-appendix.pdf";
        root = ../papers/inheritance-calculus;
        fileset = inheritanceCalculusSources;
      };
    in {
      packages.inheritance-calculus-appendix = inheritanceCalculusAppendixPdf;

      ml-ops.devcontainer.devenvShellModule = {
        packages = [ pkgs.tex-fmt pkgs.poppler-utils ];
        scripts.package-arxiv.exec = ''
          cd papers/inheritance-calculus
          latexmk -pdf preprint.tex
          ${lib.getExe pkgs.gnutar} -czvf arxiv-submission.tar.gz \
            -C . \
            $(${lib.getExe pkgs.gawk} '
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
        '';
        languages = {
          texlive = {
            enable = true;
            packages = texlivePackages;
          };
        };
      };
    };
}
