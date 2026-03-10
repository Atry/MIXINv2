{ ... }: {
  imports = [ ./dev.nix ];
  partitions.dev.module.perSystem = { pkgs, lib, ... }: {
    ml-ops.devcontainer.devenvShellModule = {
      packages = [ pkgs.tex-fmt ];
      scripts.package-arxiv.exec = ''
        cd inheritance-calculus
        latexmk -pdf preprint.tex
        ${lib.getExe pkgs.gnutar} -czvf arxiv-submission.tar.gz \
          -C . \
          $(${lib.getExe pkgs.gawk} '
            /^OUTPUT [^\/]/{gsub(/^OUTPUT \.\//, "OUTPUT "); outputs[$2]=1}
            /^INPUT [^\/]/{gsub(/^INPUT \.\//, "INPUT "); inputs[$2]=1}
            END{for (f in inputs) if (!(f in outputs) && f !~ /\.bbl$/) print f}
          ' preprint.fls | sort -u) \
          *.bib
      '';
      languages = {
        texlive = {
          enable = true;
          packages = [
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
            "libertine"
            "inconsolata"
            "newtx"
            "hyperxmp"
            "ifmtarg"
            "draftwatermark"
            "preprint"
            "tex-gyre"
            "multirow"
          ];
        };
      };
    };
  };
}
