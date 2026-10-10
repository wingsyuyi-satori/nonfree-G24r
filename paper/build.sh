#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python3 verify_certificate.py
# Ordinary TeX Live/MiKTeX installations need only the latexmk command below.
# This fallback accommodates a read-only Debian installation with missing ls-R
# databases and generated formats. It writes only to a temporary directory.
if ! kpsewhich latex.ltx >/dev/null 2>&1; then
  export TEXMFVAR="${TMPDIR:-/tmp}/texmf-var-twentyfour"
  export TEXMFCONFIG="${TMPDIR:-/tmp}/texmf-config-twentyfour"
  export TEXMF="{$TEXMFVAR,/usr/share/texlive/texmf-dist,/usr/share/texmf,/etc/texmf}"
  export TEXFORMATS="$TEXMFVAR/web2c/pdftex"
  mkdir -p "$TEXMFCONFIG" "$TEXFORMATS" "$TEXMFVAR/fonts/map/pdftex"
  if [[ ! -f "$TEXFORMATS/pdflatex.fmt" ]]; then
    (cd "$TEXFORMATS" && pdftex -ini -etex -jobname=pdflatex -progname=pdflatex '\input pdflatex.ini')
  fi
  if [[ ! -f "$TEXMFVAR/fonts/map/pdftex/pdftex.map" ]]; then
    cat /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/{cm,cmextra,latxfont,symbols}.map \
        /usr/share/texmf/fonts/map/dvips/lm/lm.map > "$TEXMFVAR/fonts/map/pdftex/pdftex.map"
  fi
fi
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
