#!/usr/bin/env bash
set -euo pipefail

pdflatex accelerate-ad.tex
convert -density 500 accelerate-ad.pdf -background white -flatten accelerate-ad.png
rm accelerate-ad.{log,aux,pdf}
