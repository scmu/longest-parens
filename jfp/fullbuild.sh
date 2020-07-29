#!/bin/bash
lhs2TeX LongParens.lhs > LongParens.tex
pdflatex LongParens.tex
bibtex LongParens.aux
pdflatex LongParens.tex
pdflatex LongParens.tex
