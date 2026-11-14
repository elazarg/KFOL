PYTHON ?= python3
LAKE ?= lake
LATEXMK ?= latexmk
ZIP ?= zip
LATEX = $(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error -outdir=build

PAPER_SOURCES := main.tex tr.tex references.bib $(wildcard sections/*.tex)
.PHONY: all paper overleaf check check-lean clean

all: paper

# main.tex and tr.tex read each other's numbering from committed snapshots,
# sections/labels-main.tex and sections/labels-tr.tex, so either one builds alone.
# Numbers in one document do not depend on the other, so one export settles both.
paper: | build
	$(LATEX) main.tex
	$(LATEX) tr.tex
	$(PYTHON) scripts/export_labels.py
	$(LATEX) main.tex
	$(LATEX) tr.tex

overleaf: build/overleaf.zip

build/overleaf.zip: paper
	rm -f $@
	$(ZIP) -q $@ $(PAPER_SOURCES)

check: check-lean

# lakefile.toml makes warnings fatal. Both entrypoints check their transitive
# axioms when built; no generated inventories or external scripts are required.
check-lean:
	$(LAKE) build Paper Report

build:
	mkdir -p $@

clean:
	rm -rf build
