PYTHON ?= python3
LATEXMK ?= latexmk
ZIP ?= zip
LATEX = $(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error -outdir=build

PAPER_SOURCES := main.tex tr.tex references.bib $(wildcard sections/*.tex)
PYTHON_CHECKS := $(sort $(wildcard checks/check_*.py))

.PHONY: all paper overleaf check check-python check-lean check-algebra clean

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

check: check-python check-lean

check-python:
	@set -e; for script in $(PYTHON_CHECKS); do $(PYTHON) $$script; done

check-lean: check-algebra

check-algebra:
	$(PYTHON) scripts/check_algebra.py

build:
	mkdir -p $@

clean:
	rm -rf build
