PYTHON ?= python3
LATEXMK ?= latexmk
ZIP ?= zip
LATEX = $(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error -outdir=build

PAPER_SOURCES := main.tex tr.tex references.bib $(wildcard sections/*.tex)
# Current paper/report regressions; see checks/README.md and the verification appendix.
PYTHON_CHECKS := \
    checks/check_chain_guards.py \
    checks/check_choice.py \
    checks/check_common_source.py \
    checks/check_decision_rules.py \
    checks/check_connections.py \
    checks/check_core.py \
    checks/check_core_atomic.py \
    checks/check_core_atomic_basis.py \
    checks/check_core_basis.py \
    checks/check_core_conservative.py \
    checks/check_core_obstruction.py \
    checks/check_core_padded_crossing.py \
    checks/check_core_unary_polynomials.py \
    checks/check_fibers.py \
    checks/check_forest.py \
    checks/check_fragments.py \
    checks/check_general.py \
    checks/check_interaction.py \
    checks/check_mixed_policies.py \
    checks/check_one_owner.py \
    checks/check_open_game_obstruction.py \
    checks/check_owner_basis.py \
    checks/check_owner_finite_basis.py \
    checks/check_owner_presentation.py \
    checks/check_owner_synthesis.py \
    checks/check_policy_families.py \
    checks/check_protocols.py \
    checks/check_raw_pairs.py \
    checks/check_reset.py \
    checks/check_reset_circuits.py \
    checks/check_sealed_rounds.py \
    checks/check_structure.py \
    checks/check_symmetric.py \
    checks/check_two_players.py


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
