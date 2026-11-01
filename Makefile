PYTHON ?= python3
LEAN ?= lean
LATEXMK ?= latexmk
ZIP ?= zip
LATEX = $(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error -outdir=build

PAPER_SOURCES := main.tex tr.tex references.bib $(wildcard sections/*.tex)
PYTHON_CHECKS := $(sort $(wildcard checks/check_*.py))
LEAN_MODULES := Basic Perspectives CoreModels CoreObstruction CoreMixed CoreConservative CoreQuotients CoreAtomic Synthesis BooleanCore Separation FullAlgebra Reset ResetModels OneConstant Fragments RawFragments OwnerFragments OwnerModels ChainGuards MixedPolicies SealedRounds
LEAN_OBJECTS := $(addprefix build/lean/,$(addsuffix .olean,$(LEAN_MODULES)))

.PHONY: all paper overleaf check check-python check-lean clean

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

check-lean: $(LEAN_OBJECTS)

build/lean/%.olean: lean/%.lean lean-toolchain | build/lean
	cd lean && LEAN_PATH=../build/lean $(LEAN) -DwarningAsError=true -o ../$@ $*.lean

build/lean/Perspectives.olean: build/lean/Basic.olean
build/lean/CoreModels.olean: build/lean/Perspectives.olean
build/lean/CoreObstruction.olean: build/lean/CoreModels.olean
build/lean/CoreMixed.olean: build/lean/CoreModels.olean
build/lean/CoreConservative.olean: build/lean/CoreModels.olean
build/lean/CoreQuotients.olean: build/lean/CoreObstruction.olean
build/lean/CoreAtomic.olean: build/lean/CoreObstruction.olean build/lean/Reset.olean
build/lean/Synthesis.olean: build/lean/Perspectives.olean
build/lean/BooleanCore.olean: build/lean/Synthesis.olean
build/lean/Separation.olean: build/lean/Synthesis.olean
build/lean/FullAlgebra.olean: build/lean/Separation.olean
build/lean/Reset.olean: build/lean/Separation.olean
build/lean/ResetModels.olean: build/lean/Reset.olean
build/lean/OneConstant.olean: build/lean/Separation.olean
build/lean/Fragments.olean: build/lean/Reset.olean
build/lean/OwnerFragments.olean: build/lean/FullAlgebra.olean build/lean/Fragments.olean
build/lean/RawFragments.olean: build/lean/Fragments.olean

build/lean/OwnerModels.olean: build/lean/OwnerFragments.olean
build/lean/ChainGuards.olean: build/lean/OwnerFragments.olean
build/lean/MixedPolicies.olean: build/lean/ChainGuards.olean

build build/lean:
	mkdir -p $@

clean:
	rm -rf build
