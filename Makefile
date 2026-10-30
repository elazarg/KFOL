PYTHON ?= python3
LEAN ?= lean
LATEXMK ?= latexmk
ZIP ?= zip

PAPER_SOURCES := main.tex references.bib $(wildcard sections/*.tex)
PYTHON_CHECKS := $(sort $(wildcard checks/check_*.py))
LEAN_MODULES := Basic Perspectives Synthesis BooleanCore Separation Reset ResetModels OneConstant
LEAN_OBJECTS := $(addprefix build/lean/,$(addsuffix .olean,$(LEAN_MODULES)))

.PHONY: all paper overleaf check check-python check-lean clean

all: paper

paper: build/main.pdf

build/main.pdf: $(PAPER_SOURCES) | build
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error -outdir=build main.tex

overleaf: build/overleaf.zip

build/overleaf.zip: $(PAPER_SOURCES) | build
	rm -f $@
	$(ZIP) -q $@ $(PAPER_SOURCES)

check: check-python check-lean

check-python:
	@set -e; for script in $(PYTHON_CHECKS); do $(PYTHON) $$script; done

check-lean: $(LEAN_OBJECTS)

build/lean/%.olean: lean/%.lean lean-toolchain | build/lean
	cd lean && LEAN_PATH=../build/lean $(LEAN) -DwarningAsError=true -o ../$@ $*.lean

build/lean/Perspectives.olean: build/lean/Basic.olean
build/lean/Synthesis.olean: build/lean/Perspectives.olean
build/lean/BooleanCore.olean: build/lean/Synthesis.olean
build/lean/Separation.olean: build/lean/Synthesis.olean
build/lean/Reset.olean: build/lean/Separation.olean
build/lean/ResetModels.olean: build/lean/Reset.olean
build/lean/OneConstant.olean: build/lean/Separation.olean

build build/lean:
	mkdir -p $@

clean:
	rm -rf build
