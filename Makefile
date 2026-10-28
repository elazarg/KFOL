.PHONY: all paper check check-archive check-minimal paper-minimal

all: paper

paper:
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build main.tex

check-archive:
	cd archive/manuscript-2026-10-28 && sha256sum --check --quiet MANIFEST.sha256
	cd archive/public-core-draft-2026-10-28 && sha256sum --check --quiet MANIFEST.sha256

check: check-archive
	python3 checks/finite_models.py
	python3 checks/review_models.py

check-minimal:
	python3 research/minimal/check.py
	python3 research/minimal/check_structure.py
	python3 research/minimal/check_symmetric.py
	python3 research/minimal/check_general.py
	mkdir -p build/minimal/lean
	cd research/minimal && lean -DwarningAsError=true -o ../../build/minimal/lean/Basic.olean Basic.lean
	cd research/minimal && LEAN_PATH=../../build/minimal/lean lean -DwarningAsError=true -o ../../build/minimal/lean/Perspectives.olean Perspectives.lean
	cd research/minimal && LEAN_PATH=../../build/minimal/lean lean -DwarningAsError=true -o ../../build/minimal/lean/Synthesis.olean Synthesis.lean
	cd research/minimal && LEAN_PATH=../../build/minimal/lean lean -DwarningAsError=true BooleanCore.lean

paper-minimal:
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build/minimal research/minimal/report.tex
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build/minimal research/minimal/structure.tex
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build/minimal research/minimal/symmetric.tex
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build/minimal research/minimal/general.tex

