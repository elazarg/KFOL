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
	mkdir -p build/minimal/lean
	cd research/minimal && lean -DwarningAsError=true -o ../../build/minimal/lean/Basic.olean Basic.lean
	cd research/minimal && LEAN_PATH=../../build/minimal/lean lean -DwarningAsError=true Perspectives.lean

paper-minimal:
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build/minimal research/minimal/report.tex
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build/minimal research/minimal/structure.tex

