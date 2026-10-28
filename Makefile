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
	cd research/minimal && lean -DwarningAsError=true Basic.lean

paper-minimal:
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build/minimal research/minimal/report.tex

