.PHONY: all paper check check-archive

all: paper

paper:
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build main.tex

check-archive:
	cd archive/manuscript-2026-10-28 && sha256sum --check --quiet MANIFEST.sha256

check: check-archive
	python3 checks/finite_models.py

