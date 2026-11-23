LAKE ?= lake

.PHONY: all paper check check-lean clean

all: paper

# The paper sources and their build are in overleaf/, a separate repository.
paper:
	$(MAKE) -C overleaf paper

check: check-lean

# lakefile.toml makes warnings fatal. Both entrypoints check their transitive
# axioms when built; no generated inventories or external scripts are required.
check-lean:
	$(LAKE) build Paper Report

clean:
	$(MAKE) -C overleaf clean
