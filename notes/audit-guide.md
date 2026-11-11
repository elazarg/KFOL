# Reading the formalization

Start with [Paper.lean](../Paper.lean): its 77 theorem statements cover the main
paper, its mathematical prose claims and the report clauses it uses.
[Report.lean](../Report.lean) gives 58 further audited report statements and
proof ingredients. Both files write out the propositions; each proof names one
library theorem. Detailed codecs, descriptors, intermediate certificates and
machine contracts are in the library, including
[Results/Certificates.lean](../KFOL/Results/Certificates.lean). The previous 140
complete contracts remain there under `KFOL.Results`, with their original
signatures recorded in [audit-relocations.json](audit-relocations.json).

## Check what the statements mean

Read the statement and its hypotheses against the corresponding manuscript
claim, then open the relevant vocabulary file:

| Subject | Vocabulary entrypoint | Underlying definitions to inspect |
| --- | --- | --- |
| Winner algebras, views, reset and guarded choice | [PaperAlgebra.lean](../KFOL/Definitions/PaperAlgebra.lean) | `Public`, `Core`, `Views`, `Reset`, `Owner`, `Equational`, `Congruences`; the report's singleton profiles, binary relational tests, explicit patch operation and atomic cuts are in `CoreFunctions`, source-guard normal forms and the finite compatibility interior are in `CoreNormalForm`, with bounded rule saturation in `FiniteHorn` |
| Public games and sealed rounds | [PaperGames.lean](../KFOL/Definitions/PaperGames.lean) | `Strategic`, `Quantified`, `Rounds`; GameTheory's strategy and equilibrium interfaces |
| Decision problems and algorithms | [Complexity.lean](../KFOL/Definitions/Complexity.lean) | `Encoding`, the original term/circuit syntax, and ComplexityLib's machine and class definitions |
| Nonfinite-basis envelope | [Envelope.lean](../KFOL/Definitions/Envelope.lean), [Equational.lean](../KFOL/Definitions/Equational.lean) | Explicit copy-labelled operations; the three actual signatures and independent basis/variety predicates |
| Powerset representation | [Relational.lean](../KFOL/Definitions/Relational.lean) | Annihilating zero extension and a right regular relation with a fresh point |
| Report navigation queries | [Queries.lean](../KFOL/Definitions/Queries.lean) | Independent path/test semantics, valuation documents, compiler and regular relations |

These files are front doors, not the entire semantic surface. The
[Paper definition index](paper-definition-surface.md) and
[Report definition index](report-definition-surface.md), with their JSON graphs,
list the project definitions and external semantic interfaces reached from the
theorem **types**. They follow definitions and constructors without traversing
proof bodies. [formalization-definitions.md](formalization-definitions.md)
provides further mathematical context.

A few meanings deserve particular attention:

- Winner values are nonempty sets. Public terms distinguish winner constants,
  owned choice and role permutations. Repeated input occurrences are independent
  copies.
- Pure SPE uses full contingent profiles and whole-player deviations in every
  subtree. Its definition does not use the backward-induction recursion that
  the theorems establish.
- A round's value is the set of actual canonical sequential-equilibrium winner
  distributions. Sequential rationality and consistency are separate
  conditions; consistency uses limits of completely mixed strategies. Equality
  with observed mixed SPE and independence of the serialization order are
  proved, rather than built into the definition.
- `UsesOnly a b` restricts effective actors as well as terminal winners.
  `BooleanMenus` restricts menus to at most two actions. The no-finite-summary
  claim concerns a semantics defined on that Boolean fragment itself.
- Equational validity quantifies over all winner-set valuations. Derivability
  has independent inference rules; a basis theorem connects the two.
- Complexity problems refer to the original encoded inputs. Binary names,
  explicit permutation arrays and a binary role count are charged as input
  bytes; malformed words reject. Inspect both the language and its encoding
  when reading a class or runtime theorem.

A successful axiom audit does not establish that these definitions express the
intended mathematics. That is the purpose of this reading step.

## Check the proof evidence

After checking the statement's meaning, follow its named theorem into
`KFOL/Results` and the relevant algebra, strategy, probability or machine proof
modules. Lean's kernel checks the proofs. Each root file ends with one
`#audit_namespace` command: it checks all declarations in that namespace and
rejects transitive dependence on axioms other than `propext`,
`Classical.choice` and `Quot.sound`. The whole-source
[Audit.lean](../KFOL/Audit.lean) covers authored library declarations, including
private helpers. The checks also exercise the namespace audit on an unsupported
axiom and require rejection.

The [surface checker](../scripts/check_surfaces.py) verifies that root claims
are written literally, have single named-theorem proofs, and contain no local
semantic definitions or proof assembly. It also verifies the immutable
relocation signatures for the original 140 contracts. These checks preserve
the presentation and its evidence; they complement kernel proof checking.

Use the pinned dependencies in `lake-manifest.json` and `lean-toolchain`, then
run:

```sh
make check-lean
python3 scripts/export_definition_surface.py --check
python3 scripts/export_definition_surface.py --check --entrypoint Report
```

`make check-lean` includes these definition-index checks, the entrypoint and
whole-source audits, the independent algebra import-boundary check, and Lean
regressions. `make check-python` runs the separate finite regression programs;
those computations do not replace generic Lean proofs. `make paper` builds the
main paper and report and refreshes their committed label snapshots.

The pure algebra and its central definitions do not import GameTheory or the
machine-complexity libraries. GameTheory supports strategies and rounds;
ComplexityLib supplies the machine/class foundations. The aggregate paper
entrypoints and theorem-assembly modules naturally bring these branches
together. Their imported mathematical interfaces remain part of the semantic
review surface.
