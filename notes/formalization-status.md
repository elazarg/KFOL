# Active formalization status

The entire main-paper scope is proved: **23/23 main result rows**,
**64/64 required catalog rows**, and **21/21 required prose obligations**.
The [inventory](formalization-claims.json) is authoritative for scope.
Other report results remain optional and have their own evidence status.

| Audit entrypoint | Mathematical statements | Presentation |
| --- | ---: | --- |
| [Paper.lean](../Paper.lean) | 79 | Main text and the report claims it cites; 603 lines |
| [Report.lean](../Report.lean) | 33 | Further report results and proof ingredients |
| [Results/Certificates](../KFOL/Results/Certificates.lean) | 140 preserved contracts | Original full statements, including native machines, codecs and intermediate invariants |

Every root proof names one library theorem. Both root files have no semantic
definitions and end with a failing namespace axiom audit. The whole-project
axiom audit also checks private library helpers. The relocation manifest pins
all 140 previous complete signatures, so consolidation has not dropped or
weakened them.

The [audit guide](audit-guide.md) explains the human reading order. Natural
vocabulary is grouped in `Definitions/PaperAlgebra`, `PaperGames` and
`Complexity`, with their underlying mathematical definitions indexed separately. The report’s
navigation vocabulary is in `Definitions/Queries`.

| Definition surface | Theorem types | Semantic declarations | Source files | Written review units |
| --- | ---: | ---: | ---: | ---: |
| Paper | 79 | 635 | 35 | 333 |
| Report | 33 | 440 | 25 | 193 |

The slices overlap and exclude theorem proof bodies. These meaning indexes do
not replace the human comparison with the manuscript or the proof/axiom audits.

## Verification

The production integration checks are:

- `make check-lean`: literal façade and preservation checks, inventory,
  independent algebra build/import audit, Paper/Report and whole-source axiom
  audits, both definition indexes, actual negative audit fixtures and 87 strict
  Lean regressions.
- `make check-python`: the explicit 33 independent Python checks, mapped to the
  current paper in `checks/README.md` and the verification appendix.
- `make paper`: both manuscripts, with the main paper remaining 14 pages and
  label snapshots refreshed.

Every authored proof closure uses only `propext`, `Classical.choice` and
`Quot.sound` where needed. Pure algebra remains independent of GameTheory,
ComplexityLib/Cslib and the strategic/round branches.

The production pins remain Lean/mathlib 4.35.0, GameTheory
`6f1af625b77215dd9e4454e6120275dbd8b61f51`, ComplexityLib
`054834a4a4e6ac3ec50ed770bacea7fc42eccc7d`, and CSLib
`254e30e6d4299c51323aaeaf5f51a4763b375d4a`.

## Mathematical additions retained

The proof-mining session proved sharp K−1 support, exact exponential circuit
tables and semantic lower bounds on every equivalent reset tree, finite
threshold state bounds, and Boolean observation completeness and order recovery
for pair-only components. The nested-quantifier extension gives nodewise
preservation over infinite, history-dependent witness domains.

The binary representation is now certified as an actual recursive owned-choice
fold, with every retained action compiled exactly once. A regression rejects a
wrong-owner tree despite agreement of its possible SPE winners. The independent
SPE definition still uses complete deviations, not the recurrence it certifies.

The TR-only navigation investigation adds exact, quadratic-size Core XPath
compilation on a nonempty valuation-document schema, a faithful single-owner
relational representation, and generic impossibility theorems for representing
reset as relational product and for selecting nonempty intersections. The
actual libxml2 XPath engine passed 60,208 independent comparisons.

The report's dependent calculus, general real-QE/semialgebraicity, numerical
free-algebra counts and unused extensions remain outside main-paper completion.
The historical mixed-open-game obstruction keeps its separately pinned external
artifact. The earlier Std-only Lean tree is retired at revision `7014dbb`;
current production consists of KFOL and the two root audit entrypoints.
