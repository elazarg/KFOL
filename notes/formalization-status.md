# Active formalization status and integration queue

The completion target is the entire main paper, its substantive prose and
necessary report dependencies. The inventory is authoritative for scope.
The complete main-paper scope is proved: **23/23 main result rows**,
**63/63 required catalog rows**, and **21/21 required prose obligations**.
Root `Paper.lean` contains **138 full public statements**, each with a guarded
axiom check. The proof-mining production build, all regressions, audits and manuscript checks pass.
Report-only results remain optional; the historical related-work artifact is
separately rebuilt and audited under its original pins.

## Parallel execution

Agents share the checkout without worktrees or edits to `../GameTheory`.
Workers own separate files, compile their results and provide integration notes.
Root maintains Paper, configuration, audits, inventory and manuscript evidence,
then commits coherent integrations after complete checks.

| Workstream | Owner | Completed | Next integration gate |
| --- | --- | --- | --- |
| Native reset circuits and synthesis | `owner` | Original-word reset/Fin-three coNP-completeness and native primitive-tree synthesis with independent root/table/winner semantics | Complete |
| Hardness and review | `nonfinite_basis` | Native DAG generator, full/public/core hardness, certificate bounds, canonicalizer consequence and final semantic scope review | Complete |
| Full/public/core complexity | `complexity` | All six fixed/uniform endpoints; original-word sparse counterverifier, explicit-array validation, quadratic certificates and arbitrary padding | Complete; definition-surface report reproduced |
| Owner branches and integration | root | Complete raw/owner/policy dichotomies, 138 literal Paper statements, claim reconciliation and pinned historical rebuild | Complete |

The production pins are GameTheory `6f1af625b77215dd9e4454e6120275dbd8b61f51`
from `port/cslib-complexity`, ComplexityLib
`054834a4a4e6ac3ec50ed770bacea7fc42eccc7d`, CSLib
`254e30e6d4299c51323aaeaf5f51a4763b375d4a`, and Lean/mathlib 4.35.0.
Algebra and representation imports remain independent of those game/machine
libraries. All round mathematics is complete against actual canonical SE.

## Final verification

No required mathematical proof remains. Completed verification:

- `make check-lean`: independent algebra build/import
  audit, full Paper/whole-project axiom audit, negative import check and all 85 strict Lean regressions pass.
- `make check-python`: all independent Python checks pass.
- `python3 scripts/check_inventory.py`: 149 source statements, 23 prose
  obligations, current evidence fingerprints and 138 public statements reconcile.
- `python3 scripts/export_definition_surface.py --check --no-build`: the
  theorem-type graph and readable review index reproduce after the clean build.
- `make paper`: both manuscripts build; the main paper remains 14 pages and
  label snapshots are refreshed.

Every authored proof closure uses only `propext`, `Classical.choice` and
`Quot.sound` where needed. The pure algebra closure excludes GameTheory,
ComplexityLib/Cslib and strategic/round modules. The retired Std-only tree is preserved at revision `7014dbb`; the single
production artifact is `KFOL/` and root `Paper.lean`. The separate historical
obstruction build and its five axiom closures also pass under the original pins.

The report's encoded substitution runtime, H/policy circuit extensions,
dependent calculus and general round semialgebraicity remain outside the
main-paper scope. The main substitution formula and both required reset-DAG
clauses are proved; these are explicit dependency fragments in the inventory.

## Integration contract

Integration notes name exact paper claims, complete public propositions,
independent definitions, proof modules, validation and residual gaps. Root
reviews hypotheses and every clause, adds full Paper statements, extends source,
axiom and import audits, refreshes evidence fingerprints, then validates and
commits. Partial statements remain partial in the inventory.

During checkpoints workers freeze production and continue in ignored
`*.lean.pending` staging files. Only compiled candidates enter KFOL. The main
paper stays at most 15 pages; proof evidence belongs in its verification appendix.
No admitted proofs, project axioms, unchecked counts, external-theorem premises
or detached certificates count as completion.


The review correction removes four alpha/orientation repeats from the owner
basis, leaving 36 native identities with proved actual range cardinality.
The Boolean impossibility quantifies Boolean-only encodings and contexts.
Finite-action public choice, exponential circuit tables, diagonal security and
the exact semantic definition of reset tables now have explicit Paper clauses.
The three previously omitted prose claims are independent inventory obligations.


The Python suite is now the explicit 33-entry list in the Makefile, mapped to
current paper/report claims in `checks/README.md` and the verification appendix.
Superseded core-basis exploration, probes, unused helpers and unused inputs
were pruned; the current padded-grid proof and retained classification checks
remain covered. Historical exploration is available at revision `c5723ac`.


The [proof-mining session](proof-mining.md) adds six full public statements
while preserving all main-paper statements. Three report propositions
record sharp K−1 support for arbitrary root action families, a finite threshold
state lower bound, and Boolean observation completeness for arbitrary pair-only
games. The shared-circuit proposition now gives exact tables and exponential
bounds on every semantically equivalent reset tree. Rational probes also recover
the scalar order. The source catalog has 149 rows, including these new
report results; all 63 required rows are complete. The rewritten scalar corollary
uses the general observation proposition, which is recorded as one additional
completed proof dependency. No independent semantic
definitions were added, and the generated public-type surface now has 138
statements reaching 1,014 semantic declarations in the same 57 files.
