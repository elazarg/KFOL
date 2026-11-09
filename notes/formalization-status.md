# Active formalization status and integration queue

The completion target is the entire main paper, its substantive prose and
necessary report dependencies. The inventory is authoritative for scope.
The current integration has **21/23 main result rows**, **58/61 required catalog
rows**, and **14/18 required prose obligations** kernel-checked in full.
The other required rows all have checked components. Counts measure complete
statements, not effort. Root `Paper.lean` now has 118 full public statements.

## Parallel execution

Agents share the checkout without worktrees or edits to `../GameTheory`.
Workers own separate files, compile their results and provide integration notes.
Root maintains Paper, configuration, audits, inventory and manuscript evidence,
then commits coherent integrations after complete checks.

| Workstream | Owner | Completed | Next integration gate |
| --- | --- | --- | --- |
| Native reset circuits | `owner` | Generic graph/codec, CNF assembly and exact counts, SAT/UNSAT semantics, actual three-generator completeness; native cached finite-algebra evaluator | Original-word parser/verifier and coNP upper; assemble reset completeness, then reset-table synthesis runtime |
| Reset circuit reduction machine | `nonfinite_basis` | All core nonfinite-basis, basis, scalar and two-player mathematics; full original-word uniform core extraction runtime | Native shared CNF graph generator runtime and 3SAT class transport |
| Full/core complexity | `complexity` | Full raw-signature hard branch and policy dichotomy; original full-word codecs/decoder/fold, sparse pair evaluation and semantic bridge | Uniform verifier/certificate bounds, fixed/uniform full/core coNP-completeness, core canonicalizer consequence; H-pair-to-owner hard branch |
| Owner branches and integration | root | Full raw-signature polynomial branch; linear relative-observation compilation, generic owner-language coNP upper, all owner polynomial branches, joint-observation counterexample; historical isolated obstruction rebuilt | Integrate class endpoints, reconcile all public statements/definitions, audit and commit |

The production pins are GameTheory `6f1af625b77215dd9e4454e6120275dbd8b61f51`
from `port/cslib-complexity`, ComplexityLib
`054834a4a4e6ac3ec50ed770bacea7fc42eccc7d`, CSLib
`254e30e6d4299c51323aaeaf5f51a4763b375d4a`, and Lean/mathlib 4.35.0.
Algebra and representation imports remain independent of those game/machine
libraries. All round mathematics is complete against actual canonical SE.

## Remaining whole-claim gates

1. `gen:thm:complexity`: full/core validity with original binary K, sparse names
   and explicit permutation arrays; fixed-K endpoints and native hardness.
2. `owner:cor:complexity`: transport the checked H-pair machines to every
   selected owner family. Complete positive branches and generic coNP upper
   already compile on the full original word language.
3. `reset:thm:circuits`: polynomial native graph generator and whole-word
   verifier/class transport. Main-required fragment is reset and its actual
   three-element generator; report H/policy circuit extensions are optional.
4. Prose: polynomial reset-table synthesis; original-core canonicalizer/comparator
   P=NP consequence; finish the reset-DAG and hard-third-observer class endpoints.
   The main substitution formula is complete; report-only substitution runtime
   is optional.
5. Finish definition/statement reconciliation, complete source/axiom/import
   audits and reproducible project checks. The historical obstruction target
   was rebuilt separately under its pinned Lean4.32.2 and standard-axiom audit.

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
