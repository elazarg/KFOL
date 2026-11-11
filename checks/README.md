# Current paper checks

`make check-python` runs the 33 entry points listed explicitly in the root
Makefile. The verification appendix cites each group and describes its finite
coverage. These are independent regression checks, not substitutes for Lean
proofs.

| Scripts in `checks/` | Current paper/report coverage |
| --- | --- |
| `check_choice.py`, `check_core.py`, `check_common_source.py`, `check_structure.py`, `check_symmetric.py` | Owned choice, contexts, bottom extensions, restricted views, winning-set families, collective choice and team refinement, tests, core extraction and common source |
| `check_fibers.py`, `check_general.py` | Unary contexts, ambiguity and fibers |
| `check_reset.py`, `check_forest.py` | Reset tables, antimatroids and forest models |
| `check_fragments.py`, `check_raw_pairs.py` | Hard fragments and role-count identities |
| `check_one_owner.py`, `check_owner_synthesis.py`, `check_owner_basis.py`, `check_owner_presentation.py`, `check_owner_finite_basis.py` | Owner guards, synthesis, generators, bases and the entire four-variable-theory obstruction |
| `check_chain_guards.py`, `check_mixed_policies.py`, `check_policy_families.py` | Selective reset and policy families |
| `check_protocols.py`, `check_interaction.py`, `check_connections.py` | Public profiles, disclosure and dependent-store models |
| `check_sealed_rounds.py`, `check_two_players.py`, `check_open_game_obstruction.py` | Round values, two roles and the scoped open-game refutation |
| `check_reset_circuits.py` | Shared reset circuits and their three-value test |
| `check_core_basis.py`, `check_core_obstruction.py`, `check_core_padded_crossing.py` | Seven-law basis, arity obstruction and padded-grid countermodel |
| `check_core_atomic.py`, `check_core_atomic_basis.py`, `check_core_conservative.py`, `check_core_unary_polynomials.py` | Retained atomic, conservative and unary-polynomial results |

`python3 checks/check_xpath.py` is an additional, optional TR regression using
`lxml`/libxml2’s actual XPath 1.0 engine. It checks the navigation compiler on
60,208 term/valuation pairs and an empty-input schema counterexample. It is
separate from the standard-library-only `make check-python` suite.

The other Python files are shared models imported by these entry points.
The four files `data/core-{small,six,seven,eight}-models.json` are fixed inputs
to the atomic-basis check of principal-ideal quotients, as described in the
verification appendix. No search program is needed to replay those checks.

Superseded candidate-basis, absorber/unitization and observer searches, their
unused helpers and their unused data were removed. Their sources remain in
git history at revision `c5723ac`. There are no `probe_*` entry points or
automatic glob that adds new exploration scripts to `make check`.
