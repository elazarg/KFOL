# Proof-mining session

The session produced four mathematical improvements, all proved in Lean and
integrated into the technical report. The main paper's scope is unchanged.
Root `Paper.lean` restates the six added public propositions in full.
No new independent semantic definitions were needed.

| Hidden concept | Proved improvement | Public statements |
| --- | --- | --- |
| Breadth of the owned-choice semilattice | A nonempty family indexed by any type has a support of at most K−1 values for finite K≥2. Its fold is a mathlib `IsLUB`. For actual continuation games the support compiles to a binary core game with the same full-profile SPE winners. Nonowner terminal actions attain the bound. | `public_choice_small_support`, `public_choice_support_sharp` |
| Canonical tables as semantic complexity invariants | The linear shared selector circuit has exactly 2^n marker guards, each with n+1 prerequisites. Every equivalent reset tree has at least 2^n marker occurrences, 2^n+1 leaves and 2^(n+1)+1 total nodes. The marker occurrence bound is optimal. | `reset_circuit_tree_succinctness` |
| Threshold profiles as codes | N actual Boolean comparison contexts distinguish N+1 reciprocal games. Any summary preserving just those observations is injective and needs N+1 states, without a compositionality assumption. | `boolean_threshold_state_lower_bound` |
| Scalar values as observable order | Every finite game using only a designated pair of effective players and terminal winners is observed completely by Boolean contexts and one third role's possible victory. A proved countable family of one-hole rational comparisons suffices. These probes recover the scalar order as well as equality. | `pair_game_boolean_full_abstraction`, `scalar_rational_observation_order` |

The support selection is made after the continuation values are fixed. It is
not a uniform pruning of game syntax under all substitutions, nor a construction
of arbitrary infinitely recursive games. Only the root action family may be
infinite. The semilattice theorem explicitly selects the owned-choice order;
ordinary subset inclusion is a different order on the same carrier.

The general real-valued separator needs only actual singleton two-winner law
hypotheses, rather than scalar syntax. The pair-game theorem derives those
hypotheses from constant-sum uniqueness. Other roles must have singleton menus
inside the components; restricting terminal winners alone would not ensure
uniqueness. The contexts may introduce the third observer. The exact probe
threshold is x≤t with t<1, including a tie at zero. No claim that irrational
closed scalar games exist is needed.

The circuit bounds apply to every semantically equivalent reset tree, including
trees using other input names. They do not give a lower bound on arbitrary
expanded-signature terms or claim that the displayed unfolding minimizes total
node count. Optimality is proved for marker occurrences.

Proof structure improved along with the statements:

- Exact minimal-guard exhaustiveness replaces the former cardinality-only
  argument; the old exponential-table bound is now a one-line corollary.
- Generic semantic bounds in `KFOL/Reset/SemanticBounds.lean` transport canonical
  guard counts to occurrence and leaf bounds for any equivalent reset tree.
- The Boolean impossibility proofs share one reciprocal-code injectivity lemma.
  Their two duplicated threshold arguments were removed.
- The old scalar separator and scalar full-abstraction interfaces are preserved
  as corollaries of the real singleton-law separation theorem. The report's
  scalar corollary now follows the more general pair-game argument.
- Pure algebra remains independent of GameTheory and ComplexityLib. Strategic
  interpretation and actual sequential-equilibrium observation stay in their
  respective import branches.

Regression coverage includes infinite Nat action indices, the sharp four-role
terminal example, insufficient two-state threshold codes, endpoint/tie probes,
exact guard payloads, and semantic bounds for alternative circuit trees.
The whole-project axiom audit includes all new modules, and the theorem-type
surface index includes all six public additions.
