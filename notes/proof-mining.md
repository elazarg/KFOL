# Proof-mining session

The initial session produced four mathematical improvements, all proved in Lean
and integrated into the technical report, with six complete new Paper statements.
The subsequent nested-quantifier extension adds two more public statements,
one central semantic definition module, and the strengthened assertion in
Section 2. The report's support proposition is strengthened in place.
The audit-surface refactor subsequently grouped the main statements in
`Paper.lean` and further mathematical statements in `Report.lean`; every
original complete contract remains in `KFOL.Results` and is recorded in the
relocation manifest.

| Hidden concept | Proved improvement | Established contract names |
| --- | --- | --- |
| Breadth of the owned-choice semilattice | A nonempty family indexed by any type has a support of at most K−1 values for finite K≥2. Its fold is a mathlib `IsLUB`. The subsequent nested-quantifier extension prunes every finite-depth public game with arbitrary history-dependent nonempty action types to at most K−1 original actions per retained node, preserving each matched subgame's SPE winners and giving a finite binary representation. Nonowner terminal actions attain the bound. | `public_choice_small_support`, `public_choice_support_sharp`, `arbitrary_public_quantifier`, `finite_depth_quantifier_reduction` |
| Canonical tables as semantic complexity invariants | The linear shared selector circuit has exactly 2^n marker guards, each with n+1 prerequisites. Every equivalent reset tree has at least 2^n marker occurrences, 2^n+1 leaves and 2^(n+1)+1 total nodes. The marker occurrence bound is optimal. | `reset_circuit_tree_succinctness` |
| Threshold profiles as codes | N actual Boolean comparison contexts distinguish N+1 reciprocal games. Any summary preserving just those observations is injective and needs N+1 states, without a compositionality assumption. | `boolean_threshold_state_lower_bound` |
| Scalar values as observable order | Every finite game using only a designated pair of effective players and terminal winners is observed completely by Boolean contexts and one third role's possible victory. A proved countable family of one-hole rational comparisons suffices. These probes recover the scalar order as well as equality. | `pair_game_boolean_full_abstraction`, `scalar_rational_observation_order` |

The support selection is made after the original continuation values are fixed
and may depend on the complete history. The nested-quantifier extension removes
the earlier restriction to one arbitrary root above finite binary continuations:
all quantifier occurrences may now have infinite action sets. The main-paper
statement assumes a uniform finite depth; the library construction works for
all well-founded public trees. The semilattice theorem explicitly selects the
owned-choice order; ordinary subset inclusion is a different order on the same
carrier.

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

Regression coverage includes nested infinite, dependent witness domains,
whole-player off-path deviations, the sharp four-role terminal example, insufficient two-state threshold codes, endpoint/tie probes,
exact guard payloads, and semantic bounds for alternative circuit trees.
The whole-project axiom audit includes all new modules. The separate Paper and
Report theorem-type indexes record their current public presentations.

## Query-language investigation (technical report only)

The report now includes `sections/appendix-queries.tex`, located after unary
contexts; its intersection corollary is placed beside the semilattice trace. The positive connection is exact, not just an analogy: public terms
compile into two-way Core XPath on height-two valuation trees, preserving and
reflecting equivalence on that schema. Parent navigation lets each child query
occur once; linear nonowner tests give the proved bound `12 * t.size ^ 2`.
No descendant axis, recursion, node-identity comparison or counting is needed.
The independently defined `Path.Holds`/`Test.Holds` semantics uses ordinary
relations and predicates.

One raw owned choice plus union also embeds faithfully in binary relations on
`Option Role`, preserving actual relation union and composition. This regular
representation is owner-specific and is not the document child relation.
Its existence does not follow from a general theorem: not every
semilattice-ordered semigroup is representable by union and composition, and
the representable ones are not finitely axiomatizable (Andréka and Mikulás,
Algebra Universalis 66, 2011, Section 3). The direct construction uses K+1
points and is kernel-checked.
Reset plus union has no such faithful representation: reset fails right
distributivity. These generic results need no role finiteness assumption.

Conversely, Core XPath selects the intersection of two input relations, whereas
even full winner terms with constants and permutations cannot do so on all
inputs with nonempty intersection. Idempotency eliminates the extra syntax,
and two ambiguous inputs with atomic intersection give the contradiction.
This gives an inexpressibility boundary for the term language. Reset tables
provide canonical guarded forms on the chosen document schema.

The XPath comparison follows the two-sorted semantics in
[ten Cate–Litak–Marx (2010)](https://doi.org/10.1016/j.jal.2009.09.002).
Equivalence is claimed only on the specified nonempty-input document schema.
The Lean regression explicitly rejects the analogous identity on an empty-input
document, and catches a guard evaluated under the candidate output instead of
at its parent. The optional lxml/libxml2 regression independently executes
60,208 compiled term/valuation cases, including all nonempty valuations at
K=3/three inputs and K=4/two inputs. It also checks the empty-input example.
