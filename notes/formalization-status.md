# Active formalization status

The entire main-paper scope is proved: **22/22 main result rows**,
**74/74 required catalog rows**, and **17/17 required prose obligations**.
The [inventory](formalization-claims.json) is authoritative for scope.
Other report results remain optional and have their own evidence status.

Finite relatedness is now settled negatively for every fixed finite K≥3.
For every m, `Paper.core_not_finitely_related` gives an (m+3)-ary nonterm
operation with core interpolants on every m valuations;
`Paper.core_no_finite_relation_basis` rules out every finite defining family
of invariant relations. This does not rule out short structural laws with
unbounded quantification. See [the research target](research/core-functions/target.md).

| Audit entrypoint | Mathematical statements | Presentation |
| --- | ---: | --- |
| [Paper.lean](../Paper.lean) | 82 | Main text and the report claims it cites |
| [Report.lean](../Report.lean) | 73 | Further report results and proof ingredients |
| [Results/Certificates](../KFOL/Results/Certificates.lean) | 140 preserved contracts | Original full statements, including native machines, codecs and intermediate invariants |

Every root proof names one library theorem. Both root files have no semantic
definitions and end with a failing namespace axiom audit. The whole-project
axiom audit also checks private library helpers. The relocation manifest pins
all 140 previous complete signatures, so consolidation has not dropped or
weakened them.

The [audit guide](audit-guide.md) explains the human reading order. Natural
vocabulary is grouped in `Definitions/PaperAlgebra`, `PaperGames` and
`Complexity`, with their underlying mathematical definitions indexed separately. The report’s
navigation vocabulary is in `Definitions/Queries`; the zero extension and
regular representation are in `Definitions/Relational`.

| Definition surface | Theorem types | Semantic declarations | Source files | Written review units |
| --- | ---: | ---: | ---: | ---: |
| Paper | 82 | 678 | 40 | 362 |
| Report | 73 | 621 | 36 | 286 |

The slices overlap and exclude theorem proof bodies. These meaning indexes do
not replace the human comparison with the manuscript or the proof/axiom audits.

## Verification

The production integration checks are:

- `make check-lean`: literal façade and preservation checks, inventory,
  independent algebra build/import audit, Paper/Report and whole-source axiom
  audits, both definition indexes, actual negative audit fixtures and 102 strict
  Lean regressions.
- `make check-python`: the explicit 34 independent Python checks, mapped to the
  current paper in `checks/README.md` and the verification appendix.
- `make paper`: both manuscripts, with the main paper remaining 13 pages and
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

The zero extension is a commutative idempotent powerset semigroup with an
annihilating empty set, preserving union in both arguments. A general direct
representation theorem covers every finite powerset with an associative,
union-preserving product and zero. The owned-choice instance also works over
infinite role sets. Andréka's publisher abstract explicitly states the broader
DLOS reduct theorem; the report credits that abstract and uses direct proofs.

The nonfinite-basis result now covers C, A and A^sym for every finite K≥3.
Finite permutation envelopes retain the core countermodels' unbounded
actual-variable obstruction, with exact preservation and reflection of variety
membership. No residual-bound hypothesis is used. The main theorem, abstract,
results list and open-problems paragraph reflect this conclusion.

The report's dependent calculus, general real-QE/semialgebraicity, numerical
free-algebra counts and unused extensions remain outside main-paper completion.
The historical mixed-open-game obstruction keeps its separately pinned external
artifact. The earlier Std-only Lean tree is retired at revision `7014dbb`;
current production consists of KFOL and the two root audit entrypoints.

The core's singleton-output predicates now have a constructive classification
at every finite arity: monotonicity, unanimity, and a nonempty intersection of
every family of winning coalitions, one per owner. The independent conditions
are in `Definitions/CoreFunctions`; `Core/ProfileSynthesis` proves necessity
and synthesizes a term, and `Report.core_singleton_profiles` exports the full
statement. This does not classify the surviving members of ambiguous outputs.
The kernel-checked three-valuation persistence law additionally couples
singleton and ambiguous outputs, at every input arity and without restricting
extra owners. `Algebra/Monotone` proves ordinary inclusion monotonicity for
the full syntax. The independently checked ternary examples in
`notes/research/core-functions` separate these conditions from full
realizability, including a candidate that preserves the first law under
core substitutions and contexts.

The superseded atomic-cut recognizer remains proved in the library; the
report uses the row-deletion criterion below.
Canonical prime source-guard normal forms are now proved for the full
operations. A winner is supplied by one variable, tested against the other
inputs' nonobserver singleton statuses. There are exactly n K^n indexed
Boolean observations. `Definitions/CoreNormalForm` groups the passive statuses,
probes, sufficient prime guards and their meaning; `Core/SourceProbes` and
`Core/SourceNormalForm` prove reconstruction, canonicity and local synthesis.
The five complete statements retain the antichain clause. The main
discussion now explicitly asserts the normal forms, so their reconstruction
and equality statements reside in `Paper.lean`; the source decomposition,
probe count and local synthesis remain in `Report.lean`. The recursive recognition procedure for jointly realizable guard families
is also stated in `Paper.lean`. Its lack of auxiliary clauses does not make
it a short structural characterization.

The one-owner basis now has optimal variable bound five: thirty-six native
laws, with five-variable exchange replacing the six-variable action-band
axiom. The six-element countermodel rules out every four-variable basis;
the relative conservative bound stays four.

The report retains recognition by repeated singleton tests. The superseded
cut-saturation and source-interior presentations are retired from the report;
their library proofs remain available. Recognition is distinct from the structural characterization question. The
new cyclic obstruction settles finite relatedness negatively.

Pairwise compatibility is now proved insufficient uniformly for every K ≥ 3.
`Core/PairwiseInterpolation` defines a repeated-value patch of three short core
operations. Every two valuations have a common candidate term, so the patch
preserves all binary invariant relations and is monotone and idempotent. Its
singleton profiles equal those of one explicit core term. Three-valuation
persistence nevertheless excludes a global realization. No finite enumeration
is used. `Report.core_binary_interpolation` states the general relational bridge;
`core_pairwise_obstruction` states all properties of the uniform counterexample.
`Core/RelationalInterpolation` extends the relational bridge to every finite
arity and proves the coherent-patch construction. `Core/FourValuation` derives
a four-row persistence law from six invariant atomic implications.
`Core/TernaryInterpolation` uses four short patches to prove three-point
interpolation, preservation of every ternary invariant relation, exact core
singleton profiles and non-realizability. These uniform symbolic proofs replace
the second finite operation's enumerated separating relation. Three further
complete claims are in `Report.lean`. The independent research checker generates
both patches from their formulas and retains the exhaustive unary checks.

`Core/LocalNormalForm` proves that ternary relational tests already force
source decomposition, canonicality and correct prime-guard interpretation at
finite arity. No role finiteness is used for source decomposition itself.
`Core/ProfileEnvelope` constructs each core profile's greatest completion by
reset against the union of all inputs. Core realizability within one profile
class is not order-convex: explicit core lower and upper bounds contain the non-core
ternary obstruction between them. These three further report claims are kernel-checked.

`Definitions/CoreGraph` now gives a structural representation at every arity:
finite occurrence graphs exclude rainbow triangles and complementary
two-colored four-vertex paths, and maximal monochromatic cliques determine
singleton blocking and source survival. `Core/ColoredGraphDecomposition`
proves the graph cut theorem; the semantic and reconstruction modules prove
the full representation in both directions. `Core/ColoredGraphGuards` identifies
jointly realizable prime families with the prime clique guards of one such
graph. These two new Report statements use no enumerated clone certificate
or outside theorem hypothesis. The operation theorem also allows infinite role
and variable types, assuming a nonempty role type.

The ternary obstruction has short separate realizations of each named
owner's full view. Thus, for three roles, even realizability on every individual
view does not ensure one common realization. The graph witness need not be
unique. The recursive row-deletion test recognizes the same guard families.
Neither representation settles the short intrinsic characterization.

`Core/MinorantObstruction` proves a four-row cover law and its atomic bridge
uniformly in all additional roles and arbitrary groups of variables.
`Core/MinorantPatches` gives four explicit four-input core operations agreeing
three at a time. Their common value has no pointwise core minorant at all,
although it preserves every ternary invariant relation and therefore has a
correct canonical source-guard form at finite role sets. The complete existential
claim is `Report.core_three_local_without_minorant`. Its helpers are private;
it adds no semantic definitions to the audit surface.

`Core/MinorantFive` raises the symbolic cover to five rows.
`Core/MinorantFiveCertificate` checks five explicit patches on all 1,024 formal
named-atom/passive-marker assignments with kernel `decide`. `Core/StatusModel`
proves that replacing those markers by arbitrary passive winner sets preserves
union and the named owned choices. `Core/MinorantFivePatches` connects the
certificate to actual core terms and proves the existence of a five-input,
four-point interpolable operation with no core minorant, uniformly for arbitrary
role types containing three distinct roles. The complete existential statement
is `Report.core_four_local_without_minorant`; it introduces no new semantic
definitions in the report's theorem types.

`Core/SixValuation` checks a finite owner-elimination certificate for the
six-row persistence law. `Core/SixPatchCertificate` checks six factored core
expressions on the formal status model, and `Core/FivePointInterpolation`
proves five-point interpolation and preservation of every invariant relation
of arity at most five, while excluding a global core realization. The
operation has an actual core minorant. This holds for every role type
containing three distinct roles, with no finiteness hypothesis. For finite
role types, `exists_five_local_profile_fiber_nonconvex` strengthens it to a
non-core operation between core lower and upper bounds, all sharing exactly
the same singleton-output predicates. The base result is
`Core.exists_five_local_noncore`; the stronger finite-role statement is
`Report.core_five_local_profile_obstruction`. The
independent five-point checker uses the exact 133-operation Lean expressions;
the superseded discovery family has been removed.

`Definitions/CoreInterpolation` gives the direct hereditary test. A query
contains upper bounds at a finite set of rows, singleton demands, and an
optional positive membership. Its three conditions use rainbow intersections
(one demand per owner), a positive column, and escape from forced competing
singletons. Each recursive call makes one allowed singleton demand and erases
that row from the bound set. Empty rows, variables, bounds and conflicting
demands use the same definitions.

`Core/BoundedGeneration` proves that bounded core tuples are generated by
bounded input columns and tuples atomic at a bounded row. `Core/AtomicInterpolation`
proves the exact singleton/positive condition using least demanded profiles and
their maximum completion. `Core/Peeling.peels_iff` combines these results by
strict induction on the number of bounds, and `recognizes_iff` joins positive
witnesses to recognize full raw tables. `Core/SourcePeeling` needs only negative
source-probe bounds and the positive observer bits. The recursive guard-table test is `Paper.core_guard_peeling`; the general
interpolation theorem is `Report.core_peeling_interpolation`. The main
discussion states the parametric obstruction and its finite-relation
consequence. `Core/CrownBoolean` proves the cut-cycle separation lemma;
`Core/CrownPatch` builds greatest profile completions, and
`Core/CrownBasePatch` unions them into an actual core patch. Rotation gives
one patch for each missing edge. `Core/CyclicPersistence` proves the
permutation-cycle winner law, using a finite union of lattice polynomials
in the observer quotient. `Core/CrownObstruction` combines the patches and
the violated law, while `Core/FiniteRelationObstruction` handles arbitrary
finite families of relations, including nullary relations and empty families.
`Core/CrownFullSyntax` proves idempotence and applies core extraction to
exclude every full-language realization; its finite-family theorem extends
nonfinite relatedness to both expansions with constants and role switches.
The only new semantic vocabulary is grouped in `Definitions/CoreCrown` and
the relation-preservation predicate in `Definitions/CoreFunctions`.

`tests/CorePeeling` checks the nullary and empty-bound boundaries, conflicting
queries, and same-owner demands where no input column suffices but an actual
owned-choice term does. The independent stdlib `peeling.py` compares the test
with unpruned subpower generation at three and four roles, including the exact
six-row obstruction. It does not use generated subpowers inside the recognizer.

The general owner-elimination calculus remains a library tool for the older
six-row persistence proof. Its complete presentations and sampled-row tests
are no longer repeated in the report after the cyclic construction supersedes
that particular recognition presentation.
