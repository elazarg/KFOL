# Active formalization status

The entire main-paper scope is proved: **22/22 main result rows**,
**67/67 required catalog rows**, and **17/17 required prose obligations**.
The [inventory](formalization-claims.json) is authoritative for scope.
Other report results remain optional and have their own evidence status.

| Audit entrypoint | Mathematical statements | Presentation |
| --- | ---: | --- |
| [Paper.lean](../Paper.lean) | 79 | Main text and the report claims it cites; 631 lines |
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
| Paper | 79 | 654 | 38 | 345 |
| Report | 73 | 645 | 35 | 293 |

The slices overlap and exclude theorem proof bodies. These meaning indexes do
not replace the human comparison with the manuscript or the proof/axiom audits.

## Verification

The production integration checks are:

- `make check-lean`: literal façade and preservation checks, inventory,
  independent algebra build/import audit, Paper/Report and whole-source axiom
  audits, both definition indexes, actual negative audit fixtures and 99 strict
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

Atomic-cut recognition and synthesis are now proved for entire operations
at every finite arity, including arity zero. `Definitions/CoreFunctions`
specifies bounds and local rules independently of terms; `Definitions/FiniteHorn`
specifies their finite saturation. `Algorithms/FiniteHorn` proves the uniform
round limit, and `Core/Cuts` proves soundness, completeness and one common
witness for all derived memberships. The four report statements include the
round bound K*m*(K+2)^m and synthesis across every sampled valuation at once.
Canonical prime source-guard normal forms are now proved for the full
operations. A winner is supplied by one variable, tested against the other
inputs' nonobserver singleton statuses. There are exactly n K^n indexed
Boolean observations. `Definitions/CoreNormalForm` groups the passive statuses,
probes, sufficient prime guards and their meaning; `Core/SourceProbes` and
`Core/SourceNormalForm` prove reconstruction, canonicity and local synthesis.
The five complete statements retain the antichain clause. The main
discussion now explicitly asserts the normal forms, so their reconstruction
and equality statements reside in `Paper.lean`; the source decomposition,
probe count and local synthesis remain in `Report.lean`. Both excluded
ternary functions also have sourcewise reconstructions, so the remaining
main-text question concerns a concise intrinsic characterization of jointly
realizable functions, beyond the exact finite recognition procedure.

The one-owner basis now has optimal variable bound five: thirty-six native
laws, with five-variable exchange replacing the six-variable action-band
axiom. The six-element countermodel rules out every four-variable basis;
the relative conservative bound stays four.

Direct joint compatibility is now checked on the n K^n source observations.
`Core/SourceCompatibility` proves a monotone, contractive, idempotent interior
operator specified by finite Horn rules. Every nonzero result has one common
term witness and is the greatest realizable coefficient array below its input.
Canonical guard families are realizable exactly when their array is nonzero
and fixed by this operator. Three complete statements are in `Report.lean`.
This refines the algorithmic criterion. The main-text question asks for an
intrinsic characterization comparable to singleton-profile admissibility;
that stronger question is not declared solved.

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
view does not ensure one common realization. The graph witness is not unique;
a direct condition on canonical guard tables, without an auxiliary realization,
is still not proved.

`Core/MinorantObstruction` proves a four-row cover law and its atomic bridge
uniformly in all additional roles and arbitrary groups of variables.
`Core/MinorantPatches` gives four explicit four-input core operations agreeing
three at a time. Their common value has no pointwise core minorant at all,
although it preserves every ternary invariant relation and therefore has a
correct canonical source-guard form at finite role sets. The complete existential
claim is `Report.core_three_local_without_minorant`. Its helpers are private;
it adds no semantic definitions to the audit surface.
