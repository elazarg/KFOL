# All-arity core functions

Exact recognition, synthesis and canonical prime source-guard normal forms
are proved. Jointly realizable families now have an exact structural graph
representation, described below. A direct criterion on the canonical guards
without an auxiliary realization remains open. Pairwise compatibility and correct singleton profiles together
are proved insufficient, uniformly for every K ≥ 3. Three-point interpolation
is also proved insufficient, with a symbolic four-valuation persistence law.
At four inputs it need not even leave one pointwise core minorant: four short
patches agree three at a time, while their common value violates a four-row
cover law. This stronger obstruction is proved in `Core/MinorantPatches` and
restated as `Report.core_three_local_without_minorant`.
Five explicit five-input patches raise this to four-point interpolation,
still without a core minorant, in `Core/MinorantFivePatches`; the root statement
is `Report.core_four_local_without_minorant`. The finite status certificate is
connected to arbitrary role types by the union-extension lemmas in `Core/StatusModel`.

The independent `four-point-candidate.py` reproduces those witnesses and their
seven-value maximality. `five-point-candidate.py` checks a further six-patch
example at K=3: it is five-point interpolable, has a core minorant, and violates
a six-row persistence law. This latter example is research evidence, with no
Lean theorem yet. `transport-orders.md` records the conditional owner-elimination
criterion suggested by its separating relation; no completeness claim is made.

## Structural graph representation

`Definitions/CoreGraph` specifies finite graphs whose vertices are independent
input occurrences, labeled by variables. Edges have owner colors. Exclude
rainbow triangles and the two-colored four-vertex path together with its
complement. A vertex supplies winner k when its input contains k; it survives
when, for each other owner r, some maximal r-clique through it has no other
vertex whose input is {r}.

`Core/ColoredGraphRealization.represents_iff` proves that the resulting operations
are exactly all core term operations. `Core/ColoredGraphGuards.guard_realization_iff`
gives the equivalent prime-source-family criterion. The proof includes the
finite colored-graph decomposition theorem, clique recurrences and reconstruction
of one common term. It works without enumerating the operation clone. The
operation theorem allows arbitrary variable and nonempty role types.

This is a structural representation theorem: the graph witness need not be
unique, while the prime source guards remain canonical. It does not establish
a fixed relational arity bound or eliminate the auxiliary graph.

## Profiles and source-guard normal forms

`Core.exists_term_iff_admissibleProfiles` classifies singleton-output predicates
at every finite arity: monotonicity, unanimity and a common variable in every
selection of one winning coalition per owner. `Core/ProfileSynthesis` constructs
a core term realizing every admissible family. Singleton profiles do not specify
the full function: the two reset associations have equal profiles and support
but different ambiguous outputs.

`Core.Sources.membership_iff_source` reconstructs a possible winner k from one
supplying variable j at a time. The probe sets j to {k}; every other input is
another owner's atom or neutral ambiguity I\{k}. No finiteness assumption is
needed for this decomposition. With K owners and n variables its observation
index has exactly n K^n elements.

Each source coefficient is monotone on the passive poset. Its canonical form
contains all inclusion-minimal sufficient exclusion guards.
`normalForm_correct` reconstructs the operation, and `normalForm_eq_iff` proves
canonicity. A projection has just an empty guard at its source.
`exists_guard_family_term` realizes any nonempty guard family at one chosen
source by a union of owned-choice spines; it does not prescribe the others.
The vocabulary is centralized in `Definitions/CoreNormalForm.lean`.

## Three-point tests already force the normal form

`Core/LocalNormalForm` extends source decomposition to every three-point
interpolable operation at finite arity. Fix the passive statuses and vary the
set of active sources. Core membership preserves the union of two source
sets; interpolation at the three relevant valuations transfers this law to
the operation. An empty source set contributes no winner. Finite additivity
therefore reduces membership to one source. Two-point interpolation identifies
that single-source observation with its canonical probe and transfers
coefficient monotonicity.

The resulting prime guards are canonical for their own reconstructed
coefficients and their meaning is the original operation. The decomposition
allows infinitely many roles; guard finiteness additionally assumes finitely
many roles. The regression instantiates decomposition at Role=ℕ and canonical
reconstruction for the non-core four-role obstruction.

## Greatest completions and gaps in core realizability

For a core term t, let U be the union of every input variable and set
`t^max = U δ t`. Reset preserves t's atomic outputs and returns U on every
ambiguous output. This is itself a core term, and is greatest among all
operations with those singleton outputs and provenance, whether or not they
are terms. `Core/ProfileEnvelope.exists_profile_maximum` proves this without
assuming the ambient variable type is nonempty; the core term supplies a leaf.

Even inside one profile fiber, the core operations are not order-convex.
For the four patches below, the core term

```
G = H ⋆_c (H ⋆_a (T ⋆_a (X ⋆_c Z)))
```

has F's singleton profiles and satisfies G ≤ F. Its greatest profile
completion E satisfies F ≤ E, but F is not a core operation. All of this is
proved uniformly for every finite role type with three distinct roles.
`Report.core_local_normal_forms`, `core_profile_maximum` and
`core_profile_nonconvexity` state the complete results. These results separate
representability by source guards and bounds within a profile fiber from
actual joint realizability.

## Pairwise compatibility and the uniform obstruction

`Core.pairwiseInterpolable_iff_preservesBinary` identifies simultaneous
interpolation at any two valuations with preservation of every binary relation
closed under coordinatewise owned choice. This includes unary tests through
diagonal relations. It allows empty invariant relations and arbitrary role and
variable types.

`Core.Pairwise` constructs an explicit operation from three short core terms.
Writing H = X ⋆_b Z, the candidates are

```
P = Y ∪ H
Q = H ⋆_a (Y ⋆_c Z)
R = (X ⋆_a Y) ⋆_c H.
```

At least two agree at every input. Their repeated-value patch M has one common
candidate interpolating any two valuations. It is monotone, idempotent, and has
exactly the singleton profiles of Q ⋆_b R. Nevertheless, its values

```
M({a,b}, {b},   {b})   = {b}
M({b},   {b,c}, {a,b}) = {b,c}
M({a},   {b},   {c})   = {a,c}
```

violate `Core.three_valuation_persistence`. Coherence, two-point interpolation,
profile equality and non-realizability are proved symbolically in Lean for
any three distinct roles, with all additional roles unrestricted.
`Report.core_pairwise_obstruction` states the complete result. The numerical
first counterexample has been retired; the research checker generates M from
its formula.

## Three-point interpolation is insufficient

The stronger obstruction also has a complete uniform Lean proof. Put

```
H = X ⋆_b Y,           T = Y ⋆_a Z,
P₀ = H ⋆_c (H ⋆_a T),
P₁ = Z ∪ (H ⋆_a (X ⋆_c Z)),
P₂ = X ∪ (H ⋆_c T),
P₃ = H ⋆_c (Y ⋆_a (Z ⋆_c (X ⋆_a Y))).
```

At least three candidates agree at every valuation, uniformly in all other
roles. Their common value F is P₀ if P₀=P₁ and P₂ otherwise. Each valuation
excludes at most one candidate, so any three valuations have a common
candidate term. `Core/RelationalInterpolation` proves the general n-point
interpolation/relational-preservation equivalence, including n=0 and empty
relations, and the (n+1)-patch argument. Thus F preserves every ternary
invariant relation. Its singleton profiles are those of the actual core term
`((X ∪ Y) ⋆_a Z) ⋆_c (X ∪ Y)`.

Nevertheless, F is not a core term:

| X | Y | Z | F(X,Y,Z) |
|---|---|---|---|
| {a,c} | {b} | {a} | {a,b,c} |
| {a,b} | {a} | {b,c} | {a,b} |
| {a} | {b} | {c} | {b,c} |
| {b} | {c} | {a} | {a,b} |

`Core/FourValuation` proves that the three exclusions in the last three rows
force c to be absent in the first row for every core term. The proof couples
six binary atomic implications with one membership implication. For example,
the relation `A={a} → (B={a} or c∈B)` is invariant: its consequent is a
subalgebra and absorbs arbitrary operands under the antecedent's owner.
Together these implications prevent any of the three negative rows from
hiding an absorption that would let c survive in the first row.

`Core/TernaryInterpolation` proves coherence by the 64 input status cases,
the exact profiles, the four evaluations, and non-realizability. All additional
roles are unrestricted; there is no role finiteness assumption. No finite
relation enumeration or native computation enters these proofs. The original
25-node patch graph and 148-element relation have been replaced by the short
formulas and the symbolic argument.

`Report.core_local_interpolation`, `core_four_valuation_persistence` and
`core_ternary_obstruction` repeat the complete claims. The Python regression
independently evaluates the formulas, checks the status cases and all the
properties below, and computes the maximum bounded output on the four rows
as (3,3,6,3). It generates the operation rather than trusting a supplied table.

## Exact saturation and the greatest realizable minorant

`Core.Cuts.recognizes_iff` proves exact simultaneous interpolation on any finite
nonempty family of valuations. `operation_iff` applies it to entire operation
tables, including arity zero. `maximum_of_saturated` gives one common witness
for every reachable membership at a bound; `round_bound` proves the stopping
bound K*m*(K+2)^m. The rules and finite saturation are specified independently
of terms in `Definitions/CoreFunctions` and `Definitions/FiniteHorn`.

`Core.Sources.interior` instead imposes one bit constraint per source probe:
a negative bit forbids its observer and a positive bit permits every winner.
`interior_iff_witness` characterizes each retained bit by a term obeying all
negative constraints. The operator is monotone, contractive and idempotent.
Every nonzero result has one common term and is the greatest realizable array
below its input; zero means no term obeys all negative constraints.
`guard_fixed_iff` gives direct compatibility as canonicality, nonzero array,
and equality with its interior. This remains a saturation criterion.

The independent Python maximum-value regression is not asserted to be an
executable implementation of the Lean Horn system. `tests/CoreCuts.lean`
checks incompatible sampled rows and the nullary boundary; the source tests
check the empty array, a positive inconsistent unary array, and arity zero.

## Reproducing the finite research checks

The standard-library Python checker independently verifies both explicit
patch operations:

```
python3 notes/research/core-functions/check.py
```

For both it checks idempotence, inclusion monotonicity, the exact singleton
profiles, provenance on each status cell, common-source tests for every finite
family of disjoint regions, source reconstruction, and every substitution of
three of the 131 unary polynomial functions. Identity reflection also holds:
a full-support core term can become unary identity only when each input is
identity, by idempotent extraction.

An optional C++20 regression also checks all binary invariant relations and all
full role-switching unary substitutions:

```
python3 notes/research/core-functions/check.py --full-unary
```

`full_unary.cpp` checks the closure generated by every triple of pairs on the
seven-value carrier, with every argument order: 117,649 ordered triples.
For the four-patch operation this is redundant with its stronger three-point
interpolation property, and serves as an independent regression.
It independently enumerates the 751 unary normal forms and compares them with
the generated unary clone. Both operations then pass all 423,564,751 unary
substitution triples. These numerical results are separate from the uniform
Lean proof and do not claim Lean-verified enumeration.
