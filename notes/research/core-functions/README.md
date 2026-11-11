# All-arity core functions

Exact recognition, synthesis and canonical prime source-guard normal forms
are proved. A concise intrinsic description of jointly realizable families
remains open. Pairwise compatibility and correct singleton profiles together
are proved insufficient, uniformly for every K ≥ 3. A stronger research
certificate rules out three-point interpolation as well. The finite relation
and the symbolic coherence calculation have not been formalized in Lean.

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

`threewise.json` specifies four ternary core terms P₀,…,P₃ as a shared,
topologically ordered expression graph. A `var` node is an input, a `choice`
node applies the indicated owner's choice, and a `union` node is derived
neutral union. Values are bitsets 1 through 7 for the nonempty subsets of
{a,b,c}. The graph has 25 nodes; its four roots are listed in `patches`.
There is no supplied operation table: the checker evaluates the terms on all
343 valuations and generates it.

At every valuation, at least three of the four terms agree. Define F to be
their common value; equivalently, take P₀ when P₀=P₁ and P₂ otherwise. Every
valuation excludes at most one candidate, so any three valuations have a
common candidate. Consequently F preserves **every ternary invariant
relation**: given three valuations whose input columns belong to such a
relation, use their common candidate term and closure under core operations.
The same argument covers relations of smaller positive arity by repetition.

Nevertheless, F is not a core term. Its four recorded evaluations are

| X | Y | Z | F(X,Y,Z) |
|---|---|---|---|
| {a,c} | {b} | {a} | {a,b,c} |
| {a,b} | {a} | {b,c} | {a,b} |
| {a} | {b} | {c} | {b,c} |
| {b} | {c} | {a} | {a,b} |

The recorded 148-element quaternary relation contains the three input
columns, is closed under every coordinatewise owned choice, and excludes
the output column (7,3,6,3). Structural induction therefore excludes a core
term; exhaustive generation of the relation is unnecessary. The checker
also independently runs the cut propagation on these four rows: the
maximum bounded output is (3,3,6,3), which misses c in the first row.

This replaces the weaker 63-element ternary obstruction. It passes all the
previous example's additional checks, including persistence in every owner
order, all common-source tests, and the unary substitution tests below.
These additional tests are finite computations at K=3, not Lean theorems.

The interpolation obstruction itself extends to any role type with three
distinct roles. For coherence, split each input into four statuses: {a},
{b}, {c}, or passive (any other nonempty set). Normalize every expression as
a formal union of distinguished atoms and tagged passive inputs. A union
containing a passive input cannot equal one of those three atoms, so choice
tests during normalization are exact and remain exact under interpretation.
The checker verifies that three patches have identical formal unions on
each of the 4³ status cells. Thus three patches agree under every
interpretation, even with infinitely many additional roles. Embed the
recorded relation using a,b,c. It is also union-closed, which the checker
verifies directly; any additional owner's choice acts as union on it.
The same four rows therefore still exclude a global core term.

This is a symbolic proof schema supported by finite checks. It supplies no
completeness theorem for four-point tests, nor the requested intrinsic
characterization of jointly realizable source-guard families.

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

The standard-library Python checker verifies both the explicit patch and the
retained finite operation:

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
