# All-arity core functions

Canonical prime source-guard normal forms and exact recursive recognition
are proved at every finite arity for finite role sets with at least three
owners. Row deletion gives a recursive test of joint realizability from the
guard table and its fixed source probes, proved in `Core/Peeling` and
`Core/SourcePeeling`. A short structural characterization remains open.
[peeling.md](peeling.md) gives the equations and their proof; the independent
stdlib checker is `peeling.py`.

Finite relatedness is now disproved for every fixed finite K≥3: for each m,
`Core.Crown.exists_local_obstruction` gives an (m+3)-ary nonterm operation
with a common core interpolant on every m valuations. The cycle construction
and its limits are summarized in [target.md](target.md). The sharper
`Report.core_exponential_locality` gives an exact threshold: 2d inputs can
pass all 2^d-point tests and fail at 2^d+1 points. Its Gray-cycle construction
and full-winner patches are proved symbolically in Lean; see
[exponential-crowns.md](exponential-crowns.md).

Closed boundary/no-trap conditions now present every invariant relation in
`Core/Hypergraphs`. This gives a complete infinite obstruction basis, still
with auxiliary clutters. [global-characterization.md](global-characterization.md)
records the remaining direct-guard target and the research branches, including
[canonical essential extensions](essential-extensions.md) and
[pointed obstruction normalization](pointed-obstructions.md).

Local tests do not suffice even within a fixed singleton-profile fiber.
Pairwise, three-point and four-point interpolation obstructions are proved
uniformly for every role type containing three distinct owners. The four-point
obstruction has no pointwise core minorant. Six explicit five-input patches
raise the non-realizability obstruction to five-point interpolation in
`Core/FivePointInterpolation`: `Core.exists_five_local_noncore` gives a
five-point interpolable non-core operation above an actual core minorant,
without assuming that the role type is finite. For finite role types,
`Core.exists_five_local_profile_fiber_nonconvex` strengthens this to an operation
between core lower and upper bounds with the same singleton profiles. The
operation preserves every invariant relation of arity at most five.

The independent `four-point-candidate.py` reproduces the four-point witnesses
and their seven-value discovery maxima. `five-point-candidate.py` checks the
exact factored expressions used by the uniform five-point Lean theorem,
including all formal passive-marker cells. `transport-orders.md` records the
complete clause calculus used to prove its six-row persistence law.

## Recursive recognition on the canonical probes

`Core.Interpolation.peels_iff` characterizes fitting upper bounds, exact atomic
demands and one optional positive membership. The recursion first checks
bounded projection columns or deletes one bounded row and demands an allowed
atom there. Rainbow selections of atomic demands enforce the common-source
profile condition. Additional one-demand positive tests keep every wrong
singleton profile from being forced at the queried row. The recursion's
rank is the number of bounded rows.

`Core/BoundedGeneration` proves the bounded generator decomposition;
`Core/AtomicInterpolation` reduces atomic and one-positive interpolation to
profiles; `Core/Peeling` combines them. `recognizes_iff` handles complete raw
target tables, including empty coordinates and empty rows, while
`operation_iff` characterizes entire operations at every finite arity.

`Sources.guard_table_iff_negative_peels` gives the canonical guard criterion.
Bound precisely the negative source probes by the complement of their
observer. Require base feasibility and the positive test for every true
source bit. Completeness supplies bounded terms for these tests; their finite
union realizes the coefficient array, and canonicity identifies the prime guards. `guard_table_iff_peels` gives the
same criterion using the full raw probe meaning. No auxiliary clause family
or occurrence graph is an input to either test. Empty variables are rejected
by the empty rainbow challenge.

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
`Core.exists_five_local_profile_fiber_nonconvex` gives actual core operations
G and E and a non-core operation F with G ≤ F ≤ E. All three have the same
singleton-output predicates, and F is five-point interpolable and preserves
every invariant relation of arity at most five. This strengthening holds for
every finite role type containing three distinct roles; clipping by reset
against the lower core term preserves the critical separation.

`Report.core_local_normal_forms`, `core_profile_maximum`,
`core_profile_nonconvexity` and `core_five_local_profile_obstruction` state these
results. They separate correct source-guard interpretation and bounds within
a profile fiber from actual joint realizability.

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

## Complete owner-elimination certificates

`Core/OwnerElimination` proves simultaneous-induction soundness of checked
membership clauses and their owner orders. `Core/OwnerEliminationComplete`
proves completeness: with three distinct owners, every finite choice-closed
relation has a finite checked clause presentation. Union is then term-definable,
and these presentations separate every tuple outside the generated relation.
`finite_sample_iff_checked_clauses` characterizes simultaneous interpolation,
and `truth_table_iff_checked_clauses` applies it to whole operations. Roles and
sample rows are finite; the finite-sample theorem permits arbitrary variable
types, including the empty type.

`Core/SourceCertificates` also retains the clause presentation on source
probes. Row peeling gives the recursive recognizer above. The certificate
calculus remains useful for short proofs of particular
persistence laws: `Core/SixValuation` checks the six-row five-point law by one
finite family of clauses and owner orders, without a subpower enumeration.

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

## Further structural restrictions

[Envelope-spine counterexample](envelope-spines/README.md) rules out replacing
every sibling subtree by its greatest profile completion, even with arbitrarily
repeated owners and unions. Its small closed-relation checker is independent
of a complete term enumeration. [Marked-type coextension](marked-type-coextension.md)
explains why coexistence of occurrence types yields no pairwise color restriction.
These are research certificates and arguments, rather than public Lean claims.

[Profile relations and one bound](profile-bounds.md) gives a restricted Horn
classification, a closed criterion with projection/two-leaf witnesses, and a
four-variable counterexample to ownerwise factorization under one bound.
