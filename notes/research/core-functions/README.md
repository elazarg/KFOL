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

The [coherent-cube theorem](coherent-cube-safety.md) gives a closed positive
regime: pairwise-intersecting marked cubes admit a common safe formula exactly
when every marked coordinate is Boolean-inessential. An explicit cofactor
normal form realizes the canonical essential extension on all cubes through
any chosen Boolean anchor. Two disjoint marked cubes already obstruct this
amalgamation; a [four-row Horn invariant](face-gluing/noncore.md) gives the
short proof and replaces the older seven-row certificate. These results are
proved mathematically in the notes and are not yet Lean claims.

The anchored forms are [not globally complete](anchor-amalgamation.md), even
for an eight-variable function with a seven-gate exact realizer. A separate
[block-factorization theorem](block-decomposition.md) reduces any idempotent
disjoint composition to canonical smaller operations: the diagonal outer
minor and the neutral inner sections. It applies to the full core, while
leaving overlapping-input and prime-operation compatibility unresolved.

For [read-once primitive core trees](read-once-profile-minimum.md), a closed
rainbow formula in the singleton profiles gives the entire winner operation.
Such a tree is the least core operation in its profile fibre. A direct
coalition induction identifies where this argument fails for repeated
variables: different occurrences can create a spurious common source.
The [intrinsic read-once recognition theorem](read-once-recognition.md)
uses canonical graphs on the original variables: minimal winning coalitions
are maximal cliques, pair colors have no rainbow triangle or induced
monochromatic four-vertex path, and the operation equals its profile envelope.
These conditions reconstruct a unique reduced cotree without a supplied
occurrence graph. This recognizes the read-once regime, not arbitrary reuse.

[Read-once rigidity](read-once-rigidity.md) supplies the complementary
upper bound: pure-owner probes bound every occurrence factor in any
subordinate term. Read-once operations are globally minimal, have unique
extensions even at independent owner flags, and attain both free bounds
in their exact operation fibre. The greatest monotone completion of their
observer faces agrees below arity 2K but can fail at 2K.

[Tight owner quotas](near-unanimity-size.md) give a non-read-once positive
family. Quotas summing to n-1 force a unique full core operation: an owner's
atomic quorum, or the whole input union otherwise. These operations are
globally minimal and extension-rigid. They are read-once exactly when at
most one quota is positive. Near-unanimity on the profile quotient requires
at least 2^K leaf occurrences; its least read-once arity is 2^K, compared
with K+1 when variable reuse is allowed.
Their [recursive pivot normal form](quota-normal-form.md) gives a word with
any chosen source occurring once, exact prime guards, and a canonical
greatest free extension attained simultaneously at every source. The
construction has explicit word and shared-circuit size bounds.

[Canonical owner closures](separable-closures.md) give a common structural
layer for all core operations: owner-shadow is precisely closure
idempotence. [Two-owner CNF operations](closure-core-operations.md) are in
bijection with finite loopless closures, with canonical irredundant normal
forms. Their [globally minimal members](minimal-cnf-matroids.md) are exactly
the matroid cocircuit operations, with an exact condition on redundant
clauses. [Matroid source guards](matroid-core-operations.md) are bases and
cocircuits; a realizing word can be linear in any chosen source. Both
prime Boolean normal forms are minimal exactly for uniform thresholds.

The [asymmetric closure example](closure-core-operations.md#source-separation-does-not-give-a-linear-full-realizer)
has an attained greatest full type at each source, yet cannot be realized
with X occurring once. Full source separation does not remove input reuse.
In the other direction, the four-leaf
[mixed-color minimum](mixed-cnf-minimum.md) has nonmaximal admissible
profiles and must repeat its shared input. It is least in its exact
profile fibre, although its positive-profile envelope is empty at one
row. Its individual owner closures are not matroids.

The [separable hull can fail](separable-hull-failure.md): even closures
extracted from an actual core operation can have a noncore product
completion, already with five variables and four owners. It retains the
original profiles and pure sections but violates omission independence.
For genuine source-separable operations,
[mixed closure outcast](mixed-closure-outcast.md) supplies closed necessary
tests on every partial coloring, including saturated fibers. A two-erasure
lemma closes the formerly missing case. Equivalently, for every full
coloring a the map T -> UNION_r c_r(T intersect a^-1(r)) is a closure.
This law also implies source attribution for loopless candidate maps.
The [canonical common-carrier extension](canonical-separable-extension.md)
is monotone, matches all old observer faces, preserves the ternary outcast
invariant, and bounds every term-induced extension. Its term attainment
and sufficiency of the coupled closure laws remain unresolved.

The [prime-obstruction theorem](prime-obstructions.md) shows that the hard
part persists at unbounded arity: the Gray crowns have core proper
identification minors and input-union proper neutral residuals, yet fail
globally after passing all 2^d-point tests on 2d inputs. They admit no
proper disjoint idempotent decomposition. Hence bounded-prime recognition
and gluing compatible lower-arity operations do not finish the problem.

[Full-support branching](envelope-spines/README.md) is necessary already at
three inputs: an explicit core operation has no realizer using any input
at most once, nor any finite union of such terms. Every binary core
operation is its greatest profile completion, so the existing spine
certificate proves this stronger claim. A four-row analytic proof separately
rules out source-linear witnesses for one positive canonical observation.

[Atomic-status selectors](status-selectors.md) give shared coordinates for
all observers: on a fixed singleton/ambiguity pattern a core operation is a
fixed union of atomic winners and whole ambiguous inputs. Four-point
interpolation already forces this representation. The selector law alone
still accepts the prime counterexamples.

The [common observer carrier](unowned-observer.md) has only K+2 states.
Its profile quotient has exact interpolation threshold K and least
near-unanimity arity K+1, while the full carrier remains nonfinitely related.
Identities are stable under unowned-role extension through K variables,
sharply, and at every arity if the two sides have a common unused owner.
A canonical completion from semantic dependence is monotone and agrees
with all old faces, but a K+1-variable example rules out its
term-inducedness, at the first arity where face data can be missing.
This is a reformulation and a sharper obstruction to
gluing, not the missing complete intrinsic criterion.

[Colored interiors](colored-interiors.md) give closed selection laws across
ambiguity patterns, including strong outcast and a ternary invariant. A
profile lower bound determines these interiors exactly for primitive
read-once words and strictly strengthens those necessary laws in general.
However, [polynomially polarized profile bounds](polarized-profile-bounds.md)
still cannot characterize the clone: every (K+1)-point interpolable operation
passes them, even in arbitrary finite circuits nesting the candidate.
Large Gray crowns therefore pass all of these tests and remain noncore.

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

[Negative budgets](negative-budgets.md) proves omission independence and an
atomic staircase giving arbitrarily large minimal infeasible families of
upper bounds. The closed full-profile one-bound theorem is now in
`Core/ProfileBounds`.

[Free-polarization obstructions](free-polarization/free-polarization-extrema.md)
record why canonical prime occurrence boxes and canonical extremal free
completions do not directly eliminate the colored occurrence graph.
[Free profile persistence](free-profile-persistence.md) gives an exact
closed criterion for when arbitrary positive profile demands force one
independent-status source bit, even with overlapping owner flags. Its
pointwise minima need not have a common realizing word.
This [nonattainment already occurs for maximal profiles](free-profile-nonattainment.md)
of one fixed ternary quota operation, despite its unique ordinary extension.

[One-pattern interpolation](free-pattern-interpolation.md) gives a complete
closed clause theory for profiles and all eligible source bits at a fixed
independent-status pattern. [Two-pattern compatibility](free-pattern-amalgamation.md)
is strictly stronger, even with antitonicity and simultaneous one-pattern
feasibility at every observer. For the ternary quota over exactly three
old owners, the entire old-observer free-extension fibre has exactly
thirteen members, with a closed graph criterion and explicit realizers.
For [arbitrarily many active unit-quota owners](quota-poison-graphs.md),
the entire poison projection has an exact graph criterion: no two incoming
zero edges and no directed two-edge path on distinct vertices. This holds
for fresh or inactive observers; active old observers have no zero edges.

The [exact-profile lower envelope](exact-profile-envelope.md) has a closed
formula using positive rainbows and true/false same-owner separators.
It computes pointwise forcing, including the mixed minimum above, and
does not assert compatibility across all rows.

[Profile maxima](profile-maximum-types.md) have a complete actual-type
classification: every globally sound full type occurs, and the greatest
arbitrary antitone source completion is term-induced. This generalizes the
quota maximum construction to every admissible profile tuple. Targets
with ambiguous proper subsets of the input union lie outside this regime.

[Actual-type side effects](actual-type-side-effects.md) strengthen the
old drift and owner-shadow tests and refute their sufficiency even for
a known core target. [Binary type saturation](binary-occurrence-types.md)
constructs a realizer with exactly one occurrence of each actual full
type for one owned choice, but its type-saturated colored graph is not
unique. Neither result removes general mixed-type compatibility.

[Neutral-source elimination](ghost-elimination.md) proves closure of all
neutral faces, the exact full projection-profile fiber, and why every proper
neutral face of the crown obstruction is nevertheless just input union.
The [four-variable gluing counterexample](face-gluing/README.md) shows that
jointly realizable atomic data and all core neutral faces can still fail to
have one realization; it has a written proof and standalone finite checks.

[Grouped cubes and powerdomains](grouped-cubes-and-powerdomains.md) gives an
exact scalar implication-preorder recurrence and proves why its initial edge
data, even on all cofactors, cannot suffice. It also identifies the observer
algebra as a Smyth powerdomain and proves that two natural logical-relation
transfers still miss the noncore P4 operation. These are mathematical research
arguments, not new Lean claims or a solution of the full characterization.
