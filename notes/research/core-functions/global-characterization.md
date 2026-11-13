# Global characterization: structural reductions and obstructions

The active target is in [target.md](target.md). This note separates proved
library results from research arguments that have not been formalized.

## Proved in Lean

- `Core/AtomicObserver`: exact closed reachability criterion for one observer
  on atomic interval inputs, including ambient role sets larger than three
  and the nullary boundary.
- `Core/Bichain` and `Core/BichainFiber`: the four-element observer quotient is
  the union-expanded bichain; its pure Boolean-projection fiber is the whole
  expanded clone at one lower arity plus one zero trace, with uniqueness.
- `Core/AtomicAmalgamation`: three individually core-realizable complete views
  with common unanimity singleton profiles need not have a common core term.
  Three atomic rows suffice to exclude one. The relation certificate is closed
  under the actual owned choices; no clone-enumeration assumption is used.
- `Core/Hypergraphs`: closed boundary/no-trap axioms present every invariant
  relation, even empty relations and empty coordinate sets. Universal
  preservation and positive/negative guard persistence give exact global
  obstruction criteria. Auxiliary clutters are still quantified over.
- `Core/ProfileRelations`: all mixed-gate-closed finite Boolean profile
  relations have forced bits, same-owner implications and rainbow conflicts.
  `Core/RainbowPersistence` gives a closed one-bound criterion with projection
  or two-leaf witnesses, without finite-type assumptions.
  `Core/ProfilePersistence` shows why constraints on separate owner families
  do not suffice, even for one output bound. See [profile-bounds.md](profile-bounds.md).

- `Core/ProfileBounds`: a complete direct criterion for prescribed full
  profile tables under one upper winner bound; it specializes to ordinary
  admissibility when the bound is unrestricted.
- `Core/Staircase`: omission independence and arbitrarily large atomic
  upper-bound obstructions whose every proper subfamily has a projection
  witness. This supersedes finite row-Helly experiments.
- `Core/GhostElimination`: every neutral face is zero or a lower-arity core
  operation; the full projection-profile fiber is precisely reset of the
  lower-arity core, plus projection. `Core/CrownResiduals` shows that all
  proper neutral faces of the cyclic noncore operation are input unions.
  See [neutral-source elimination](ghost-elimination.md).

The bichain is the algebra in Harding, Walker and Walker, *Type-2 Fuzzy Sets
and Bichains* (2013), Definition 5 and Figure 1. Its older normal-form results
for identities do not specify which formal normal forms arise from terms;
they do not supply the missing guard characterization.

## Shared coordinates and one common observer carrier

The [status-selector representation](status-selectors.md) replaces separate
per-owner selections on one atomic-status fibre by a canonical pair: fixed
atomic winners and whole ambiguous inputs. Four-point interpolation already
forces this law. The prime examples satisfy it, so the remaining issue is
compatibility across status patterns.

The [unowned-observer construction](unowned-observer.md) places the original
observer algebras in one (K+2)-element carrier B_I as omitted-atom faces.
The original operation is core exactly when those faces have a common
term extension. Its profile quotient D_I has exact local interpolation
threshold K and least near-unanimity arity K+1. The additional N/P distinction
restores nonfinite relatedness, with Gray-crown patches constructible using
only the old owners. All proper quotients of B_I factor through D_I.

This viewpoint gives sharp stability of identities through K variables when
unowned roles are added, and all-arity stability for identities with a common
unused owner. It does not justify filling the missing face data arbitrarily.
The canonical completion based on all old cofactor essentialities is
monotone, has the correct faces and singleton profiles, and lies below every
term extension, yet it need not be term-induced. The sharp example needs
only K+1 variables, with one
shared input: three positive profile coalitions force a fresh winner which
all old cofactor-essentiality data miss.

[Colored interiors](colored-interiors.md) couple the selections across
ambiguity patterns. They satisfy strong outcast, idempotence and a ternary
invariant. A closed profile lower bound is exact for primitive read-once
words and rejects the dependence-completion counterexample. These laws do
not suffice in general. Every (K+1)-point interpolable operation passes
all [positive-profile bounds after polynomial polarizations](polarized-profile-bounds.md),
including arbitrary circuits nesting the candidate, identifications and
constant cofactors. Consequently large Gray crowns pass this entire testing
scheme despite being noncore.

## Union polarization does not complete the scalar criterion

The following uniform mathematical counterexample has a written proof below,
but is not yet a Lean theorem or a report claim. Ternary experimental agreement
was misleading and must not be extrapolated.

Let B={b,c,N,P}, with the two bichain operations and observer union. For a
monotone Boolean function f, interpret b,c as fixed bits 0,1 and N,P as free
coordinates, obtaining a Boolean subcube Q(v). Define D_f(v) as follows:
return b or c when f is constantly 0 or 1 on Q(v); otherwise return P when
some P-marked coordinate is essential in f restricted to Q(v), and N otherwise.
An essential coordinate has a pair of vertices differing only there on which
f changes.

Replace each input by the observer union of k fresh atomic inputs from
{b,c,P}. Every positive atomic interval of the resulting P trace has a monotone
Boolean separator that is constant on every zero interval, for every k.
Indeed, choose an essential marked coordinate j and a Boolean edge witnessing
it. In each block choose a nonconstant cardinality threshold theta_i. At a
fixed mixed block its value can be either witness bit; at a marked block its
lower and upper values bracket that bit; at block j they are 0 and 1. Then
psi=f(theta_1,...,theta_n) separates the positive interval. Wherever psi
changes, a coordinatewise Boolean path has an f-changing edge in a strictly
increasing block. That block is P-marked and essential in the corresponding
cofactor. Hence every psi-positive interval is D_f-positive. The atomic
criterion therefore accepts every such polarization.

Nevertheless f(a,b,c,d)=ab OR ac OR bd gives a nonterm D_f. The
[four-row invariant](face-gluing/noncore.md) gives a short analytic proof:
outputs 1 at (1,1,0,0) and 0 at (0,0,1,1) force P at (N,P,1,0) or
(P,N,0,1) for every full bichain term. D_f instead returns N on both
marked rows. Thus even all union-polarized atomic tests miss a nonterm.

The [coherent-cube theorem](coherent-cube-safety.md) proves the exact positive
boundary: pairwise-intersecting marked cubes impose no additional constraint
beyond the marked variables' Boolean inessentiality. Its anchored construction
is not globally complete, even when an exact term exists: the
[eight-variable counterexample](anchor-amalgamation.md) is realized by a
seven-gate read-once formula but by none of its anchored forms.

## Disjoint factors of full operations are canonical

[Block decomposition](block-decomposition.md) applies to all observers at
once. For an idempotent disjoint-block factorization with essential outer
inputs, the composite is core exactly when the outer and all inner factors
are core. The outer factor is its block-diagonal minor; each inner factor is
its neutral residual outside that block. This proves uniqueness and gives
an intrinsic factorization test, without searching for unspecified factors.
Equivalently, a block can be summarized by one winner set when there are
exactly as many distinct context functions as the carrier has states.
Overlapping input reuse remains outside this reduction. The four-variable
gluing obstruction is already prime: all proper identification minors and
all proper neutral sections are core, so it has no proper disjoint idempotent
decomposition.

This is not only a four-variable issue. The
[unbounded-prime theorem](prime-obstructions.md) proves that the Gray-crown
operation on 2d inputs has every proper identification minor core and every
proper neutral residual equal to input union, while remaining noncore and
2^d-point interpolable. A deleted-region patch realizes each identification
minor because the lower transversals separate every input pair. Thus proper
disjoint decomposition cannot reduce all obstructions to bounded prime arity.
Even semantic agreement on all intersections of the proper diagonal faces
does not provide a common realizing term.

## A closed profile envelope is exact for read-once trees

[Read-once profile minimality](read-once-profile-minimum.md) gives a sound
closed lower envelope in every profile fibre, and exactly the intersection
of positive-profile extensions when the top bits are true. A winner k is certified by
one winning coalition per owner whose nonempty intersection consists only
of inputs containing k, with no rival-singleton input in the intersection
of the other owners' coalitions. The one-bound theorem proves that any
core operation retaining those positive profile bits must retain k.

For a primitive read-once tree this envelope is exactly its full value,
not merely its singleton outputs. A direct induction constructs certificates
with a singleton common source. Hence a read-once tree is the least core
operation in its complete profile fibre. Distinct occurrences of one input
can invalidate the singleton-intersection step, so this is a positive
structural regime rather than the remaining all-term characterization.

The [intrinsic recognition theorem](read-once-recognition.md) gives closed
conditions for this regime using canonical graphs on the original variable
support. Minimal winning coalitions must be precisely maximal cliques;
their complement graphs must color every variable pair once, with no
rainbow triangle and no induced monochromatic four-vertex path. These
conditions reconstruct a unique reduced owner cotree. Equality with the
closed profile envelope then recognizes the full read-once winner operation.
The criterion needs no supplied occurrence graph, but does not cover general
overlapping reuse.

[Pure-owner upper bounds](read-once-rigidity.md) make read-once operations
globally minimal and rigid under every unowned-role extension. They also
determine the unique free independent-status extension from the canonical
cotree. This rigidity exposes a sharp failure of the greatest monotone
observer-face completion: it agrees below arity 2K, but at 2K inputs it
can exceed the only term-induced extension, despite correct faces and
singleton profiles.

## A rigid non-read-once family

[Tight owner quotas](near-unanimity-size.md) provide full-value positive
examples requiring reuse. Choose nonnegative d_r with sum n-1. The quota
profiles Phi_r(E)=[|E|>=n-d_r] force a unique core operation: output the
corresponding atomic quorum when it exists, and otherwise the union of
all inputs. An elementary partition repair supplies every required
positive-profile certificate. The operation is globally minimal and
extension-rigid, and is primitive read-once exactly when at most one
quota is positive. Its colored interiors have an explicit quorum cutoff.

The profile quotient admits near-unanimity at arity K+1, while a primitive
word needs at least 2^K leaf occurrences; equality requires all variables
distinct. Thus its least read-once near-unanimity arity is 2^K. Quotas also
give explicit minimal core operations with no read-once core minorant,
already at three variables, rather than merely existential minimal
operations selected from a finite poset.

The [quota pivot normal form](quota-normal-form.md) constructs these
operations directly: a chosen source occurs once, with one smaller-quota
sibling at each active owner's spine node. It attains that source's
canonical maximal factor vector. Combining pivot words attains the
greatest free extension at every source simultaneously; it coincides
with the greatest arbitrary antitone completion in this family. Prime
guards and exact construction-size bounds are explicit.

## Canonical closures and minimal CNF operations

[Owner-shadow is exactly closure idempotence](separable-closures.md).
The pure-owner sections of every core operation therefore give canonical
loopless closures, with spanning predicates equal to its singleton
profiles. The [functional-dependence theorem](cofactor-dependence-closures.md)
identifies c_r(E) with the inputs made inessential by fixing E to {r};
the closure laws follow directly from restrictions of arbitrary functions.
When the source coefficients separate, their products reconstruct
the operation directly from these colored closures. Synthetic closure
families still need full atomic-profile compatibility; pure-probe
admissibility alone is insufficient.

The [additive case](additive-closure-characterization.md) has a complete
closed criterion on the original variables. Write i ->_r j when the
single source i captures j. For i!=j, an r-arrow to j must contain every
s-successor of j among its own r-successors. Opposite nontrivial arrows
must have the same color. These two conditions suffice: the union
preorder has monochromatic components, whose ancestor spines provide
source-linear minorants with every canonical factor attained. Their
union realizes the candidate; marked completion attains the greatest
free extension. The test also applies directly to monomial guard data
without assuming closure operators in advance. It is a subclass theorem;
joint-premise closure dependencies are not represented by this graph.
Cofactor-dependence composition proves the first arrow law for any
genuine core operation, without separation. Two-point neutral profiles
prove the second. Consequently the same laws classify all jointly
realizable additive pure-owner families, and their separable upper hull
is always core and greatest in its exact pure-closure fiber.

[Every finite loopless closure](closure-core-operations.md) is realized
by a two-owner CNF: fold owner 1 within complements of proper closed sets
and owner 0 between clauses. This is an exact bijection, and complements
of meet-irreducible closed sets give the canonical irredundant CNF.

The [global minimality classification](minimal-cnf-matroids.md) has a
matroid answer. A prime clause clutter is minimal exactly when it satisfies
cocircuit elimination; failure gives an explicit strictly smaller factored
word. Redundant clauses are harmless precisely when they are unions of
the contained prime clauses. Thus all minimal full-support CNFs are
matroid cocircuit operations with optional flat-complement clauses.

The [matroid operations](matroid-core-operations.md) equal their closed
profile lower envelope, are rigid under unowned-role extensions, and have
prime source guards described by bases and cocircuits. Factoring against
minimality gives a chosen-source-linear word attaining the entire maximal
full factor vector at that source. Simultaneous read-once realization
holds exactly for rank-one direct sums. Both canonical Boolean normal
forms are globally minimal exactly for uniform thresholds; every other
loopless matroid has an explicit strict DNF-above-CNF witness.

The [canonical separable hull](separable-hull-failure.md) shows why these
closures do not yet solve the general target. For a core F, multiplying
its pure factors gives a nonempty monotone idempotent upper bound with
the same singleton profiles, pure sections and whole-input provenance.
A four-variable word gives a noncore hull for every K>=3, including
three owners. Its hull nevertheless satisfies hereditary omission and
has core proper input minors. The explicit word is the greatest core
minorant of that hull. Thus even jointly extracted closure data with
these stronger compatibility properties do not justify independent
owner completion.

All two-owner CNF operations do have an attained greatest full type at
each source: factor the chosen source into a subordinate linear word,
then union with the original target. But the
[asymmetric closure operation](closure-core-operations.md) has no full
realizer linear in X. Every possible X-path is forced to use owner 0
only, with each sibling equal to Y choice_1 Z; that collapses to a
strictly smaller read-once operation. Maximal-type attainment and source
separation therefore do not imply chosen-input linearization.

## Essential overlap among global minima

The [mixed three-owner example](mixed-cnf-minimum.md)

    F=(X choice_1 Y) choice_0 (Y choice_2 Z)

is globally minimal and least in its exact profile fibre, but its profile
tuple is not maximal admissible. Its positive-only profile envelope is
empty at (1,0,2), while F returns {1,2}. The proof uses a complete
same-owner separator table, rather than term enumeration. Every realizer
must repeat Y, and each of its canonical owner closures violates matroid
exchange. It therefore excludes maximal-profile and disjoint-matroid
routes as universal descriptions of minima.

The displayed word also attains its greatest arbitrary antitone free
completion. At the shared source the maximal actual type family has two
incomparable members; no greatest full vector exists. Thus a greatest
free extension can require an OR of genuinely different source types.

## Exact free-bit forcing from positive profiles

[Free profile persistence](free-profile-persistence.md) works even when
the passive atomic-owner flags overlap. A positive rainbow selection
forces a marked free coefficient precisely when its common intersection
is the source and its rival deviations avoid the required intersections.
For arbitrary positive demands, an inclusion-minimal infeasible zero-bit
premise has at most one demand per owner: an owned gate would otherwise
combine two deletion witnesses. This proves the same closed criterion
for all jointly feasible positive profile families.

This computes the pointwise least free coefficient across positive-profile
extensions. For maximal admissible profiles these are the exact profile
realizers. A single word attaining all pointwise minima is a separate
condition; the general exact-profile problem is not solved by this forcing
criterion.

The failure is sharp even for maximal profiles: the
[ternary quota obstruction](free-profile-nonattainment.md) has two exact
realizers with no common lower free extension. A common-source persistence
law forces one of two source bits, although each can individually be zero.
Its full operation and ordinary ambient extension are unique. Thus free
joint attainment is a separate issue even after both those questions are
settled.

The [one-pattern theorem](free-pattern-interpolation.md) now supplies an
exact joint profile/source clause presentation, using absorber exclusions,
rainbow clauses and same-owner separator clauses. Reset padding supplies
all requested positive bits after the zero-budget conditions hold.

[Two patterns need not amalgamate](free-pattern-amalgamation.md), even
when an antitone completion has correct ordinary guards and every entire
one-pattern source vector is jointly realizable at all observers. A
two-query path law gives the obstruction. For the ternary quota over
exactly three old owners, the same analysis gives a complete thirteen-element
old-observer free-extension fibre. Its six uncertain poison bits form a
zero graph with no globally reachable vertex; the extension order is the
opposite face order of a hexagon boundary. This complete small fibre
classification does not supply the remaining all-arity guard criterion.

The [poison-graph theorem](quota-poison-graphs.md) extends the exact
projection classification to arbitrarily many active unit-quota owners.
At a fresh or inactive observer, exact zero records are disjoint unions
of outgoing stars, opposite pairs and isolates. Forbidden incoming pairs
and directed two-edge paths give necessity; explicit rainbow witnesses,
minimal-premise repair and reset padding give sufficiency. Active old
observers instead have all these coefficients forced to one. This is
an unbounded closed mixed-pattern criterion, still restricted to the
specified poison projection rather than arbitrary guard tables.

## Exact-profile forcing and mixed closure outcast

[The exact-profile envelope](exact-profile-envelope.md) computes the
pointwise intersection of all exact-profile realizers. Besides positive
rainbows, its certificates use a true and false coalition at one owner.
These negative bits recover the mixed minimum even where its positive
envelope is empty. Joint attainment across all rows is a separate question;
existing profile-fibre nonconvexity excludes interval bounds as a complete
recognizer.

For source-separable candidates satisfying actual-source attribution,
[partial-coloring tests](mixed-closure-outcast.md) express nonemptiness
and full singleton-profile factorization using the constant part A and
unblocked positions Q. For genuine source-separable core operations,
outcast has the closed form at every partial coloring

    c_r(E_r union (J\Q)) intersects Q = empty for every r.

Restoring blocked ambiguous positions cannot capture a free one, including
at an initially saturated fiber. Pair-cut (P) is equivalent to this
full outcast law. Its direct cofactor proof uses a third observing owner
to detect a source outside the two old closures. The corresponding canonical
selection maps Q_a are interiors. Equivalently, every full coloring a
makes T -> UNION_r c_r(T intersect a^-1(r)) a closure operator.
For loopless candidate maps this condition implies source attribution.
The [canonical common-carrier extension](canonical-separable-extension.md)
is monotone, has all prescribed observer faces, and bounds every
term-induced extension. It preserves the full ternary outcast invariant;
for arbitrary admissible colored closures, that preservation is equivalent
to full Q-outcast and preservation of the spanning owners under blocked
restorations. Canonical attainment can fail even for a genuine
core target, as the complete-head family below shows. Sufficiency for arbitrary closure data
is refuted by the
[prime four-variable counterexample](separable-closure-counterexample.md),
uniformly for every K>=3, even with hereditary profile/omission tests
and core proper neutral faces and identification minors. All pure-owner
closures are its actual functional-dependence closures, and full old-value
outcast holds. A universal three-row guard law nevertheless excludes it.
The colorful-cover lemma separately shows that admissible
spanning profiles imply nonemptiness; omission then supplies exact atomic
profiles, and colored outcast plus omission supplies full span-outcast.

The same note gives a positive
[two-rule common-context classification](separable-closure-counterexample.md).
If one owner captures y from L union {x} and another captures x from
M union {y}, with no other nontrivial rules, realizability is equivalent
to L intersect M being nonempty. A shared context protects auxiliary
sources in two explicit source-linear minorants; union with the context
projections realizes the operation and yields greatest free-completion
attainment. Disjoint contexts give the uniform three-row persistence
law used by the prime instance. When both contexts are nonempty there
is also an explicit greatest core minorant, obtained by replacing the
conflicting context's value by its context-input union. It keeps every
pure port, so the noncore candidate is its separable upper hull.

Hereditary span-outcast has the exact pairwise mixed-loop formulation
(L) in [the closure-cut note](mixed-closure-outcast.md). Thus the additive arrow laws have direct
coalition analogues, but those analogues and hereditary common-source
admissibility still miss the prime obstruction. The stronger reciprocal
cut (C2), derived from the three-row law for arbitrary source-separable
core targets, detects it: disjoint-context reciprocal captures cannot
create two new free heads. It is still insufficient: the
[three-owner feedback obstruction](three-owner-exchange.md) passes
(P),(C2), hereditary common-source and functional dependence, including
all proper input reductions, yet violates a stronger closure-elimination
law. That law uses a direct rainbow cover condition on colored captured
blocks. Its projection lemma follows from monotonicity and ordinary
singleton-profile admissibility. The strengthened law itself implies
hereditary admissibility and simultaneous cross-value dependence
composition. Its sufficiency for pure ports is false: the
[eight-variable triple](feedback-three-colors.md) satisfies the full law
at every supplied owner, while a fresh identity coordinate rules out
every common word. Two foreign colors admit complete compression to
conditional mutual captures; three foreign colors require repeated
queries, even after all independent-base profile tests are imposed.
Compatibility after adding an unused owner is necessary but still
insufficient: a [five-variable terminal tuple](feedback-profile-obstruction.md)
passes all identity-extension feedback tests but has no joint pure-port
realizer. It has full cofactor independence, a core passive baseline,
and core proper neutral residuals. These tests do not settle even pure traces. A
[naive lift to independent coalition nodes](coalition-lift-obstruction.md)
does not repair this: a genuine core CNF already yields a mixed SCC
with disjoint labels, and the coherence map fails to commute with gates.

The [complete-head circuit classification](complete-head-circuits.md)
gives an exact unbounded family. Each head has a distinct owner and
is captured by that owner when every other head and its possibly empty
context are that owner's atoms. Realizability holds exactly when
the nonempty contexts represent every owner or some two contexts overlap.
Joint pure-port realizability requires exactly two nonempty contexts
or more, and feedback elimination detects the excluded cases. Short
spines give a closed greatest core minorant and the sharp behavior
under owner extension. When every owner has a head and contexts are
disjoint, the ordinary operation is genuine and source-separable,
but no canonical maximal head full type is actual. Two actual
types have that nonactual vector as their join. This refutes maximal
full-type attainment inside the genuine separable class. A context
overlap restores all maximal head vectors. In the disjoint case
the greatest old-observer independent-flag product is still attained;
the canonical common-carrier product is not, although its smaller
greatest term-induced extension is attained and has a closed formula.

## Full types at greatest profile completions

The [pure-trace quotient](pure-trace-quotient.md) identifies joint
pure-owner data with term operations on a colored product of
three-state algebras. A single coordinate has a five-relation basis
of arity at most three. The product has genuinely stronger
compatibility conditions; its finite relatedness is not proved.
Naming zero gives independent coordinate isolation and a ternary
relational basis for the expansion. The constant-free clone is
strictly smaller even on idempotent operations preserving every
maximal proper invariant relation in every finite power. The same
counterexample preserves every unary subalgebra and fails a binary
invariant relation.
An explicit five-leaf identity separates its equational theory from
the full core, so this is a proper reduction of the pure-port problem.

[Capture-trigger normal forms](capture-trigger-normal-form.md) settle
every source-separable upper interval above a greatest profile
completion. A derivative profile tuple supplies a source-free trigger
for each owner stage; the resulting source-linear minorant attains the
entire canonical vector. Arbitrary shared-anchor closures are a special
case. This is an intrinsic sufficient criterion, not a characterization
of all separable operations.

For genuine separable targets, [owner-extension stability](owner-extension-stability.md)
is equivalent to canonical common-carrier attainment. One new owner
tests every extension: fresh-owned gates can be replaced by derived
union, and a single old-owner word then works for arbitrary larger
owner sets. This equivalence does not assert an intrinsic condition
for that test to succeed.

For [every greatest profile completion](profile-maximum-types.md), soundness
of a full occurrence vector separates owner by owner, and every sound
vector is actual. A spine realizes the proposed vector; attaching the
target once at each owner restores the whole target without changing that
vector. The restoration uses exactly the fact that an ambiguous target
value is the whole input union.

Consequently the unique greatest actual type at source j is
NOT Phi_r on coalitions excluding j, for each owner r. A finite fold of
these realizers attains the greatest arbitrary antitone free completion.
This is a general positive type theorem, containing the quota family and
input union. It does not apply when a target's ambiguous value omits some
input winner, which is where the remaining mixed-guard problem persists.

## Other routes that do not suffice

Independent observer criteria fail by the formal amalgamation example.
Completing singleton profiles and taking unions of their greatest envelopes
also loses term functions below those envelopes. Tracking surviving Boolean
DNF monomials and CNF clauses independently loses the requirement that the
same repeated occurrence survive both.

The [spine obstruction](envelope-spines/README.md) is stronger than a failure
of choosing greatest siblings. Every binary core operation is a greatest
completion on its support. Thus a ternary term with any variable occurring
at most once is itself in the excluded spine language. The explicit core
counterexample needs every variable at least twice in every realizer, and
requires a node with two nongreatest full-support children. A four-row
analytic argument rules out a source-linear witness for its distinguished
positive guard bit. Branching dependence cannot be removed by allowing
arbitrary smaller-arity siblings along one source path.
The counterexample now has a seven-leaf primitive realizer, and a profile
argument proves seven optimal without the finite envelope certificate.
The general lemma behind the proof says that a source used once, mandatory
for an owner's profile, cannot introduce a third winner when the rest of
a winning coalition is fixed to that owner's atom.
The [five-variable separable example](pure-trace-quotient.md#repetition-persists-in-a-source-separable-core)
also excludes extracting a source-linear minorant for every positive
probe of a genuine separable target. No larger uniform bound works
for arbitrary core targets either: the
[rectangular source hierarchy](rectangular-source-complexity.md)
forces 2^d marked-source copies in every subordinate word, with an
exact minimum of 3*2^d-2 leaves despite a linear-size circuit.

A simple coherence schema records only the set of states occurring in a tuple:
R_Gamma consists of tuples whose nonempty value-set belongs to Gamma. Requiring
invariance under the three operations at every relation arity still misses the
cyclic nonterm operations. Nonuniversal such schemas either allow no P, where
the cyclic operation acts as union, or forbid b and c in one coherent set,
where a single deletion patch agrees on every column. Adding passive guard
monotonicity does not remove that defect. A richer relation schema needs the
colored incidences retained by the proved clutter presentation.

A canonical occurrence graph cannot simply retain maximal source types.
For X star_r (X star_s Y), r!=s, the two X occurrences have distinct filter
roles, including a dominated type. Taking all sound types fails even when
every variable is active, as the three-variable example below shows. Choosing
witnesses can create new maximal cliques and new guards, so this has not
eliminated the compatibility problem.

[Canonical blocker soundness](canonical-blocker-shortcut.md) also fails:
one target can pass every owner cut against input-column-sound heads while
an explicit two-choice term violates it. Invariant auxiliary support cannot
be replaced by this one-pass condition.

The [uniform column-sound barrier](canonical-sound-barrier.md) is stronger
for the proposed maximal-support construction: taking all sound heads
fails NoTrap at every arity at least two, using only one canonical probe
per input. Admissible sound support families do have a greatest union;
it is precisely the all-term-valid family. This fact alone supplies no
new direct criterion for that family.

[Atomic/neutral-face gluing](face-gluing/README.md) fails at four variables:
the operation differs from one short atomic realizer on only eight full
inputs and has explicit core realizers for every proper neutral residual.
Its scalar essential-source trace excludes a global term. The example also
satisfies the profile, provenance and omission laws. This is a written
research result with independent checks, pending Lean formalization.

## Further structural work

[Source-type pruning](source-type-pruning.md) supplies causal-drift and
owner-shadow necessary laws and a three-active-variable counterexample to
inserting all sound source types. Both laws still accept the known ternary
nonterms. [Canonical essential extensions](essential-extensions.md) gives a
cograph classification for quadratic Boolean functions and a five-variable
weighted-majority nonterm beyond that family. These research proofs do not
replace the full guard characterization.

The [all-owner side-effect law](actual-type-side-effects.md) rules out
additional exact types even when the target is an explicit core operation.
The previous drift and shadow tests therefore do not characterize actual
types conditional on core realizability either. In the positive binary
case, [one occurrence per actual full type](binary-occurrence-types.md)
suffices for a universal realizer, but different owner orders give
nonisomorphic type-saturated graphs. Knowing the canonical full-type
family does not force its individual edge colors.

Actual full types are also not closed under a globally sound coordinatewise
join: two explicit actual types of the same core target have a sound join
excluded by the all-owner side-effect law. That target is globally
nonseparable, so the example does not settle the separable maximum-type
attainment question. Conversely, the four-variable synthetic counterexample
has one globally sound canonical type per source, all passing shadow, drift
and all-owner side effects, but no common term realizes its guards. Individual
type tests alone therefore do not characterize global guard realizability.

[Exponential crowns](exponential-crowns.md) strengthen the locality obstruction:
paired-variable Gray cycles and one common cover give 2^d+1 core patches
using only 2d inputs. The full-winner construction, including additional
owners, is proved in the generic interval/frame modules. The operation is
2^d-point interpolable and fails at 2^d+1 points. This rules out replacing
the recognition theorem by a polynomial-in-arity locality bound.

[Pointed obstruction schemas](pointed-obstructions.md) give a further written
normalization proof: one query needs only K+1 nontrivial stem families;
negative-row head fibers can be empty, the original forbidden owner, or an
off-owner block. Forced extra pure heads show why ordinary pairwise cycles
and heads bounded by the target width are insufficient. This normalization
is not yet formalized and does not remove the diagram quantifier.
