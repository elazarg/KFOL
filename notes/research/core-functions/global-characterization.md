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
