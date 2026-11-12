# The canonical common-carrier extension of a separable operation

Mathematical research, without Lean claims. A source-separable core
operation has a canonical candidate extension to B_I. It is flat-order
monotone, extends every old observer face, preserves the full ternary
outcast invariant, and bounds every term-induced B_I extension from
above. It need not be induced by a term, even for a genuine separable
target; the complete-head classification below identifies both this
failure and the strictly smaller attained maximum in that family.
The claim does not concern independent overlapping owner flags.

Fix finite owners I with K>=3, finite nonempty variables V, and a
source-separable core operation F on its full support. Write c_r for
its canonical loopless owner closures and Phi_r(E)=[c_r(E)=V].
Their construction and source formula are in
[separable-closures.md](separable-closures.md).

The common carrier B_I has old atoms r and N,P, with flat-union order
atom r<N<P. The quotient sigma identifies N,P and retains the old
atoms. At v in B_I^V put

    E_r(v)={i:v_i=atom r};
    P(v)={i:v_i=P};
    J(v)={i:v_i is N or P};
    Q(v)=V\UNION_r c_r(E_r(v)).

The E_r are disjoint and Q subseteq J. Admissibility of the spanning
profiles makes at most one c_r(E_r) equal V.

## Definition and agreement with the old faces

Define

    G_Q(v)=atom r if c_r(E_r(v))=V;
           P if no owner spans and P(v) intersects Q(v);
           N otherwise.                                  (1)

If an owner spans, Q is empty, so the two cases cannot conflict.

**Theorem.** G_Q agrees with the prescribed operation on every
omitted-atom face B_I\{atom k}.

In this face E_k is empty and c_k(E_k) is empty. The original
observer-k membership condition is

    some j in P(v) is outside UNION_(r!=k) c_r(E_r(v)),

which is exactly P(v) intersecting Q. The old rival singleton
outputs are already fixed by the spanning profiles. These give all
face outputs: a rival atom when its profile holds, P when the
observed winner k is present, and N otherwise. The observer map
from the old winner carrier onto this face is surjective for K>=3,
so this identifies the whole face restriction.

Here a P input can come from an old k singleton as well as from a
k-containing ambiguous menu; no atomic-k input is required in the face.

## Flat-order monotonicity

**Theorem.** G_Q is monotone for the coordinatewise flat-union order.

Increasing a B_I input can only remove old atomic positions and add
or retain P marks. Thus each E_r shrinks, each c_r(E_r) shrinks, and
Q grows. A new spanning owner cannot appear. If an old atomic output
changes, it therefore becomes N or P, not a different atom. A P
output persists because its marked position remains P and stays in Q.
An N output can only remain N or become P. These are exactly the
required order comparisons.

This argument uses the closure and profile conditions, not an assumed
word for G_Q.

## An upper bound on every term-induced extension

Let T be any old-owner word realizing F, interpreted on B_I. Its
sigma-output is fixed by the old singleton profiles:

    sigma(T(v))=atom r iff c_r(E_r(v))=V.

Let C_T be its actual fresh selection set at this status pattern.
The occurrence-path formula gives

    C_T subseteq Q.                                      (2)

An occurrence's owner-r factor is bounded by the corresponding
pure-owner port. Taking the OR of products over occurrences is
therefore bounded by the product of those pure-owner ORs. A fresh
winner uses all old-owner factors, giving (2).

If T(v)=P, some P input belongs to C_T and hence to Q, so G_Q(v)=P.
If T(v) is atomic the outputs agree by their sigma-profiles. Otherwise
T(v)=N and G_Q(v) is N or P. Consequently

    T(v)<=G_Q(v) for every v.                             (3)

This does not assert that the upper bound itself is term-induced.

## Closure outcast and preservation of the spanning status

For a partial coloring E_r let J be its ambiguous positions and
Q=V\UNION_r c_r(E_r). A blocked restoration assigns some positions
of J\Q arbitrary old-owner atoms, giving larger atomic sets E'_r.
Two closed conditions are relevant:

    Q-outcast:    V\UNION_r c_r(E'_r)=Q;
    span-outcast: c_r(E'_r)=V iff c_r(E_r)=V, for every r. (4)

For source-separable core operations, full Q-outcast, including
saturated initial fibers, is proved in
[mixed-closure-outcast.md](mixed-closure-outcast.md).

Span-outcast follows directly from an actual word. Its actual
selection set C_T is contained in Q by (2). All restored positions
are therefore unselected for T. Whole-word outcast preserves its
output on the base all-N ambiguous assignment after those positions
are replaced by arbitrary atoms. In particular it preserves its
sigma-output. The profile formula then gives precisely span-outcast.
This argument does not require equality of C_T and Q at a saturated
fiber.

Indeed this span argument applies to every core word's canonical
pure-owner closures; source separation is needed for the additional
full Q-outcast theorem.

## The full ternary invariant

On B_I define

    (x,y,z) in R iff sigma(x)=sigma(y)
                       and (x!=P implies z=y).           (5)

The [colored-interior proof](colored-interiors.md) establishes this
invariant for primitive gates. The candidate G_Q preserves the entire
relation as well, not just its induced interior law.

More generally, for any loopless colored-closure family with admissible
spanning profiles, define G_Q by (1). Then

    G_Q preserves R iff Q-outcast and span-outcast (4)
                        hold at every partial coloring.  (6)

For sufficiency, take valuation rows u,v,w whose columns lie in R.
The first two have the same atomic sets E_r. If G_Q(u)!=P, the P
positions D of u miss Q: either an owner spans and Q is empty, or
the P-case in (1) is false. Every changed position from v to w is
in D, and hence is canonically unselected.

Restore the positions of D that became atoms. Q-outcast preserves Q,
and span-outcast preserves the spanning decision. The remaining changes
are N/P changes outside Q, which do not affect (1). All P marks on
Q are unchanged. Thus G_Q(w)=G_Q(v). Also the first two output
sigma-statuses agree because u,v had the same atomic pattern. This
is exactly (5).

For necessity, consider any blocked restoration D subseteq J\Q.
Take u with P at D and N at the other ambiguous positions. Then
G_Q(u)!=P. First take v all N, and let w perform the proposed atom
restoration. Its columns with u,v lie in R, so preservation gives
G_Q(w)=G_Q(v). The spanning decision is unchanged, proving
span-outcast.

Next mark one retained j in Q by P in v and w. Their other retained
inputs stay N. Again the columns lie in R. The output at v is P,
so the output at w is P and j remains in its canonical Q'. This
proves Q subseteq Q'. Monotonicity of the atomic sets gives the
reverse inclusion. If Q was empty that reverse inclusion already
proves equality. Thus Q-outcast holds and (6) is proved.

Both properties in (4) hold for the canonical closures of F, so this
establishes preservation of R for (1).

## Equivalent closed mixed-closure tests

Writing B=J\Q, conditions (4) are equivalent to the following two
tests for each owner r:

    c_r(E_r union B) intersects Q = empty;
    c_r(E_r union B)=V implies c_r(E_r)=V.                (7)

Necessity restores all of B to r. For sufficiency, a restoration adds
only a subset of B to each atomic set. Monotonicity gives both
Q preservation and absence of a new spanning owner. The reverse
spanning implication is automatic by monotonicity. When Q is
nonempty the second line follows from the first; it retains content
when Q is empty.

There is also a closure-only form of the first line. For every full
coloring a:V->I put

    d_a(T)=UNION_r c_r(T intersect a^(-1)(r)).             (8)

It is extensive, monotone and empty-preserving. Full Q-outcast is
equivalent to idempotence of every d_a. Taking complements identifies
this with idempotence of Q_a; outcast gives that identity by restoring
J\Q_a(J) to its a-colors. Conversely, choose a matching an initial
partial coloring and its proposed restored colors. Then

    T subseteq T union D subseteq d_a(T).

Monotonicity and idempotence give d_a(T union D)=d_a(T), which says
that the restored union of owner closures has the same complement Q.
Thus (8) is a closed mixed-closure axiom, not a term-search condition.

## Omission independence makes span-outcast redundant

For candidate loopless closures, assume their spanning profiles are
admissible, full Q-outcast holds, and the old source formula satisfies
omission independence. Then span-outcast follows. In particular it need
not be an additional axiom when those conditions are already present.

The [colorful-cover and omission lemmas](separable-closures.md) give
nonemptiness and the exact atomic-profile law. Q-outcast supplies strong
source attribution, so at any fixed status pattern the old output is

    A union UNION_(j in Q) w_j.

First suppose A!=I, and choose k outside A. Give every blocked ambiguous
position J\Q menu I, and every Q-position menu I\{k}. These menus are
ambiguous because K>=3. The output omits k. Omission independence
therefore permits arbitrary atom replacements at any of the blocked
positions without changing the output. The exact atomic-profile law
implies that the spanning owners are unchanged. This proves span-outcast
on every unsaturated pattern, in particular whenever a color is absent.

Here is the abstract bootstrap from missing-color patterns to all
patterns. Suppose restoring B subseteq J\Q to r creates a new r-span.
For k!=r put B_k={b in B:{s:b in c_s(E_s)}={k}}.
If B_k alone does not create the span, first restore it to r and then
erase k-atoms. Every remaining b in B\B_k keeps an original non-k
shadow and is blocked. The r-set has not changed in the erasure and
still does not span. Missing-color span-outcast would forbid the
remaining restoration from creating the r-span, a contradiction.
Thus B_k alone creates the r-span for every k!=r.

Choose h different from r,k. In the original pattern erase h-atoms.
All B_k remain k-blocked, while the unchanged r-set does not span.
Missing-color span-outcast now forbids restoring B_k to r from creating
the span, contradicting the preceding conclusion. This proves full
span-outcast. Mixed restorations reduce to a single owner because any
new spanning owner depends only on its own enlarged atomic set.

This missing-color bootstrap itself uses only
monotonicity and extensivity. The two other colors are the reason for
the K>=3 hypothesis.

## Attainment and its limits

The canonical candidate is an upper bound on all term-induced B_I
extensions and has the structural laws above. Neither these laws nor
(6) prove that it is a word operation. Nor is it asserted to be the
greatest arbitrary flat-monotone extension of the old faces: such
extensions can exceed the pure-port product bound.

For arbitrary synthetic closure data, sufficiency of these laws is
actually false: the
[four-variable counterexample](separable-closure-counterexample.md)
satisfies both outcast laws, hereditary profile admissibility and
hereditary omission, and has core proper neutral faces and identification
minors, but its prescribed old operation and G_Q are noncore. This holds
for every fixed K>=3.

For an already genuine core target, G_Q attainment is also false in
general. The [complete-head circuit classification](complete-head-circuits.md)
gives source-separable core operations with one head and one private
anchor at each old owner. No realizer attains G_Q: a uniform
observer invariant forbids its fresh output when all heads are P and
each anchor has its own old atom. No head's canonical maximal full
type is actual either. The same classification computes the greatest
term-induced common-carrier extension: G_Q off that bad anchor
coloring, and anchor union on it. Short safe spines attain this
strictly smaller maximum.

Attainment is now proved for
[additive owner closures](additive-closure-characterization.md): a
component-spine construction gives every maximal full vector and a
single realizer attaining their greatest independent-flag completion.
It is also proved for the shared-context
[two-reciprocal-rule class](separable-closure-counterexample.md), whose
head spines and context projections attain the canonical vectors.
For complete-head circuits any context overlap restores these
maximal vectors, including at an isolated head context.

The B_I input statuses used here have disjoint old atomic sets E_r.
Free independent-status polarization permits the same variable in
several owner sets simultaneously. Old-observer product attainment
is a separate question from G_Q or full-vector attainment. The
disjoint-context counterexample actually attains its greatest product
at all old observers, even with independent flags; its failure occurs
at a new observer. The general intrinsic guard characterization and
old-observer product-attainment problem remain open.
