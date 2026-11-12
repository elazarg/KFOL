# Closed partial-coloring tests and mixed closure outcast

Mathematical research, without Lean claims. These are necessary mixed
closure laws for source-separable core operations. Canonical outcast
holds at every partial coloring, including saturated fibers. The key
step is an abstract two-erasure lemma: with at least three colors,
outcast on colorings missing one color already implies full outcast.
These laws do not supply a complete realizability criterion.

Use the setting of [separable-closures.md](separable-closures.md): finite
owners I with K>=3, finite nonempty variables V, and canonical loopless
closures c_r. At a valuation w put E_r={i:w_i={r}}. Source separation
and reconstruction give

    k in F(w) iff some j with k in w_j lies outside
                         UNION_(r!=k) c_r(E_r).          (1)

Fix disjoint atomic sets E_r and let J=V\UNION_r E_r be the ambiguous
positions. Write

    C_r=c_r(E_r);
    T_j={r:j in C_r};
    A={r:E_r\UNION_(s!=r) C_s is nonempty};
    Q=V\UNION_r C_r.

Extensivity gives Q subseteq J. At this status pattern, (1) says

    F(w)=A union UNION_(j in Q) w_j
          union {r:some j in J has T_j={r} and r in w_j}. (2)

## The source-attribution hypothesis

Assume the strong source-attribution condition

    j in J and T_j={r} implies r in A.                   (3)

It is necessary for genuine source-separable core operations, as proved
in [separable-closures.md](separable-closures.md). It is stronger than
merely admitting a whole-menu selector on one fiber: a constant part
containing all but one owner can mask a partial menu contribution.

Under (3), all the last contributions in (2) already belong to A, so

    F(w)=A union UNION_(j in Q) w_j                       (4)

throughout the status fiber. The remaining tests have especially simple
closed forms in these coordinates.

## Nonemptiness and full atomic profiles

**Proposition.** Under (3), F is nonempty at every menu assignment of
this status exactly when A is nonempty or Q is nonempty.

If A is nonempty it is contained in every output. If Q is nonempty it
contributes a nonempty menu. If both are empty, (4) is empty.

Suppose this nonemptiness condition holds at every status pattern.
Then the full atomic-profile factorization

    F(w)={r} iff c_r(E_r)=V                              (5)

holds at all valuations exactly when the partial-coloring data obey

    Q=empty and A={r} implies c_r(E_r)=V                  (6)

for every status pattern and owner.

Indeed c_r(E_r)=V kills every non-r source in (1); nonemptiness forces
the output {r}. Conversely, if Q is nonempty, its whole ambiguous menu
makes (4) ambiguous. If Q is empty, the output is the fixed nonempty
set A, which is {r} exactly when A={r}. Thus (6) is precisely the missing
reverse implication. Pure-r probes alone do not provide this reverse
implication on mixed atomic patterns.

These tests quantify over partial atomic colorings, not the contents
of arbitrary ambiguous menus.

## Actual fresh selections and their canonical upper bound

Let a primitive old-owner word realize F, and interpret it on the common
carrier B_I with old atoms and N,P. At the fixed status pattern, let C
be the ambiguous positions whose change from N to P gives output P.
This is the word's actual unowned-source selection set.

Always

    C subseteq Q.                                       (7)

For a marked j occurrence, its full factors B_(occ,r) are bounded by
the pure-owner coefficients D_(j,r)=[j notin c_r(E_r)]. A fresh winner
uses every old-owner factor. Hence

    (some occurrence avoids every owner)
        implies (for every owner, some occurrence avoids it).

The right side is exactly j in Q. Equivalently the OR of occurrence
products is bounded by the product of the pure-owner ORs. This proves
(7) without assuming that the greatest free completion is term-induced.

If A!=I, condition (4) makes the actual set equal to Q:

    C=Q.                                                (8)

The same word's fixed-status evaluation on old winner menus gives a
whole-menu selector A_word union UNION_(j in C) w_j. Its constant part
is forced to be A: test each k by assigning every ambiguous input
I\{k}. For any k outside A, set one ambiguous j to I and the others
to I\{k}. Its k-bit detects j in C, while (4) detects j in Q.
Thus the selectors agree. This argument is exactly where A!=I is used.

## Outcast for an unsaturated initial fiber

**Theorem.** Suppose F is genuinely core and source-separable, and its
initial status pattern has A!=I. Restore any subset of J\Q to
arbitrary old-owner atoms, leaving Q ambiguous and keeping every initial
atomic position fixed. If E'_r is the new atomic pattern, then

    V\UNION_r c_r(E'_r)=Q.                               (9)

In particular the statement allows the new constant part A' to equal I.

By (8) the chosen word's actual initial selection set is C=Q. Its
whole-word strong outcast theorem, proved by the ternary invariant in
[colored-interiors.md](colored-interiors.md), preserves all these
selections after restoring unselected positions to arbitrary atoms.
Thus its actual new set C' is still Q. Apply the canonical upper bound
(7) at the new pattern to get

    Q=C' subseteq Q'=V\UNION_r c_r(E'_r).

On the other hand every E_r is contained in E'_r. Closure monotonicity
gives Q' subseteq Q. Hence Q'=Q, proving (9). No identification of the
actual and canonical selections at a saturated final fiber is needed.

This is a necessary condition for core operations. It is not inferred
from (3) or the closure laws alone.

## Two erasures remove the saturation hypothesis

The following argument is about the owner maps themselves. In particular,
it does not assume that the canonical Q is an actual word's fresh selection
set at a saturated pattern.

**Erasure lemma.** Let |I|>=3 and let c_r be monotone extensive maps on
subsets of V. For every partial coloring by disjoint sets E_r, define

    J=V\UNION_r E_r,    Q=V\UNION_r c_r(E_r).

Assume outcast holds whenever some color is absent: if E_h=empty for
some h, restoring any blocked ambiguous positions J\Q to old atoms
preserves Q. Then outcast holds at every partial coloring.

It is enough to rule out a single-owner restoration capturing one free
point. Indeed, if a mixed restoration captures j in a final c_r, the
positions newly colored r alone already cause this capture; the other
owner maps do not enter that particular test.

Suppose, towards a contradiction, that restoring B subseteq J\Q to r
captures j in Q:

    j in c_r(E_r union B).

For each b in B put T_b={s:b in c_s(E_s)}, which is nonempty. For a color
k!=r let

    B_k={b in B:T_b={k}}.

We first prove

    j in c_r(E_r union B_k) for every k!=r.               (10)

Otherwise first restore B_k to r. The point j is still free: only the
r-map increased, and by assumption it has not captured j. Now erase all
k-atoms, making them ambiguous. Monotonicity keeps j free. Every remaining
b in B\B_k is still blocked: its original nonempty T_b had some color
other than k; that owner's atomic set is unchanged or, for r, enlarged.
The resulting partial coloring has no k-atoms. Missing-color outcast
therefore allows us to restore the remaining B\B_k to r without
capturing j. The final r-set is E_r union B, contrary to the supposed
capture. This proves (10).

Choose distinct k,h different from r; this is where three colors are
needed. Return to the original pattern and erase only its h-atoms.
Again j stays free. Every point of B_k remains blocked by k, whose
atomic set was unchanged. This pattern is missing color h, so its
outcast law forbids restoring B_k to r from capturing j. But its r-set
after restoration is E_r union B_k, contradicting (10). QED.

Only monotonicity, extensivity and missing-color outcast were used.
Idempotence, profile laws and an underlying term are unnecessary for
this abstract implication.

**Full canonical outcast theorem.** If F is a source-separable core
operation with |I|>=3, restoring any subset of J\Q to arbitrary owner
atoms preserves the canonical free set Q, including when A=I initially.

Indeed a pattern missing color h has h outside A, so the previously
proved unsaturated theorem gives precisely the premise of the erasure
lemma. Apply the lemma to the canonical owner closures.

## An equivalent finite family of mixed closure tests

Let B=J\Q. At every initial pattern, full outcast is equivalent to the
K conditions

    c_r(E_r union B) intersects Q = empty
        for every owner r.                              (11)

Necessity follows by restoring all positions of B to the same atom r.
For sufficiency, any restoration adds to E_r only a subset of B.
Monotonicity bounds its new closure by c_r(E_r union B), which misses
Q by (11). No point of Q can become blocked. No new point outside Q
can become unblocked because all the old atomic sets remain present.
This is exactly (9).

Thus outcast is a closed mixed-elimination axiom on
the canonical owner closures: positions already blocked by some owner
may all be assigned to any one owner without closing an initially free
position. It needs K closure tests for each initial partial coloring,
without an auxiliary realization graph or a recursive recognition rule.

## Canonical colored interiors

Fix any full old-atom coloring a:V->I. For J subseteq V put

    Q_a(J)=V\UNION_r c_r({i outside J:a_i=r}).             (12)

**Corollary.** Q_a is a contractive, monotone, idempotent map, and

    Q_a(J) subseteq J' subseteq J implies Q_a(J')=Q_a(J).

Extensivity of each c_r gives contraction. Increasing J shrinks every
atomic set; closure monotonicity therefore increases Q_a(J).
For the displayed outcast identity, restore J\J' to their a-colors.
These are blocked positions because J' contains Q_a(J). Full canonical
outcast gives the identity. Taking J'=Q_a(J) proves idempotence.

These interiors are determined directly by the old operation's canonical
pure-owner ports. A chosen realizing word can have fewer actual fresh
selections at saturated fibers; no equality with that chosen word's
interiors is asserted there.

Equivalently, every full coloring a defines a closure

    d_a(T)=UNION_r c_r(T intersect {i:a_i=r}).             (13)

It is the complement-dual of Q_a, so it is extensive, monotone and
idempotent. Thus all these differently colored closure computations can
be united in one step without creating a new consequence on a second
step. This is a closed condition on the original owner maps.

Conversely, idempotence of every d_a is equivalent to full canonical
outcast for any family of extensive monotone owner maps. For an initial
partial coloring put T=UNION_r E_r. Given a proposed restoration of
B subseteq J\Q, extend both the initial colors and the restored colors
to a full coloring a. Then

    T subseteq T union B subseteq d_a(T),

so monotonicity and idempotence give d_a(T union B)=d_a(T). These are
exactly the old and restored unions of owner closures. Their complements
are the same Q. This proves the converse without a realizing word.

## Colored outcast implies source attribution

**Corollary.** For loopless owner maps, full colored outcast already
implies (3). Thus a candidate satisfying the closed colored-closure
condition need not impose source attribution as a separate axiom.

Suppose an ambiguous j has T_j={r}, but r is absent from A. Erase the
atomic set E_r. Looplessness gives c_r(empty)=empty, so j is now free;
all other owner maps remain unchanged and did not capture it. Every
erased position is still blocked by another owner, since

    r notin A implies E_r subseteq UNION_(s!=r) c_s(E_s).

Restoring precisely these blocked positions to r is an outcast
restoration. It would recapture j in c_r(E_r), a contradiction.

This argument uses neither nonemptiness nor the atomic-profile law.
In deriving colored outcast for actual core operations above, source
attribution was already supplied by its independent occurrence proof;
there is no circularity in subsequently deriving it from the closed
condition for arbitrary candidate maps.

## Why actual and canonical selections must still be distinguished

When A=I, old winner semantics cannot detect whether an additional
ambiguous input is selected: the fixed atomic contribution is already
the entire old role set. Equality (8) need not hold for a chosen word.

For example take variables x,y_r for r in I and the old input-union
operation. On the old winner carrier both words

    x union UNION_r y_r,
    (UNION_r y_r) union UNION_r (x choice_r y_r)

realize it. At y_r=atom r, x ambiguous, their canonical closure data
are identities, A=I and Q={x}. In B_I with x=P, the first word returns
P. In the second every marked owned summand is absorbed to its old
atom r; their union is N and the actual selection set is empty.
This is the sharp identity-stability example from
[unowned-observer.md](unowned-observer.md).

It shows why the proof cannot simply identify actual and canonical
fresh selections at an initially saturated fiber. The two-erasure
argument proves canonical outcast without making that identification.

## Three colors are necessary for the abstract implication

The erasure lemma's color hypothesis is sharp even for loopless
closures. With two colors and V={a_0,a_1,b,j}, put

    c_0(E)=E union ({j} if {a_0,b} subseteq E else empty),
    c_1(E)=E union ({b} if a_1 in E else empty).

These maps are monotone, extensive, idempotent and empty-preserving.
They obey outcast whenever a color is missing. If E_0 is empty, the
only possibly blocked ambiguous position is b, and restoring b cannot
activate the 0-rule without the free anchor a_0. Restoring it to 1
does not change c_1. If E_1 is empty, the only possibly blocked
ambiguous position is j, whose restoration cannot activate the 1-rule
without a_1 or change the premises of the 0-rule.

But at E_0={a_0}, E_1={a_1}, both b,j ambiguous, Q={j}. Restoring the
blocked b to 0 captures j. Thus missing-color outcast does not imply
full outcast for two abstract owner closures. No two-owner core
realizability claim is made for this example.

The conditions in this note are necessary reductions, not a complete
mixed-closure characterization. The general joint source-guard target
is unchanged.
