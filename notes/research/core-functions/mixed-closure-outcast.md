# Pairwise closure cuts and full colored outcast

Mathematical research, without Lean claims. Canonical colored outcast
holds for source-separable core operations, including saturated fibers.
It is equivalent to a pairwise cut law on the owner closures. A direct
proof uses their functional-dependence interpretation and a third
observing owner; no fresh-source selection or saturation case is needed.
Hereditary span-outcast likewise has a closed mixed-loop formulation.
These necessary laws do not give a complete realizability criterion.

Fix finite owners I with K>=3, a finite nonempty variable set V, and
loopless owner closures c_r. Use the source reconstruction

    k in F(w) iff some j with k in w_j is outside
                         UNION_(r!=k) c_r(E_r(w)),
    E_r(w)={i:w_i={r}}.                                  (1)

For disjoint atomic sets E_r put

    J=V\UNION_r E_r;
    T_j={r:j in c_r(E_r)};
    A={r:E_r\UNION_(s!=r) c_s(E_s) is nonempty};
    Q=V\UNION_r c_r(E_r).

Extensivity gives Q subseteq J. At this status pattern, (1) says

    F(w)=A union UNION_(j in Q) w_j
          union {r:some j in J has T_j={r} and r in w_j}. (2)

The strong source-attribution condition is

    j in J and T_j={r} implies r in A.                   (3)

For genuine source-separable core operations it holds by
[canonical source attribution](separable-closures.md). Below it is also
derived directly from colored outcast for arbitrary loopless candidate
maps. Under (3), the last contributions in (2) are already contained in A:

    F(w)=A union UNION_(j in Q) w_j.                     (4)

Thus A is the constant atomic part and Q is the canonical whole-menu
selection set. Neither is defined using a realizing term.

## The pair-cut law

Consider the following closed condition for distinct owners r,s,
disjoint premise sets B,D, and i outside B union D:

    i in c_r(B) implies
        c_s(D union {i}) subseteq c_r(B) union c_s(D).    (P)

The different letters B,D denote premise sets, not the constant part A.
The condition says that transferring a consequence of one closure to
another owner cannot capture a point outside their existing closure
union. It permits joint premises of arbitrary size.

**Equivalence theorem.** For loopless closures, (P) holds if and only if
full Q-outcast holds: restoring any subset of J\Q to arbitrary owner
atoms preserves Q at every partial coloring.

For necessity take a pattern with B atomic at r, D atomic at s, and
everything else ambiguous. The point i is blocked by r. Restoring it
to s must leave the union c_r(B) union c_s(D) unchanged. This gives (P).

For sufficiency restore one blocked ambiguous i to s. Choose an old
capturing owner r. If r=s, closure idempotence gives
c_s(E_s union {i})=c_s(E_s). If r!=s, apply (P) to B=E_r,D=E_s.
The enlarged s-closure stays within the old closure union, which therefore
stays unchanged. For several restorations apply this argument one at
a time. Every remaining originally blocked point stays blocked because
all atomic sets and their closures only grow. This proves full outcast.

## A direct proof of pair-cut for core operations

**Theorem.** The canonical owner closures of every genuine source-separable
core operation satisfy (P), hence full Q-outcast, for K>=3.

Use the [cofactor-dependence theorem](cofactor-dependence-closures.md):
fixing B to {r} makes every input in c_r(B)\B inessential in the whole
winner-valued function. Suppose (P) fails, so there is

    j in c_s(D union {i}) but j outside c_r(B) union c_s(D).

In particular j is distinct from i and lies outside B union D. Choose
an observing owner k different from r,s, and let N_k=I\{k}.
Give B the r atom, D the s atom, and every other input N_k, except
that j may have either I or N_k. Both menus are ambiguous. At these
statuses j lies outside every rival closure. It is the only potential
source of k, so (1) makes the two outputs differ on k.

But i in c_r(B)\B means that replacing i by {s} preserves both outputs.
After this replacement D union {i} is fixed to {s}. Since
j in c_s(D union {i}), functional dependence now makes the output
independent of j. The two outputs must agree, a contradiction.

This proof establishes (P) directly on two-color patterns. The abstract
equivalence then proves full outcast even when all old owner atoms are
present and the constant part A is the entire I.

## Equivalent full-pattern tests and canonical interiors

Put B=J\Q. Full Q-outcast is equivalently the K tests

    c_r(E_r union B) intersects Q = empty for every r.    (5)

Necessity restores all B to r. Conversely every restoration adds only
a subset of B to each atomic set. Monotonicity bounds its enlarged
closure by c_r(E_r union B), so it cannot capture a point of Q.
Closure monotonicity also prevents any previously blocked point from
becoming free. This gives precisely the same Q.

For a full coloring alpha:V->I define

    Q_alpha(J)=V\UNION_r c_r({i outside J:alpha(i)=r});
    d_alpha(T)=UNION_r c_r(T intersect alpha^(-1)(r)).     (6)

Full Q-outcast implies that Q_alpha is an interior. Contraction follows
from closure extensivity, and monotonicity from shrinking the atomic
sets when J increases. If Q_alpha(J) subseteq J' subseteq J, restore
J\J' to their alpha-colors; outcast gives Q_alpha(J')=Q_alpha(J).
Taking J'=Q_alpha(J) proves idempotence.

Equivalently every d_alpha is a closure. Conversely, if every d_alpha
is idempotent, take any restoration B subseteq J\Q and extend the
original and restored colors to a full alpha. For T=UNION_r E_r,

    T subseteq T union B subseteq d_alpha(T).

Monotonicity and idempotence give d_alpha(T union B)=d_alpha(T),
which is exactly Q-outcast. Thus (P), (5), and idempotence of all
colored maps in (6) are equivalent closed formulations.

## Colored outcast implies source attribution

For loopless owner maps, full Q-outcast implies (3); this is not an
additional condition on a candidate already satisfying (P).

Suppose ambiguous j has T_j={r} but r is absent from A. Erase E_r.
Looplessness removes its only capture of j, making j free. Every
erased r-position remains captured by another owner, because

    r notin A implies E_r subseteq UNION_(s!=r) c_s(E_s).

All these erased positions are therefore blocked and may be restored
to r under outcast. This would recapture the free j, a contradiction.

## Full old-value outcast and atomic survivors

There is a stronger semantic statement for every core operation,
without requiring source separation. Fix any partial atomic coloring.
Every input of J\Q belongs to some c_r(E_r)\E_r, hence is inessential
once E_r is fixed to {r}. Further fixing all the other atomic sets
preserves that independence. Finite coordinate-by-coordinate changes
therefore permit arbitrary simultaneous menu replacements at J\Q
without changing the entire old winner set. The original atomic
positions are kept fixed throughout.

For source-separable core operations, atomic restorations also preserve
A, not only Q. To test any old winner k, first give all ambiguous inputs
the menu I\{k}. Formula (4) says k belongs to the output exactly when
k belongs to A. Restore the chosen blocked positions to their specified
atoms. Full old-value outcast preserves that output; formula (4) at
the new pattern, whose remaining ambiguous menus still omit k, detects
exactly the new A. This proves A'=A for every k.

The common-carrier selection of a chosen word may still be strictly
smaller than canonical Q at a saturated pattern. Input union already
exhibits that distinction. None of these proofs identifies the chosen
word's actual fresh selections with Q.

## A pairwise test for hereditary spanning stability

For every nonempty U subseteq V restrict c_r to U by intersection.
Span-outcast on every such restriction is equivalent to the following
closed mixed-loop law, for distinct r,s and disjoint B,D, with
i outside B union D:

    i in c_r(B) and B subseteq c_s(D union {i})
        imply i in c_s(D).                              (L)

For necessity, if the conclusion fails take U=B union D union {i}.
In that restriction i is blocked by r and may be restored to s. The
new s-set D union {i} spans U, but D did not span U since it misses i
in its closure. This violates hereditary span-outcast.

Conversely consider a single blocked restoration to s in a restriction
U which creates an s-span. Write D=E_s and choose a capturing owner r.
If i already belongs to c_s(D), idempotence forbids any change, so take
r!=s and put B=E_r. The new s-closure contains U and hence contains B.
Law (L) gives i in c_s(D), again a contradiction. Restorations one at
a time prove the assertion for arbitrary simultaneous restorations.
No colored-outcast or profile-admissibility assumption is needed for
this equivalence beyond the stated closure hypotheses.

## A stronger reciprocal capture cut

The reciprocal-rule persistence lemma is first a direct law for arbitrary
core guard tables, without source separation:

    C_(x,k)(q) implies C_(x,k)(u) or C_(y,k)(v).         (G2)

Here u,v,q are its disjoint-context template probes, with all deleted
inputs neutral at N_k. The law couples two different source positions.
A violation excludes a common core interpolant on these three rows.
Neutral elimination justifies the same law after lifting from a retained
variable set: the residual of any putative interpolant is core or zero,
and in either case obeys persistence.

There is a further necessary law for arbitrary source-separable core
operations. For distinct r,s, disjoint contexts L,M, and distinct
x,y outside L union M, it says

    y in c_r(L union {x}) and x in c_s(M union {y})
        imply {x,y} subseteq c_r(L) union c_s(M).        (C2)

Thus two differently owned captures cannot bootstrap two previously
free heads through disjoint contexts. The conclusion allows a reciprocal
capture only when those heads were already blocked by the contexts.

First take the neutral restriction to U=L union M union {x,y}.
For a genuine core F this restriction is core and source-separable,
with the restricted pure-owner closures. Membership of the two retained
heads in c_r(L),c_s(M) is unchanged by that restriction.

Use the universal three-row persistence lemma in
[the reciprocal-rule characterization](separable-closure-counterexample.md).
Choose an observing owner k distinct from r,s and put N_k=I\{k}.
At its u-row, x is the sole k-source and is captured by s from
M union {y}. At its v-row, y is the sole k-source and is captured by
r from L union {x}. Both k-bits are therefore zero, even if the
closure family has further rules. Persistence forces the q-bit zero.
But at q the atomic r-set is L, the atomic s-set is M, and x is
the sole k-source. The separable formula makes that bit zero exactly
when x belongs to c_r(L) union c_s(M). Exchange the two heads and
owners to obtain the same conclusion for y. This proves (C2).
Equivalently the three observer-k probe rows may be lifted to the
original variables by giving every deleted input N_k; the queried
k-bits are precisely those of the neutral restriction.

Law (C2) implies the hereditary mixed-loop law (L). Suppose the premises
of (L) hold but i is outside c_s(D). Choose an inclusion-minimal
T subseteq B with i in c_r(T). Looplessness makes T nonempty. Pick
x in T. The (C2) contexts T\{x},D and heads x,i satisfy its premises:
c_r(T) contains i, while c_s(D union {i}) contains every point of B
and hence x. Its conclusion puts i in c_r(T\{x}) or c_s(D), contrary
to minimality and the supposition. Thus (L) need not be checked
separately when (C2) is imposed.

There is a structural version in terms of the given minimal captures.
Write S =>_r y when y is outside S, y belongs to c_r(S), and no
proper subset of S captures y. For r!=s impose

    S =>_r y, T =>_s x, x in S, y in T
        imply (S\{x}) intersect (T\{y}) is nonempty.    (CI)

Thus reciprocal minimal captures of different colors must share an
additional witness. For the two-rule family this is exactly the
common-context condition; for additive closures it excludes opposite
arrows, whose additional premise sets are empty.

Law (C2) implies (CI). If the displayed intersection were empty, apply
(C2) to contexts S\{x},T\{y}. Minimality gives y outside
c_r(S\{x}). Also y is outside c_s(T\{y}): otherwise closure
idempotence would make x already captured by T\{y}, contradicting
minimality of T. This contradicts the conclusion of (C2).

Conversely, assume (P) and (CI). In a proposed instance of (C2), if
either head already belongs to c_r(L) union c_s(M), then both do.
For example x in c_r(L) gives y in c_r(L) by idempotence, while
x in c_s(M) gives y in that old union by (P); interchange heads for
the other cases. If neither is already captured, choose minimal
S subseteq L union {x} capturing y and minimal T subseteq M union {y}
capturing x. They necessarily contain x and y respectively. Their
additional premise sets lie in the disjoint L,M, violating (CI).
Hence (P),(CI) are equivalent to (P),(C2), without an auxiliary
presentation or a term quantifier.

In the additive setting, the empty-context instance of (C2) forbids
opposite differently colored arrows. Joint-premise dependencies need
its nonempty contexts as well: the
[prime four-variable counterexample](separable-closure-counterexample.md)
satisfies (P), (L), hereditary profile admissibility and hereditary
omission independence, and every proper neutral face and identification
minor is core, but
it violates (C2) on the heads B,C with contexts {A},{W}.
Thus (C2) is stronger than those earlier tests. No sufficiency result
for the combined general closure laws is asserted.
