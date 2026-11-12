# Closed partial-coloring tests and mixed closure outcast

Mathematical research, without Lean claims. These are necessary mixed
closure laws for source-separable core operations. The outcast theorem
below assumes an unsaturated initial constant part; it does not settle
the saturated case or supply a complete realizability criterion.

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

## An equivalent finite family of mixed closure tests

Let B=J\Q. At an unsaturated initial pattern, (9) is equivalent to the
K conditions

    c_r(E_r union B) intersects Q = empty
        for every owner r.                              (10)

Necessity follows by restoring all positions of B to the same atom r.
For sufficiency, any restoration adds to E_r only a subset of B.
Monotonicity bounds its new closure by c_r(E_r union B), which misses
Q by (10). No point of Q can become blocked. No new point outside Q
can become unblocked because all the old atomic sets remain present.
This is exactly (9).

Thus the outcast consequence is a closed mixed-elimination axiom on
the canonical owner closures: positions already blocked by some owner
may all be assigned to any one owner without closing an initially free
position. It needs K closure tests for each initial partial coloring,
without an auxiliary realization graph or a recursive recognition rule.

## Why the initially saturated case remains separate

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

It shows that the proof cannot simply identify actual and canonical
fresh selections at an initially saturated fiber. It does not show a
failure of the canonical Q-outcast law there: for input union, Q is
the identity interior and obeys outcast. Whether that canonical law
holds for all initially saturated fibers of source-separable core
operations is left open here.

The conditions in this note are necessary reductions, not a complete
mixed-closure characterization. The general joint source-guard target
is unchanged.
