# Two patterns do not amalgamate

Mathematical research, without Lean claims. The complete
[one-pattern interpolation theorem](free-pattern-interpolation.md) does not
extend by checking each independent-status pattern separately. A ternary
example has maximal admissible profiles and a unique ordinary winner
operation. Its proposed free coefficients are antitone, agree with every
ordinary one-hot coefficient, and are jointly realizable at each fixed
pattern across all eligible sources and all observers simultaneously.
No single word realizes them at all patterns. Two queried coefficients at
different patterns give the obstruction. The same laws give an exact
thirteen-element description of the six poison-corner records. With exactly
three old owners, those records classify the entire old-observer free
extension fibre.

The two-query law first fixes an observer outside {a,b}. The final
completion and its pointwise realization concern every old or fresh
observer at a common global independent-status pattern.

## The quota fibre and the two queries

Let V={X,Y,Z}, let I have at least three old owners, and choose distinct
owners a,b. Fix an observer k outside {a,b}; it may be an old third owner
or a fresh unowned observer. Prescribe

    Phi_a = Phi_b = majority(X,Y,Z),
    Phi_h = X AND Y AND Z       for h outside {a,b}.

This tuple is maximal admissible. The
[tight-quota theorem](near-unanimity-size.md) identifies its unique ordinary
winner operation U: return {a} or {b} if that singleton occurs at least
twice among the three inputs, and otherwise return the full input union.

Write E^(i) for the independent pattern

    E_a=E_b={i},
    E_h=empty                  for every other old h!=k.

If k is old, its irrelevant flag set is also taken empty. At E^(i) the two
other variables are eligible sources. Define

    q_XY(S)=C_(X,k)^S(E^(Y)),
    q_YZ(S)=C_(Y,k)^S(E^(Z)).

**Two-pattern persistence.** Every word with profiles Phi satisfies

    q_XY OR q_YZ = 1.                                     (1)

The same law holds after any permutation of X,Y,Z.

## Proof of the two-query law

First note a consequence of the same-owner separator lemma from
[one-pattern interpolation](free-pattern-interpolation.md). For either
r=a or r=b, a word with q_XY=0 must satisfy

    Phi_r({X,Z}) implies Phi_r({Y,Z}).                     (2)

Indeed, take A={X,Z}, B={Y,Z}, and J={X} in that lemma. The difference
A\B is {X}; E_r={Y} lies in B; and every foreign nonobserver flag set
misses A. Every alternative in PairSafe_J is therefore false. A positive
A-bit and negative B-bit would force q_XY=1. The second zero query gives

    q_YZ=0 implies Phi_r({X,Y}) -> Phi_r({X,Z}).            (3)

Consequently, if both queries vanish, each owner r in {a,b} has the chain

    Phi_r({X,Y}) <= Phi_r({X,Z}) <= Phi_r({Y,Z}).

This conclusion applies to any word with the two zero bits, without
assuming its complete profiles Phi.

Suppose a word with profiles Phi and both zero queries exists, and
choose one with the fewest primitive gates. It cannot be a leaf.

At its root both zero queries pass to both children. At an a-root,
the parent's a-profile is zero on every singleton. The own-owner OR
recurrence makes both children's a-profile zero on every singleton, so
the a-filter at each query is open in both directions.
The queried source coefficient is therefore the OR of its child
coefficients. The b-root argument is identical. At any other owner's root
the relevant flag set is empty, so both singleton profiles at that flag
set are zero and the filters are open. An observer-owned root directly
takes OR. Thus both children have both zero queries.

If the root owner is a, some child owns the positive a-profile at {X,Y}.
By (2)--(3), that child owns all three positive a-pair bits. The b-profile
takes AND at this root, so both children already own all three b-pair
bits. The selected child's profile tuple therefore dominates Phi: the
remaining owners' unanimity positives are top bits and hold in every word.
Maximal admissibility forces that child's complete tuple to be exactly
Phi. This gives a smaller word with the same profiles and both zero
queries, contradicting minimality.

The b-root case is symmetric. At a root outside {a,b}, both majority
profiles take AND, so both children's tuples dominate Phi and hence equal
Phi. Either child again contradicts minimality. This proves (1).

## Every individual whole pattern is feasible

For a pivot p, write the other two variables as u,v and use

    T_p=(u choice_a v) choice_b
            (p choice_a (u choice_b v)).                  (4)

Its a-profile is `(u OR v) AND (p OR (u AND v))`, its b-profile is
`(u AND v) OR (p AND (u OR v))`, and both are majority. Every other
owner's profile is unanimity. At the poison pattern E^(v), its source-u
coefficient is zero and its source-p coefficient is one. Both occurrences
of u are blocked immediately by v, while the pivot's a- and b-sibling
profiles at {v} are zero. The same word with u,v interchanged gives the
corresponding pair at E^(u).

Thus the following two whole-pattern source vectors are individually
realizable with the same full profiles:

    E^(Y): (C_X,C_Z)=(0,1), supplied by T_Z;
    E^(Z): (C_Y,C_X)=(0,1), supplied by T_X.

Their two displayed zero requirements cannot hold in one word by (1).
The number of patterns is sharp, since either individual whole pattern
has the displayed pivot realizer.

## Exact free coefficients of a pivot

Fix a global independent pattern E=(E_h)_(h in I). For each old or fresh
observer k, ignore E_k when k is old and put

    L_k(E)=V \ UNION_(h!=k) E_h.

These are its eligible sources. The greatest quota coefficient is

    Cmax_(j,k)(E)=AND_(h!=k) [|E_h|<t_h],

where t_a=t_b=2 and all other thresholds are three. For an eligible source
j every foreign E_h omits j and has at most two elements. Thus the
threshold-three factors are always true on their relevant source domains.

For the pivot (4), with nonpivot variables u,v, the exact coefficients are:

    k=a or k=b:
        C_(j,k)^T_p(E)=Cmax_(j,k)(E) for every eligible j;

    k outside {a,b}:
        C_(u,k)^T_p(E)=Cmax_(u,k)(E)
                         AND NOT [v in E_a intersect E_b];
        C_(v,k)^T_p(E)=Cmax_(v,k)(E)
                         AND NOT [u in E_a intersect E_b];
        C_(p,k)^T_p(E)=Cmax_(p,k)(E).                      (5)

These formulas hold with arbitrary other-owner flags; T_p has no gates
owned by those owners.

Here is a direct evaluation. Write a_w=[w in E_a] and b_w=[w in E_b].
For an outside observer and eligible source u, the two u-occurrences in
(4) contribute

    (NOT a_v AND NOT (b_p AND b_v))
        OR (NOT a_p AND NOT b_v).

This is exactly

    NOT (a_v AND a_p) AND NOT (b_v AND b_p)
        AND NOT (a_v AND b_v),

which is (5). Interchanging u,v proves the other nonpivot formula. The
single pivot occurrence has exclusion factors
`NOT (a_u AND a_v)` and `NOT (b_u AND b_v)`, giving Cmax.

At observer a the a-gates are unfiltered. For source u the contributions
give `NOT (b_p AND b_v) OR NOT b_v`, hence
`NOT (b_p AND b_v)`; source v is symmetric, and the pivot gives
`NOT (b_u AND b_v)`. These are exactly its three Cmax coefficients.
At observer b the two u-occurrences give `NOT a_v OR NOT a_p`, hence
`NOT (a_v AND a_p)`; source v is symmetric and the pivot gives
`NOT (a_u AND a_v)`. This proves the remaining part of (5). Own-observer
flags are not used in these computations.

## An entire antitone completion

The obstruction extends to a coefficient prescription for all observers
at every independent pattern, not just the two assignments above. For
every old or fresh observer k and eligible source j prescribe

    G_(j,k)(E)=Cmax_(j,k)(E) if k=a, k=b, or j=Z;
    G_(X,k)(E)=Cmax_(X,k)(E)
                  AND NOT [Y in E_a intersect E_b] otherwise;
    G_(Y,k)(E)=Cmax_(Y,k)(E)
                  AND NOT [Z in E_a intersect E_b] otherwise. (6)

For each fixed source and observer, (6) is antitone on the independent
passive flag domain. It agrees with the
[greatest quota coefficients](quota-normal-form.md) at every ordinary
one-hot pattern, since different singleton flags are disjoint. Thus it
has exactly U's canonical ordinary source guards at every observer.

**All-observer pointwise realization.** At every global independent
pattern E, one five-leaf pivot word has profiles Phi and simultaneously
realizes every coefficient (6) at every eligible source and every old or
fresh observer.

If |E_a|>=2 or |E_b|>=2, choose any pivot. Every outside observer's eligible
coefficient Cmax is zero. At observers a,b, (5) already equals Cmax.

Suppose both sets have size at most one. If their intersection is empty,
every pivot's extra exclusions in (5) are true. Any pivot therefore
realizes Cmax at every observer, as required by (6).

Otherwise E_a=E_b={i}. Choose T_Z if i=Y, and T_X if i=X or i=Z.
At every outside observer i is ineligible, because it belongs to both
foreign flag sets E_a,E_b. If i=Y, formula (5) for T_Z kills X and retains
Z. If i=Z, formula (5) for T_X kills Y and retains X. If i=X, the pivot
T_X retains both eligible nonpivot sources Y,Z. These are exactly the
three cases of (6). Further flags may make sources ineligible but do not
change any pivot coefficient. At observers a,b every pivot again equals
Cmax by (5), independently of all own-owner flags.
This covers every global pattern and proves the simultaneous assertion.

Nevertheless (6), at the fixed outside observer used in (1), sets
q_XY=q_YZ=0. No single old-owner word with profiles Phi induces G.
The failure therefore persists after requiring antitonicity, all ordinary
one-hot guards, and simultaneous one-pattern feasibility across the
complete observer family.

## The complete six-corner image

Fix the outside observer k again, and consider all six coefficients
`C_(u,k)(E^(v))` with u!=v. Record a zero coefficient as a directed edge
u->v. Then the possible records are exactly:

* the empty edge set;
* any one of the six singleton edge sets;
* any one of the three opposite pairs u->v and v->u;
* any one of the three outgoing stars u->v and u->w.

Thus there are exactly thirteen records. This is a structural
classification, not a count inferred from clone enumeration.

Equivalently, the zero-edge graph has no vertex reachable from every
vertex, or has at least two sink strongly connected components. On three
vertices a forbidden incoming pair or directed two-edge path has such a
reachable vertex; the four listed graph forms do not. Conversely the
classification below excludes every other graph. This is a single closed
graph condition on the six coefficients.

For necessity, common-source-set persistence from
[free-profile-nonattainment.md](free-profile-nonattainment.md) forbids two
edges with the same head: at E^(v), the two eligible source coefficients
cannot both vanish. Equation (1) forbids a directed path u->v->w with
three distinct vertices. Any two remaining edges must therefore be an
opposite pair or an outgoing star. Neither kind permits a third edge:
it would create either two edges with the same head or a forbidden
two-edge path.

For sufficiency, a pivot T_p has exactly the opposite pair between its
two nonpivot variables, by (5). To obtain the outgoing star at X use

    S_X=((X choice_a Y) choice_b Z)
             choice_a ((X choice_a Z) choice_b Y).         (7)

It has six leaves. Its a-profile is

    ((X OR Y) AND Z) OR ((X OR Z) AND Y),

and its b-profile is

    ((X AND Y) OR Z) AND ((X AND Z) OR Y).

Both are majority, while every other owner's profile is unanimity.
At a poison singleton the two children of its root have a-profile zero,
so the root takes OR on source coefficients. The source-X coefficient is

    (NOT [Y in E_a] AND NOT [Z in E_b])
        OR (NOT [Z in E_a] AND NOT [Y in E_b]).             (8)

It vanishes at both E^(Y) and E^(Z). The other four corners equal one:
at E^(Y) source Z survives through the left branch, at E^(Z) source Y
survives through the right branch, and at E^(X) source Y survives through
the right branch while source Z survives through the left branch.
Thus S_X has exactly the outgoing star X->Y,X->Z. Permuting the variables
gives the other two stars.

Finally, combine two words having profiles Phi by any one primitive owned
choice. Their profiles remain Phi. At every poison corner the queried
coefficient is the OR of the two input coefficients: an a- or b-filter
sees the negative singleton profile, every other foreign filter sees the
empty coalition, and an observer-owned gate directly takes OR. Therefore
the new zero-edge record is the intersection of the two records.

Intersect the opposite pair {u->v,v->u} with the outgoing star
{u->v,u->w} to obtain the singleton {u->v}. Intersect two distinct
opposite pairs to obtain the empty record. This supplies every listed
record and completes the exact classification.

## Exactly thirteen full old-observer extensions at three owners

Now restrict the old owner set to exactly I={a,b,c}. Consider the entire
collection of free source coefficients for the three old observers,
on all their independent passive patterns. No fresh-observer assertion
is included in this classification.

**Corollary.** The unique quota operation U has exactly thirteen
term-induced old-observer free extensions. Its extension is determined
by the six poison-corner bits at observer c, and their exact compatibility
conditions are the two graph prohibitions above: no two incoming edges
and no two-edge directed path with three distinct vertices.

For observer c, the only rival flag sets are E_a,E_b, both subsets of
the two passive variables. If either has size two, its majority profile
forces the source coefficient to zero. Otherwise both have size at most
one. Disjoint sets are an ordinary one-hot pattern, so the unique ordinary
operation U fixes the source coefficient at Cmax=1. The only remaining
case is E_a=E_b={i}; these are precisely the six poison corners. Thus the
six bits determine all observer-c coefficients.

Every observer-a coefficient is fixed, independently of E_c:

    C_(j,a)(E)=1 iff |E_b|<2.                              (9)

If E_b has size two, its positive b-profile forces the coefficient to
zero. Otherwise choose different j-containing pairs A_a,A_b with common
intersection {j}, choosing A_a to avoid E_b. This is possible because
E_b is empty or a singleton among the two passive variables. Put A_c=V.
These are positive profile coalitions. The b-avoidance condition is
E_b intersect A_a=empty. The c-avoidance condition is
E_c intersect A_a intersect A_b=E_c intersect {j}=empty, since the source
is excluded from every rival flag set. Free singleton-source persistence
therefore forces the coefficient to one. This proves (9), including
overlapping E_b,E_c.

Symmetrically, at observer b every coefficient is fixed by

    C_(j,b)(E)=1 iff |E_a|<2,                              (10)

independently of E_c. Hence two words with these profiles have the same
complete old-observer free extension exactly when their six observer-c
poison bits agree. All thirteen records have explicit word realizers, so
the count is exact for the full free extension fibre, not merely its
six-coordinate projection.

The six two-edge records give its six minimal extensions: three pivots
and three outgoing-star words. The six one-edge records are intermediate,
and the empty record is its greatest extension. Pointwise joining free
extensions intersects their zero-edge records, as witnessed by any owned
choice between profile-equivalent realizing words. In particular there
is no least extension.

The order is the opposite of face inclusion on the boundary of a hexagon,
including the empty face.
Its six vertices are the singleton zero edges; its six edges are the
three opposite pairs and three outgoing stars; its empty face is the
greatest extension. The compatible pairs form the cycle

    XY -- XZ -- ZX -- ZY -- YZ -- YX -- XY,

where XY denotes the zero edge X->Y. Thus the poset description, the
count, and the six minimal extensions follow from one explicit cycle.
