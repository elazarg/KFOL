# Profile relations and one output bound

These results simplify parts of the intrinsic-characterization problem. They
do not settle simultaneous realization of complete source guards.

## Every closed relation of profile bits has a restricted Horn theory

A Boolean bit has an owner. The owner's gate takes OR in its own group and
AND in the other groups. With three available owners, the finite relations
closed under all gates are exactly models of:

- forced true bits;
- implications within a single owner group;
- forbidden conjunctions with at most one bit of each owner.

The empty conjunction represents the empty relation. No nonemptiness or
surjectivity assumption on the owner map is needed. The converse uses the
coordinatewise AND derived from three owners and minimal Horn clauses. A
minimal infeasible positive premise cannot repeat an owner; a minimal
feasible implication can have only one antecedent, at its conclusion's owner.

`Definitions/ProfileRelations` contains the independent theory vocabulary;
`Core/ProfileRelations` proves the classification and its canonical version.

## A single bound with rainbow positive demands has a two-leaf witness

Let J be a finite set of owners and A_r their requested winning coalitions.
Put C = intersection of all A_r. At input w, let E_s be the variables whose
value is exactly singleton s. For an allowed winner set U, a core term can
satisfy all these positive demands and have t(w) contained in U exactly when
C is nonempty and at least one of the following holds:

1. Some l in C has w_l contained in U.
2. Some s in J intersection U has E_s intersected with all A_r for r != s
   nonempty.

The first case is witnessed by projection x_l. The second is witnessed by
x_j star_s x_l, taking j from the second intersection and l from C. For
necessity, a singleton root gives a common-source witness with E_s; an
ambiguous root acts as union, and one child retains every rainbow demand.
This proof uses no bound on the number of owners or variables.

## Complete prescribed profiles under one bound

The complete profile table has a closed criterion, now proved in
`Core/ProfileBounds`. Put P_U={j:w_j is contained in U} and E_s={j:w_j={s}}.
For one owner r and coalitions A,B, define PairSafe_r(A,B) by:

1. (A\B) intersects P_U; or
2. r belongs to U, A\B is nonempty, and E_r\B is nonempty; or
3. A\B is nonempty and A intersects E_s for some allowed s different from r.

This is exactly existence of a bounded term with Phi_r(A)=1 and Phi_r(B)=0.
Its negation is the explicit implication preorder on that owner's coalitions.

A prescribed tuple Phi has an exact bounded realizer iff its top bits are
true, every true/false same-owner bit pair satisfies PairSafe, and every
full-owner selection of winning coalitions satisfies the preceding rainbow
budget criterion. The proof applies the restricted Horn classification to
the actual relation of bounded-term profiles. Forced bits are handled by
pairing them with their owner's top bit. Partial rainbow conflicts extend
with top coalitions for unselected owners.

There is no auxiliary presentation or recursive process on the criterion's
right side. When U is unrestricted, PairSafe is just A not contained in B,
and the rainbow budget condition is just common-source intersection; Lean
proves exact recovery of `AdmissibleProfiles`, even at infinite arity.

## Separate owner families do not suffice

At three owners and four variables a,b,c,d, use

    w = (all three owners, singleton 2, singleton 0, singleton 0).

The target profiles (ab,ad,ac) are jointly admissible because all their
winning coalitions contain a. Each owner profile separately has a term
omitting owner 1 at w:

    a star_2 b,    a star_0 d,    a star_0 c.

No joint realization omits 1. The two positive demands Phi_1(ad) and
Phi_2(ac) already force its presence: C={a}, whose value contains 1, and
the only potential permitted absorbing owner in J={1,2} is 2, but its
atomic-input set {b} misses {a,d}.

`Core/ProfilePersistence` proves the stronger uniform two-profile winner
persistence law and this full-profile counterexample without enumeration.
The new rainbow conflicts in constrained profile relations therefore cannot
be replaced by the original common-source conflicts plus separate owner
restrictions. Ternary computational evidence suggesting such a factorization
was misleading: a fourth variable suffices to refute it.

## Requested winners and exact one-point completion

For rainbow positive demands, adding a winner k at the bounded input has
three direct tests: the existing rainbow condition, an input containing k
wholly inside U, and PairSafe_r(A_r,E_r(w)) for each demanded owner r≠k.
There is no order search. Repair a bounded positive/negative separator by
attaching a common rainbow witness at every other demanded owner. Attach
these repaired branches to the eligible k-source. Foreign branches cannot
absorb away k; its own choice retains it.

For full prescribed profiles Φ and one exact nonempty output T, the exact
condition is bounded-profile feasibility under T, atomic compatibility
Φ_r(E_r(w)) iff T={r}, and whole-input coverage of T. Start with a bounded
profile witness and reset eligible source inputs against it. This preserves
all profiles; ambiguous outputs grow to T, while atomic compatibility
already fixes any atomic output.

These criteria are kernel-checked in `Core/ProfileQueries` and
`Core/ProfileCompletion`. Whole-input provenance is proved uniformly over
arbitrary role and variable types in `Core/WholeInputs`.

The existing five-point obstruction passes the exact one-point criterion
at every input for one fixed admissible profile tuple, but has no global
core realization (`Core/ProfilePointObstruction`). Thus even these complete
pointwise tests do not give the sought global guard characterization.

## Remaining target

Full source guards require many output bounds simultaneously. Even a known
core upper bound does not make separate OneBound tests sufficient. The
following uniform K>=3 counterexample supersedes the earlier unrelated
two-bound example. Its complete written proof is in
[appendix-core-profile-gluing.tex](../../../sections/appendix-core-profile-gluing.tex),
`core:prop:profile-bound-gluing` and `core:cor:pointwise-helper-obstruction`;
it has not been formalized in Lean.

For distinct owners a,b,c put

    P=x star_a y, S=x star_b y, Q=P star_c z, R=z star_c x,
    C=(S star_b z) star_a Q,
    H0=(R star_b S) star_a Q,
    H1=(R star_a P) star_c (P star_b z).

The baseline C has six leaves. Both seven-leaf helpers have the exact
profile tuple

    phi_a=z(x OR y), phi_c=xy, phi_r=xyz for r outside {a,c}.

This extends C's profiles, which differ only by phi_c(C)=xyz. At EVERY
valuation one of H0,H1 is contained in C. If z=c and one of x,y=b,
H0=C=bc; otherwise H1 is contained in C. This case split works for
arbitrary menus and extra owners, without finite enumeration.

Nevertheless no core H<=C has c-profile xy. At u=(a,b,c), v=(a,c,b),
the baseline outputs bc,ab. Every term satisfying these two bounds obeys

    Phi_c(xy) implies Phi_c(z).

A root-to-leaf descent proves this. Keep a positive xy bit, a negative
z bit, and both bounds. The value at v must be ambiguous, so its bound
passes to both children. At u only a b-absorber is possible. If there is
one, select that child; its b-winning coalition {y} excludes a c-winning
coalition {z}. Otherwise choose a child preserving the positive/negative
c-bits. The sole jointly safe projection is z, which fails the xy bit.

This is also a counterexample on the specific mask-downset relevant to
actual interval types. Set psi_c=xy, all other masks zero. The inactive
inherited profiles together with psi_c are exactly phi. On the omitted
trigger face x=y=c any such helper equals c and C=c union z, so bounding
it only on the no-mask region is equivalent to bounding it everywhere.
In F=C union T the sound full type B_c=not xy, B_r=1 otherwise therefore
passes inherited-profile admissibility and EVERY separate one-point budget,
yet is not actual. An actual type would linearize to T star_c H with
H<=C and Phi_c(H)=xy.

Even ONE POSITIVE profile requirement can fail to glue under a known core
bound; negative profile data are not the sole cause. Put

    D=(S star_b z) union Q.

At every input either the whole x-menu or the whole y-menu lies in D.
If the b-fold is not b, D is full input union. Otherwise its b-absorber
and Q's possible c-absorber ensure that D contains a whole b/c input
among x,y; if Q does not absorb, it contains P, hence both x,y or an
a-singleton among them. Thus projections x,y give pointwise witnesses
for the SINGLE demand Phi_a(xy)=1.

No joint witness exists. At the same atomic rows u,v, D outputs bc,ab.
With a-positive xy the v-output cannot be a (its a-atomic coalition is
the same at u), b (its b-atomic coalition z misses xy), or c (the bound).
Thus that bound always passes to both children. At u a is forbidden and
c cannot absorb, by the disjoint positive a-quorum. Select a b-absorbing
child if present, otherwise any child retaining the positive a-bit.
No bounded positive projection exists. This is
`core:prop:positive-profile-gluing`, with a uniform written proof.

Thus the missing compatibility is genuinely simultaneous, including for
one active mask over a known core interval. It cannot be removed by
intersecting the complete theories of individual bounds.
