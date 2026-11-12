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

## Remaining target

Full source guards require many output bounds simultaneously. Intersecting
the complete theories of individual bounds is insufficient: on three
variables, the profile tuple (XYZ,XYZ,X) separately fits the bounds

    w=({0,2},{2},{1}), omit 1;
    v=({1},{2},{0}), omit 2,

but no common term realizes that tuple under both bounds. Here is a direct
argument, not yet a public Lean claim. At the first row every joint-safe
term must be ambiguous: it cannot be atom0 because no input is atom0;
atom1 is forbidden; atom2 would also occur at the second row, which has the
same set {Y} of atom2 inputs. At the second row it cannot be atom0 either:
the first-row bound and omission independence permit replacing Z=1 by Z=0,
whereupon its atom0 tests match the second row. This would make its first-row
value atom0, already excluded.

Induct on a joint-safe term. There is no absorber at the first row. If there
is an absorber at the second, its value must be atom1, giving Phi1({X})=1.
Otherwise both children satisfy both bounds, so induction forces that same
positive profile bit in both children and hence at the root. The only
joint-safe projection is X. Thus every joint-safe term has Phi1({X})=1,
contradicting the target's unanimity profile for owner1.

Separate exact-profile witnesses can be written without enumeration. Put
A=X star_2 (Y star_2 Z). The first row is handled by

    (X star_0 A) union (X star_1 A),

and the second by

    (X star_1 A) union (X star_2 (Z star_0 Y)).

Their profiles are both (XYZ,XYZ,X); their designated outputs are {0,2}
and {0,1}, respectively. This is a written research proof, not a report claim.

The complete one-bound theorem therefore leaves a genuine compatibility
problem across rows. The short direct structural characterization of jointly
realizable guards remains open.
