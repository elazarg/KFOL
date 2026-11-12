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

One bound and rainbow demands are a restricted interpolation problem. Full
source guards require many bounds simultaneously, and profile descriptions
also involve more than one coalition per owner. Neither the Horn
presentation nor the two-leaf theorem removes those interactions. The short
direct structural characterization of jointly realizable guards remains open.
