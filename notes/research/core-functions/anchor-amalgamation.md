# Choosing one canonical anchor does not give global completeness

This is a mathematical obstruction to a possible use of the
[anchored normal form](coherent-cube-safety.md). It does not refute that
construction's local exactness. Even a function with a disjoint read-once
realizer need not have any globally exact anchored normal form.

Use endpoint names 0,1 for b,c in the bichain B={0,1,N,P}. Thus meet is
minimum in 0<P<N<1 and join is maximum in 0<N<P<1. Products and sums below
mean these operations when evaluating terms, and Boolean AND/OR when
describing their Boolean functions. Write T(f,v) for the anchored construction.

## Neutralizing an independent factor commutes with the construction

**Lemma.** Let g(X) and h(Y) be monotone Boolean functions on disjoint
coordinate sets, and suppose h(1)=1. Then, for every anchor (u,w),

    T(g AND h,(u,w)) |_(Y=1) = T(g,u)                       (1)

as bichain operations. Dually, when h(0)=0,

    T(g OR h,(u,w)) |_(Y=0) = T(g,u).                      (2)

The assertions allow constant g. Irrelevant variables never occur in T:
they cannot belong to a minimal activation or deactivation set, and remain
irrelevant in recursive cofactors. This also handles constant neutral h.

Prove (1) by induction on the total number of variables. If g is constant,
the assertion follows directly from the endpoint laws. Otherwise consider
the two cases in the construction.

If g(u) AND h(w)=0, the minimal activation sets split as U_X union U_Y.
Each false factor contributes one of its minimal activation sets, and each
true factor contributes the empty set. This describes precisely all minimal
activation sets, since the coordinates of the factors are disjoint. At
least one of U_X,U_Y is nonempty. In the corresponding recursive cofactor,
the h-factor has value 1 at its remaining anchor. Applying induction and
then setting all Y variables to 1 reduces the summand to

    (MEET_(i in U_X) x_i) meet T(g|_(U_X=1),u).

An empty U_X means the monomial 1 and the unchanged cofactor. If g(u)=0,
joining these summands gives exactly T(g,u), with repetitions indexed by
U_Y removed by idempotence. If g(u)=1, every U_X is empty and every summand
is T(g,u), again giving (1).

If g(u) AND h(w)=1, both factors are true at the anchor. A minimal
deactivation set kills exactly one factor: it is a minimal deactivation
set in X or one in Y. Each Y-clause becomes 1 after setting Y=1, since its
nonempty disjunction of Y variables masks its recursive child. The X-clauses
reduce by induction to the defining clauses of T(g,u). Their meet is
T(g,u). This proves (1); Boolean duality gives (2).

## A four-variable calculation, proved by the defining recursion

Let g=AB OR CD. Describe an anchor on each pair by Z=(0,0), M=(1,0), or
F=(1,1), swapping the two variables to represent a mixed pair. Swapping
the two pairs leaves only the following cases. The construction gives:

| Pair states | Anchored term |
|---|---|
| Z,Z | AB OR CD |
| M,Z | B(A OR CD) OR CD |
| M,M | B(A OR CD) OR D(C OR AB) |
| F,Z or F,M | (A OR CD)(B OR CD) |
| F,F | (A OR C)(A OR D)(B OR C)(B OR D) |

For example, in the M,M case the two minimal activations are {B} and {D}.
After fixing B=1, the remaining function is A OR CD, true at the remaining
anchor. Its sole minimal deactivation is {A}, so its term is A OR CD.
The other activation gives C OR AB. This gives the indicated row. If one
pair is F and the other is not F, deactivating either member of the F pair
is sufficient, giving the two displayed clauses. With two F pairs one must
deactivate one member of each pair, giving the four clauses. The Z,Z and
M,Z rows follow from their two activation sets in the same way. These are
applications of the definition, not an enumeration of term functions.

Every row except Z,Z gives P at

    (A,B,C,D)=(0,P,N,N).

For M,Z or M,M the first summand gives P; in F,Z or F,M the two factors
give N and P; in F,F the four factors give N,N,P,P. In all cases the result
is P. The Boolean cofactor on this cube is CD, independent of marked B,
so D_g returns N. The Z,Z term is D_g: it is a disjoint OR of two disjoint
ANDs. Therefore

    T(g,u)=D_g  if and only if  u=(0,0,0,0).               (3)

The witness row is understood after the pair/variable permutations used
to put the anchor into the displayed case.

## A realizable eight-variable function missed by every anchor

Put

    F=(AB OR CD) AND (EF OR GH).

Its displayed read-once formula realizes D_F. Indeed D commutes with AND
or OR on disjoint coordinate sets. For AND, a constantly-zero factor masks
everything, a constantly-one factor is an identity, and with two nonconstant
factors every essential variable of either remains essential: independently
make the other factor true. On N,P both operations simply propagate P.
This proves the assertion for AND; the OR case is dual.

Suppose T(F,v) were globally equal to D_F. Set E,F,G,H to 1 in this
equality. The neutralization lemma gives T(AB OR CD,v_ABCD)=D_(AB OR CD).
By (3), the first block of the anchor must be all zero. Neutralizing the
other block proves that the second block must also be all zero. Thus the
only possible anchor is the all-zero vertex.

At that anchor the construction is the prime DNF

    ABEF OR ABGH OR CDEF OR CDGH.

It is not D_F. At

    (A,B,C,D,E,F,G,H)=(1,1,P,N,N,N,N,N)

its four summands give N,N,P,P, so its output is P. The Boolean function
on this cube is EF OR GH, since AB is already true. The marked coordinate
C is inessential, and D_F returns N. This is a contradiction.

Consequently no choice of anchor makes T(F,v) globally exact, even though
D_F has the seven-gate pure realizer displayed above. A complete intrinsic
criterion cannot simply ask whether one of the canonical anchored terms
matches the guard data. Their lower-envelope representation remains valid;
its individual members need not include a global realizer when one exists.
