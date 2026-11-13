# Source activation above a fixed core operation

Written mathematical results, not new Lean claims. The report contains the
proofs in [appendix-core-intervals.tex](../../../sections/appendix-core-intervals.tex).
The full target remains joint realizability of arbitrary source families.

## Exact order structure

Fix a core operation C(v) on nonempty W. Let I(C) contain the core F(X,v)
with C <= F <= C union X. All passive source bundles are exactly C's:
at a passive-source k-probe, X omits k and the interval bounds fix the bit.
Consequently the complete source predicate P_X determines F by

    F(X,v) = C(v) union {k in X : P(E(v) with its k-block erased)}.

The erasure of the k-block matters. There need not be a common scalar
P(E(v)) on an arbitrary valuation, since E(v) may use every owner.

Join of interval predicates is OR, realized by union. Meet is AND,
realized by substitution F(G(X,v),v). The bounds remain valid, and the
source formula proves the pointwise identity. Bottom is C and top C+X.
Thus this is a finite bounded distributive sublattice of the Boolean
source-coordinate cube. It is exactly the downset lattice of the preorder

    p <=_C q iff every interval realizer positive at q is positive at p.

Every excluded predicate violates one of these unary implications.
Equivalently, interval interpolation on every pair of source probes gives
one global interval realizer. The global interval bound is part of the
hypothesis; this does not yield two-point interpolation for the full clone.
The missing structural task here is to compute this preorder directly from
C, without quantifying over interval realizers.

## Singleton fibers collapse

For each owner r, all proper colorings with Phi_r(C)(E_r)=1 have the same
activation bit lambda_r. Fix q!=r and erase X=q from h=F(q,v), obtaining
nonempty core g<=C. On every C=r valuation, g=r. If h has any r-singleton
value, preservation of that nonzero singleton predicate makes h=r on the
entire C=r fiber. Otherwise h=r+q throughout it. Singleton profiles depend
only on their own atomic flags, so the alternative is independent of q.

The passive cofactor-dependence theorem also supplies explicit equivalence
edges: when C is independent of passive i after a proper atomic fixing,
F is independent of i there as well. Antitonicity and these equivalences
do not generate the whole preorder.

## A complete binary-base criterion

Let C=x choice_a y and let P be antitone on proper colorings of {x,y}.
There is an interval realizer iff:

1. All colorings with x=a or y=a have one value lambda.
2. If lambda=1, P(x=b,y=c)=1 for distinct b,c different from a.

For lambda=0, take the greatest single-source completion Q_P retaining
x+y, then Q_P choice_a C. This equals C when C=a and Q_P otherwise.
For lambda=1, antitonicity and condition 2 make every unowned coloring
positive. Start with C+X and attach C once at each foreign owner r whose
diagonal P(x=r,y=r) is zero. This suppresses X exactly on those singleton
fibers. These constructions cover all nonempty input menus.

Necessity of condition 2 has an analytic three-row proof. At

    u=(X=b,x=a,y=c), v=(X=c,x=b,y=a), w=(X=a,x=b,y=c),

the budgets ab,ac,bc force every core term's tuple to be (a,a,bc).
Use the existing one-bound profile-pair test to obtain the bridges
Phi_a(y)=>Phi_a(x) under the first budget and Phi_c(X)=>Phi_c(y) under
the third. If b occurs at u, these bridges and equal atomic coalitions
force the other two rows to be ambiguous. Their budgets then pass to a
strictly smaller child still supplying b at u. No leaf qualifies.
Swapping x,y and b,c proves the symmetric conclusion.

The predicate zero exactly when both passives are foreign-a atoms obeys
antitonicity, uniform singleton-fiber activation, and every passive
cofactor independence of C. It fails condition 2. This rules out the
otherwise natural antitone-plus-cofactor preorder proposal.

## Generalization to test next

Every binary identification minor of a larger base inherits the criterion.
In particular, for a read-once C=L choice_a R on disjoint blocks, lambda_a
forces activation on the coloring with all L-leaves=b and all R-leaves=c,
for distinct foreign b,c; antitonicity gives its subcolorings. Whether
these minor-induced edges and passive cofactor edges generate the full
preorder even for read-once C is unproved. The arbitrary-base preorder
and the original joint-guard characterization both remain unresolved.
