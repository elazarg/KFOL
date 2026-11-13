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
For arbitrary C the remaining task is to compute this preorder directly
from C. For every greatest profile completion it is now computed below.

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

## Closed criterion for every greatest profile completion

Suppose C is the greatest completion of its singleton profiles: it returns
the forced singleton when one exists, and the whole passive union U
otherwise. Put f_r(A)=Phi_r(C)(A), T_r={E:f_r(E_r)=1}, and

    theta_r(E) = AND_(s!=r) f_r(W\E_s).

The exact conditions for a source predicate P in I(C) are:

1. P is antitone.
2. P has one value lambda_r on each T_r.
3. lambda_r=1 implies theta_r<=P, for every owner r.

This is a closed intrinsic relative criterion at every arity and every
finite K>=3. There is no quantification over term realizers on its right
side. Each theta_r is one normalized owner box, equal to one on T_r and
zero on every foreign T_s. The explicit preorder is componentwise inclusion
on unowned colorings, with one additional point r per owner and E<=r
exactly when theta_r(E)=1. The T_r coordinates collapse to that point.

### The derangement law

The lower bound lambda_r*theta_r<=P holds for ANY core baseline C.
Fix a proper E, a missing owner k, and a derangement sigma of I\{r}.
For each foreign s form u_s with X=sigma(s), E_s colored s, and all
remaining passive inputs colored r. Let w be the canonical k-probe of E.
Any core term satisfying

    t(u_s) subseteq {r,sigma(s)} for all s!=r,
    t(w) subseteq N_k

must have t(u_s)=r for all s. Suppose some sigma(s0) occurs. Query w
cannot be singleton j!=r,k because its j-coalition is the same at u_j,
whose bound excludes j. The k singleton is forbidden. The r singleton,
when k!=r, would also hold at u_s0 by monotonicity, since E_r is contained
in W\E_s0. Thus the query is ambiguous and its bound passes both children.

At an r root, the pair test under the u_s0 bound gives
Phi_r(W\E_s)=>Phi_r(W\E_s0); any absorber at another positive row
would therefore absorb at u_s0 and lose sigma(s0). At a foreign-j root,
only u_(sigma^-1(j)) could absorb, via profile Phi_j({X}). If j=k this
contradicts the query budget directly. Otherwise the query's pair test
forces Phi_j(E_j), contradicting the bound at u_j. All rows consequently
act as union. Descend to a child supplying sigma(s0), preserving all
budgets. No passive leaf supplies sigma(s0); X violates the query budget.

If theta_r(E)=1, every u_s has C=r. Thus lambda_r=1 would supply
sigma(s) at every u_s, contradicting the law when P(E)=0.

### Explicit sufficiency and occurrence bounds

The unowned region is a downset, with indicator AND_r NOT f_r(E_r),
itself one normalized owner box. Let P0 be P restricted to that region.
Its greatest U-retaining source completion, followed by attaching C once
at every owner, gives an interval realizer of P0. Singleton C is restored;
ambiguous C=U absorbs all passive side effects.

For theta_r, synthesize helpers H_s for s!=r with r-profile f_r,
s-profile dual(f_r)(A)=NOT f_r(W\A), and unanimity elsewhere. These
are admissible because a dual-positive coalition meets every f_r-winning
coalition. A one-X spine attaching H_s at owner s realizes theta_r.
Union with C and restore every foreign singleton of C by attaching C
at the other owners. On C=r all helpers are r, so X survives. On
ambiguous C=U all helper contributions are already in C. The restoring
stages preserve theta_r, since it vanishes on every foreign T_s.

Union the P0 realizer with theta_r for each lambda_r=1. This gives P.
In fact, with union named, the minimum X-occurrence count is between
b(P) and b(P)+K: intersect a minimum owner-box cover with the one box
for the unowned region, realize these <=b(P) zero-tag boxes with one X
each, and add at most K one-X theta spines.

### Binary example

For C=x choice_a y, the conditions become constancy on all colorings
with x=a or y=a, plus the rule that value one there forces value one
at every x=b,y=c with distinct b,c!=a. The predicate zero exactly when
both passives are foreign-a atoms respects antitonicity and every passive
cofactor independence of C, but violates this rule. The earlier binary
analysis is subsumed by the all-arity theorem.

## Remaining target and a failed composition rule

The full joint-guard characterization is still open. This interval theorem
requires a core baseline and freezes every passive source bundle. For a
baseline which is not its greatest profile completion, the universal
theta bounds still hold but the synthesis proof does not apply.

An unrestricted union-base rule is false. Take C=x choice_a y and
D=x choice_b y, a!=b. Every predicate realizable above either base has
equal values at e=(x=a,y=b), f=(x=b,y=a), by singleton-fiber rigidity.
Their union is U=x+y, above which U+(X choice_a x) distinguishes e,f.
Thus L(C+D) need not be the distributive sublattice generated by L(C)
and L(D). Whether disjoint supports admit such a rule remains unproved.
