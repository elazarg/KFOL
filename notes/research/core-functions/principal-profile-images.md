# Profile images below a genuine core upper bound

Written mathematical proofs in
[appendix-core-principal-profiles.tex](../../../sections/appendix-core-principal-profiles.tex),
`core:prop:principal-profile-preorders` and
`core:thm:principal-profile-locality`. These new statements are not Lean
theorems. Their Gray deletion patches and profile completions already have
independent proofs; the new profile-image and sharp row-threshold arguments
are written.

The original target remains a short intrinsic criterion on joint guards.
These results show how much joint data even a single owner's principal
profile image can carry.

## Arbitrary finite preorders

For a known core C, the family

    L_c(C)={Phi_c(H): H core, H<=C}

is a finite distributive lattice. Bounded helpers are closed under every
owned choice; c-choice gives profile OR and any foreign choice gives AND.

Every finite preorder P on X occurs EXACTLY as the implication preorder on
singleton coalitions inside such a family, with K fixed >=3. Add a padding
variable p. For every upset S of P, take the greatest completion E_S with
c-profile OR_(x in S+p) x, b-profile AND_(x in S+p) x, and unanimity at
the other owners. Put C=UNION_S E_S.

For uPv with u!=v, the row u=a,v=c,all other inputs=b has C-value bc:
E_S returns c when v belongs to S, and b otherwise, since u then also
does not belong to S. PairSafe_c({u},{v}) fails under bc, forcing the
implication for every H<=C. Conversely E_S realizes every upset on those
singleton bits. Their evaluation map is a surjective lattice homomorphism.
Padding handles the empty upset and even X empty.

Thus arbitrary finite upset lattices occur as quotients of these profile
images. This is a representation theorem, not an intrinsic computation of
L_c(C) from arbitrary mixed source guards.

## Sharp exponential simultaneous-row threshold

Use the paired Gray transversals from [exponential-crowns.md](exponential-crowns.md).
There are m=2^d intervals L_i<U_i on 2d variables, indexed cyclically.
Let C=F_0, the genuine core deletion patch whose retained exceptions are
C_i for i=1,...,m-1. Its own-c profile image is exactly

    normalized monotone phi with phi(U_i)=phi(L_i), 1<=i<m.

Necessity: at the atomic matching row (c on L_i, a at the unique free
coordinate, b outside U_i), the bound bc excludes a positive U_i bit
and a negative L_i bit by the one-bound pair test.
Sufficiency: E_phi with c-profile phi, dual b-profile, and unanimity elsewhere
is bounded by C. On a retained exception it returns c or b according to the
common endpoint bit. Everywhere else provenance bounds it by input union.
This is valid on all winner menus and for every additional owner.

Take A=U_(m-1), B=L_1. Boolean inclusion and the retained reverse covers give
a path A=>B using EVERY m-1 reversed edge. Incidence

    L_j subseteq U_i iff j=i or j=i+1

shows that there is no alternative path avoiding a reversal: any relevant
path stays at ranks d,d+1 and can move backward only through those reversals.
Consequently all core H<=C obey Phi_c(H)(A)=>Phi_c(H)(B).

For each retained edge i, remove its reversal too. The reachability upset
of A gives a normalized phi_i separating A from B and constant on all
other retained intervals. Its completion H_i is bounded by C everywhere
outside C_i. Every valuation excludes at most one H_i, since the regions
are disjoint. Therefore ANY m-2 arbitrary valuations admit a common
separator respecting their C-bounds. The m-1 atomic matching rows exclude
all separators. The threshold is EXACTLY 2^d-1.

All these C have unanimity singleton profiles and identity pure-owner
closures. Their growing implications live in the mixed source guards.

This refutes a uniform K-row (or any polynomial-in-arity row) bound even
when the upper bound is already known to be core. The arbitrary-bound
staircase did not establish this principal-bound result. Neither result
solves the full intrinsic guard problem.
