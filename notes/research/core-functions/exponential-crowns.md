# Critical verification of the transversal/Gray crown

The exact quantitative theorem is now proved in Lean and stated as
`Report.core_exponential_locality`. It strengthens nonfinite relatedness:
2d inputs suffice for a nonterm operation that passes all 2^d-point tests,
and an explicit (2^d+1)-row sample fails. This does not settle the original
short direct guard characterization.

## Set geometry

Let d>=2, V=(Fin d)×Bool, and X=Bool^(Fin d). Choose a cyclic Hamiltonian Gray
ordering next of the 2^d bitstrings: each next(x) differs from x in exactly one
coordinate, and next is one cycle. Put

    L_x = {(j,x_j): j in Fin d},
    U_x = L_x union L_next(x).

Every L has cardinality d and every U cardinality d+1. In particular L is
nonempty and U is proper in V. For every selected L_z,

    L_z subseteq U_x iff z=x or z=next(x).              (I)

Indeed U_x has one point in every unchanged block and exactly two points in
the one changed block. A transversal contained in it is one of its endpoints.
Each U_x is distinct: equality determines the unordered endpoint pair by (I),
and a Hamilton cycle of length at least four repeats no unordered edge.

Draw all Boolean-lattice inclusion edges and reverse U_x→L_x at every zero
edge except an omitted edge h. Each retained edge gives a two-vertex SCC
{L_x,U_x}. Contracting these pairs leaves the directed cut cycle as a path:
the only other selected incidence is L_next(x)→U_x. The omitted U_h is a
sink for these downward transitions.

No unselected Boolean vertex can enlarge an SCC. A cycle with a strict
inclusion can lose cardinality only through the reversed covers, from rank
d+1 to rank d. It can therefore use only ranks d,d+1. An unselected rank-d
vertex has no incoming strict downward edge, and an unselected rank-(d+1)
vertex has no outgoing strict downward edge. Thus every nontrivial SCC is
exactly one retained cover pair. Consequently the only collapsed strict
intervals L subsetneq U are the retained (L_x,U_x).

If every edge is reversed instead, all selected L_x,U_x lie in one SCC.
The opposite interval (L_next(x),U_x) is a strict interval distinct from all
selected zero intervals, so its prescribed positive observation violates the
atomic observer criterion. Equivalently, the inequalities
phi(L_next(x))<=phi(U_x)=phi(L_x) force equality around the full cycle.

## The full winner-valued operation

Fix owners b,c (and any third owner a for the obstruction). For a winner
valuation S define its interval

    L(S)={j:S_j={c}},   U(S)={j:S_j!={b}}.

Let C_x be exactly the region L(S)=L_x, U(S)=U_x. Since U_x\L_x has one
coordinate, this is precisely c at L_x, a value neither b nor c at the free
coordinate, and b elsewhere. Regions are disjoint because their exact
c-singleton sets L_x are distinct.

Define F as the full input union except that it is {b,c} on every C_x.
Define F_h by omitting C_h from this exception list.

Let B_h consist of every normalized monotone Boolean phi on 2^V constant
on the retained zero intervals. The graph argument proves:

    some phi in B_h separates L<U
       iff (L,U) is not a retained zero interval.        (S)

Indeed no positive interval has reversed endpoints, so the reachability
upset of U gives a normalized separator. Normalization follows from strict
separation and the inclusion edges to top/from bottom.

For each phi use singleton-profile synthesis and greatest completion to get
E_phi with c-profile phi(E), b-profile not phi(V\E), all other profiles
unanimity, and full input union on ambiguous outputs. Take the finite
nonempty derived union of all E_phi. The family is nonempty because OR-all
and AND-all are normalized and constant on every retained zero interval:
every L_x is nonempty and every U_x is proper.

At any winner-valued input S:

* If L(S)<U(S) is separated, some E_phi returns the full input union. The
  other completions are contained in that union by provenance. A possible
  singleton of an unnamed owner already equals the full union, so causes no
  exception to this argument.
* At a retained zero interval all completions return b or c. OR-all returns
  c, AND-all returns b, so their union is exactly {b,c}. This applies to all
  ambiguous values and all additional owners at the free coordinate.
* If L(S)=U(S), all inputs are b/c atoms. OR-all and AND-all include exactly
  every endpoint that occurs: all b gives b, all c gives c, and a mixed tuple
  gives {b,c}.

These are precisely the values of F_h on every valuation over any ambient
K>=3. Therefore all deletion patches are actual core operations, not merely
atomic observer realizations.

## Locality, idempotence, and quantitative consequence

There are m=2^d disjoint exceptional regions. Add one more core patch H:
the union of the greatest completions for OR-all and AND-all. It equals
{b,c} on every exceptional region, since each lower endpoint is nonempty
and each upper endpoint is proper. At an exceptional input only its own
deletion patch may differ from F; elsewhere only H may differ. Thus every
valuation excludes at most one of m+1 core patches, and every m valuations
have a common patch. The m atomic matching rows and one opposite atomic row
have no common core interpolant by cyclic propagation. The threshold is
therefore exactly m+1, at arity 2d.

A constant input valuation cannot lie in any C_x because L_x is nonempty and
U_x is proper, so both b and c occur there. Thus F is idempotent; idempotent
extraction also excludes winner-constant/role-switch realizations.

For fixed K>=3 this yields noncore 2^d-local operations at arity 2d.
Every polynomial p(2d) is eventually below 2^d, so no polynomial in input
arity can bound a sufficient locality threshold. Odd arities can be padded
by an unused input and nonrealizability retained by substituting that input
back to an existing variable.

## Optional q-ary block improvement

The same proof works for V=(Fin d)×(Fin q), L_x selecting one point per
block, and a Hamilton cycle in the Hamming graph on (Fin q)^d. Adjacent
transversals still have a union containing exactly those two transversals.
It gives q^d patches at arity qd. In particular q=3 improves the exponential
rate to 3^(n/3), if the extra Hamilton-cycle proof is desired. The binary
construction already establishes the polynomial-threshold obstruction.

## Independent full-value checks

The construction was checked exhaustively at d=2 and d=3 for K=3 and K=4,
using principal reachability cuts and evaluating the greatest completions by
their independent singleton profiles. At d=3,K=4 this checks all 11,390,625
winner valuations against all eight deletion patches. These computations
are corroboration; the symbolic proof above covers all dimensions and every
ambient role set with three distinguished owners.

## Formal modules

- `Definitions/CoreIntervals`: raw interval operation and independent cut predicates.
- `Core/IntervalCompletion`: Boolean separators give actual full-winner terms.
- `Definitions/CrownFrame`, `Core/CrownFrame`: cover incidence and explicit
  principal cut formula after deleting the wrapping edge.
- `Core/IntervalCrownCompletion`: reindexing supplies every deletion patch.
- `Core/IntervalCrownLocality`: fewer samples than patches have a common interpolant.
- `Definitions/GrayCrown`, `Core/GrayCrown`: reflected list, cyclic bijection,
  one-coordinate adjacency and paired transversals at every dimension.
