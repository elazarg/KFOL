# Closure operators classify two-owner CNF operations

Mathematical research, without Lean claims. Every finite loopless closure
operator gives a source-separable core operation with a canonical CNF.
Conversely these closure operators classify the full-support two-owner
CNF operations exactly. Matroid exchange is not needed for existence;
it supplies stronger minimality conclusions in
[matroid-core-operations.md](matroid-core-operations.md).

Fix finite owners I with K>=3, two distinct owners 0,1, and a finite
nonempty variable set V. A loopless closure c on V is extensive,
monotone, idempotent, and satisfies c(empty)=empty. Spanning means
c(S)=V. All menus are nonempty winner sets.

## A core word from any loopless closure

For every proper closed set H form the clause that folds choice_1 over
V\H. Fold choice_0 over all these clauses:

    F_c=FOLD_choice_0_(H closed, H!=V)
                       (FOLD_choice_1_(i in V\H) x_i).    (1)

Every clause is nonempty. The family is nonempty because empty is a
proper closed set. In particular its clause V includes every variable.
Thus (1) is a full-support primitive core word.

The elementary closed-set identities are

    c(S)=V iff no proper closed H contains S;
    j notin c(S) iff some closed H contains S and misses j. (2)

The reverse implication in the second line uses c(S) subseteq H; the
forward implication takes H=c(S).

For source j define factors on sets not containing j by

    D_(j,0)(E_0)=[c(V\E_0)=V];
    D_(j,1)(E_1)=[j notin c(E_1)];
    D_(j,r)=true for r notin {0,1}.                       (3)

**Theorem.** The canonical source coefficients of F_c are exactly

    c_(j,k)=AND_(r!=k) D_(j,r)(E_r).                      (4)

For k!=1, a marked occurrence in the clause V\H survives the inner
choice_1 gates exactly when H contains E_1. There is such a clause
containing j precisely when j is outside c(E_1), by (2). At k=1 the
inner gates add no filter.

For k!=0, an outer gate absorbs to 0 if some clause is entirely 0,
equivalently some proper closed H contains V\E_0. The marked clause
contains j={k} and cannot itself be all 0. Thus the common outer filter
is c(V\E_0)=V, independent of the marked occurrence. At k=0 these
outer gates add no filter. This proves (4).

The factors in (3) are canonical: pure-0 and pure-1 probes recover them.
All other owner factors are true. Their being coefficient factors does
not assert that their whole vector occurs at one marked leaf.

## Profiles and full winner values

The profiles of (1) are

    Phi_1(E)=[c(E)=V];
    Phi_0(E)=[c(V\E)!=V];
    Phi_r(E)=[E=V] for r notin {0,1}.                    (5)

The first two statements follow from (2) and the OR/AND recursions.
At another owner all gates take AND, and the full clause V ensures that
every variable is required. These profiles are normalized and admissible.

At an arbitrary valuation let

    L={i:w_i={1}},      U=V\{i:w_i={0}},
    W_k={i:k in w_i}.

Source reconstruction gives the same explicit formula as for matroids:

    0 in F_c(w) iff some j in W_0 is outside c(L);
    1 in F_c(w) iff c(U)=V and W_1!=empty;
    k in F_c(w) iff c(U)=V and some j in W_k is
                    outside c(L), for k notin {0,1}.      (6)

Equivalently,

    F_c(w)={0}                         if c(U)!=V;
           {1}                         if c(L)=V;
           ({1} if W_1!=empty else empty)
             union UNION_(j notin c(L)) w_j otherwise.   (7)

The first two cases cannot conflict because L subseteq U. In the first
case choose j outside c(U); it lies outside U, is the 0 singleton, and
is outside c(L). In the second case L is nonempty by looplessness. In
the last case c(L) is proper, so the indicated input union is nonempty.
This verifies the full formula directly; nonemptiness also follows from
the actual word (1).

## Exact recognition of the two-owner CNF class

Consider any nonempty family C of nonempty clauses covering V and its
word

    F_C=FOLD_choice_0_(C in C)
                       (FOLD_choice_1_(i in C) x_i).

Define

    c_C(S)=intersection {V\C : C in C and S subseteq V\C},

with empty intersection equal to V. This is a closure operator. Its
empty-set value is V\UNION C=empty, so it is loopless. The same source
calculation proves F_C=F_(c_C): an outer 0-filter says that no clause
lies in E_0, and an inner surviving j-clause says that one of its
complementary closed generators contains E_1 and misses j.

**Classification theorem.** Loopless closure operators on V are in
bijection with full-support two-owner CNF operations of this shape.

Existence and surjectivity were just proved. For injectivity, for every
S and j outside S a pure-1 source probe tells whether j belongs to
c(S), by (3). Extensivity already determines membership for j in S.
Thus the full operation recovers c uniquely.

There is also a direct recognition test from source data. If a candidate
has source reconstruction and its coefficients have (4), recover c from
its pure-1 factors by

    c(S)=S union {j notin S:D_(j,1)(S)=false}.

Check the closure laws and c(empty)=empty, and check that its pure-0
factors are [c(V\E_0)=V] and all other factors are true. These closed
conditions are necessary and sufficient for membership in this CNF
class. They do not introduce a realizing-word witness.

## The canonical irredundant CNF

A proper closed set H is meet-irreducible when it is not the intersection
of two strictly larger closed sets. Every closed set is an intersection
of such sets containing it: if it is reducible, split it into larger
closed sets and continue; finiteness terminates this process.

Consequently (1) can be restricted to the complements of the
meet-irreducible proper closed sets, without changing c or F_c. This
clause family is forced in every CNF representation of F_c. Indeed the
complement of each representing clause is closed for the generated
closure. A meet-irreducible H must be the intersection of generators
containing it; if none equals H, this expresses H as an intersection
of strictly larger closed sets, contradicting meet-irreducibility.

Thus these clauses form the unique irredundant CNF and minimize both
the clause count and the leaf count within this two-level CNF shape.
They need not give the shortest arbitrary primitive word. For matroids,
the meet-irreducible proper flats are the hyperplanes, recovering the
cocircuit CNF.

The [minimal-CNF classification](minimal-cnf-matroids.md) gives the exact
boundary: F_c is globally minimal among core operations if and only if
c is a matroid closure. Its proof identifies the prime clause clutter
by cocircuit elimination and characterizes every harmless redundant clause.

Using only the maximal proper closed sets instead replaces c by

    c_coatom(S)=intersection {H maximal proper closed:S subseteq H}.

It has the same spanning sets but can be larger than c; it can even
have loops. Prime Boolean clauses alone therefore need not determine
the original full operation. Matroid closures are coatomistic, so this
replacement leaves them unchanged.

## An asymmetric closure between two familiar completions

Let V={X,Y,Z}. Close a set to V when it contains X and at least one
of Y,Z, and also impose Y implies Z. Its closed sets are

    empty, {X}, {Z}, {Y,Z}, V.

Its meet-irreducible proper closed sets are {X},{Z},{Y,Z}. Hence the
canonical five-leaf CNF is

    (X choice_0 (X choice_1 Y)) choice_0 (Y choice_1 Z).   (8)

The spanning predicate is X AND (Y OR Z). The coatom closure additionally
imposes Z implies Y; it is the matroid closure with parallel class
{Y,Z} and singleton class {X}. Its operation is the primitive read-once
word X choice_0 (Y choice_1 Z).

At the other extreme, close only spanning sets to V and leave every
nonspanning set unchanged. This is again a loopless closure with the same
spanning predicate. Formula (7) is then the greatest profile completion:
after either singleton profile succeeds it returns that singleton, and
otherwise it returns the entire input union.

In general, for two loopless closures c<=c' with the same spanning
sets, (3) gives F_(c')<=F_c. The map is injective, so strictness of
closures gives strictness of the corresponding operations. In the
example the read-once operation is strictly below (8), which is strictly
below its profile maximum. All three have the same complete profiles.
Thus arbitrary closure existence does not imply the matroid family's
global minimality theorem.

## Free completion and the boundary of the result

The source calculation is valid even when E_0 and E_1 are independent
and overlap. At each marked occurrence the outer 0-filter is common to
all its clauses, so taking the OR of the inner clause contributions still
gives (4). Pure-owner probes bound every other realizer's full factors
by (3). Consequently this CNF attains the greatest term-induced free
extension, and the same pure-owner argument makes it the greatest
arbitrary antitone completion. This is not a least-extension or
unique-extension assertion.

For matroids, basis exchange additionally gives equality with the closed
profile lower envelope, global minimality, and rigidity over unowned
role extensions. Those stronger conclusions are proved in
[matroid-core-operations.md](matroid-core-operations.md). Existence for
arbitrary closures does not imply those stronger conclusions; the precise
global-minimality boundary is the matroid condition just cited.

The [colored-closure reduction](separable-closures.md) places this
two-owner construction inside the broader source-separable problem.
It remains a constructive class, not a classification of all mixed
closure systems or all jointly realizable source guards.
