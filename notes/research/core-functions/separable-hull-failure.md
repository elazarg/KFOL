# A four-variable separable-hull obstruction for every K>=3

Mathematical research, without Lean claims. Canonical pure-owner sections
give closure operators even when the original source coefficients do not
separate by owner. Taking the product of those sections gives a canonical
upper bound preserving the original singleton profiles and pure sections.
It need not be term-induced. Four variables suffice for every K>=3,
including three owners. The example below even has a greatest core
minorant, explicit hereditary compatibility, and core proper input minors.

Fix a finite owner set I with at least three owners. Let F be a genuine
core operation on a finite full variable support V. At source j and an
owner r, let D_(j,r)(E) be its pure-r source coefficient, for E subseteq
V\{j}. One may use any observer k!=r: put j={k}, inputs in E equal
to {r}, and all other inputs equal to N_k=I\{k}. This coefficient is
independent of the choice of k!=r.

The [colored closure representation](separable-closures.md) gives

    D_(j,r)(E) iff j notin c_r(E)

for canonical loopless closure operators c_r. Define the separable hull
H, as a winner set, by

    k in H(w) iff some j has k in w_j and
        D_(j,r)(E_r(w)) for every r!=k,
    E_r(w)={i:w_i={r}}.                                  (1)

Whenever k belongs to w_j and r!=k, j is not in E_r(w), so every factor
in (1) is in its specified domain.

## Properties the hull always retains

**Lemma.** F(w) subseteq H(w). In particular H is nonempty-valued.
It has exactly F's singleton-output predicates, and its pure sections
are the same D_(j,r).

Every occurrence factor of source j at owner r is below the OR of all
such factors, namely D_(j,r). Its full contribution is therefore below
the product in (1). Taking the OR over supplying occurrences proves
F subseteq H.

If F(w)={r}, every potential source j for a different winner k has
j notin E_r(w). The pure-r source probe with that same E_r(w) still
has F-output {r}, since singleton profiles depend only on their owner's
atomic positions. Hence D_(j,r)(E_r(w)) is false and H cannot contain
k. Its nonemptiness makes H={r}. Conversely if H is a singleton, its
nonempty subset F is the same singleton. This proves exact agreement of
all singleton predicates, including their admissibility.

At a pure-r source probe, all other rival factors have empty atomic sets
and equal true. Thus H's pure section is precisely D_(j,r), as claimed.

The hull is inclusion-monotone: enlarging an input can add winner bits
and remove singleton statuses, so the antitone factors cannot change from
true to false. It is idempotent, because at an equal ambiguous input all
atomic sets are empty, and at equal atomic inputs only their common
winner is available.

It also has whole-input provenance. At an ambiguous source j, put
T_j={r:j in c_r(E_r)}. If T_j is empty, the whole menu w_j contributes.
If T_j is a singleton {r}, it can supply only r; but then E_r is nonempty,
since c_r(empty)=empty. The same winner is therefore covered by some
input equal to {r}. If T_j has at least two owners it supplies nothing.
Atomic sources are already whole singleton menus. Every output winner
can thus be covered by a whole input menu contained in H(w).

None of these properties proves joint source realizability.

## Core lower bounds are determined by pure-port bounds

There is a general order fact behind the example. Let G be a normalized
source-separable reconstruction with pure ports D_(j,r), initially
allowing empty outputs. For any core operation S,

    S<=G iff D^S_(j,r)<=D_(j,r) for every j,r.           (B)

Necessity evaluates the inequality at pure-owner probes. Conversely
every occurrence factor of S is below its own pure-owner port, hence
below D_(j,r). Its full contribution is therefore below the product
defining G. Taking the union of occurrence contributions proves S<=G.
Thus bounding a core operation by a separable candidate is exactly
bounding all its pure ports.

If the target ports are jointly realized by some core S_0, then a
greatest core lower bound R of G exists. There are finitely many
operations on the fixed finite carrier and variable set, and the core
lower bounds are closed under nonempty pointwise union. Their finite
union is core and greatest. It lies above S_0 and below G, so its pure
ports equal the target ports exactly. Equivalently R is the greatest
core operation in that exact pure-closure fiber. None of this proves
that R is itself source-separable or supplies a closed construction
for arbitrary port data.

For additive owner closures the situation is positive: the
[colored-preorder theorem](additive-closure-characterization.md) realizes
their separable hull whenever the pure data come from any core operation.
The counterexample below needs genuinely joint closure premises.

## The uniform four-variable counterexample

Choose distinct owners 0,1,2 and variables A,B,C,W. The following is an
actual constant-free core word, with union implemented by the standard
three-owner abbreviation:

    R=A union W
       union (B choice_1 W) union (C choice_0 A)
       union ((B choice_1 C) choice_0 A)
       union ((C choice_0 B) choice_1 W).                (2)

Its complete source coefficients are computed in
[the reciprocal-rule theorem](separable-closure-counterexample.md).
Write A_0 for [A={0}], and similarly for the other atomic flags.
At an observer k outside {0,1}, its only nontrivial source coefficients
are

    C_(B,k)=NOT W_1 OR (NOT C_1 AND NOT A_0);
    C_(C,k)=NOT A_0 OR (NOT B_0 AND NOT W_1).             (3)

Sources A,W are unconditional. At observer 0 the B coefficient is
NOT(C_1 AND W_1) and C is unconditional; at observer 1 B is
unconditional and C has coefficient NOT(A_0 AND B_0).

Consequently its canonical owner closures are exactly

    c_0(E)=E union ({C} if {A,B} subseteq E else empty);
    c_1(E)=E union ({B} if {C,W} subseteq E else empty);
    c_r(E)=E for r outside {0,1}.                        (4)

For example the pure-1 B port sets A_0=false in (3), giving
NOT(C_1 AND W_1). The pure-0 B port sets W_1=false and is true.
The C calculations are symmetric. Thus taking the separable product
of (4) gives the exact hull

    G=A union W
       union (B if NOT(C=W={1}) else empty)
       union (C if NOT(A=B={0}) else empty).             (5)

The genuine core word R has value

    R=A union W if A={0} and W={1};
      G otherwise.                                    (6)

This follows by distributing the two Boolean expressions (3). Own-owner
bits are unchanged, and in the exceptional case their winners 0,1 are
already supplied by A,W. In fact (2) is the greatest core operation
below G, by the greatest-minorant theorem in the linked note.

## The hull violates a universal three-row law

For any observer k outside {0,1}, let N_k=I\{k}. In variable order
A,B,C,W, take

    u=(N_k,{k},{1},{1});
    v=({0},{0},{k},N_k);
    q=({0},{k},N_k,{1}).                               (7)

Every core term has the persistence property

    k in output(q) implies k in output(u) or output(v).

The linked note proves it for arbitrary terms, without a term-table
search. In the observer-k view, extra-owner gates act as union on these
rows; expansion into pure 0/1 terms and their monotone Boolean cube
endpoints give the implication.

But (5) gives G(u)=G(v)=N_k and G(q)=I. Hence G is not core for
every fixed K>=3. Equation (6) removes precisely the unsupported
head contributions at the conflicting anchor assignment.

This witness also explains what the hull forgets. In (3), B can supply
an outside winner when W is not the 1 atom, or when C is not 1 AND A
is not 0. The two branches are coupled. Each pure-owner probe sees a
surviving branch, but their product inserts the forbidden mixed case
A=0,W=1. The same phenomenon occurs symmetrically at C.

## Strong compatibility still does not repair the product hull

The hull's closure family (4) is extracted from the explicit core word
R, not proposed independently. It has all colored-idempotence laws and
admissible spanning profiles on every restriction. The hull itself has
those very closures as its functional-dependence closures, satisfies
hereditary omission and span-outcast, and has core proper neutral faces
and identification minors. It is prime under disjoint idempotent
factorization. All these statements are proved in
[separable-closure-counterexample.md](separable-closure-counterexample.md).

Thus even a jointly realized family of pure-owner closures, together
with these closed hereditary laws, does not make its separable upper
hull core. The missing data are the mixed source dependencies. The
separate question whether a genuine source-separable core operation
attains its own maximal full factor vectors is not refuted here: R
itself is nonseparable at its two head sources.
