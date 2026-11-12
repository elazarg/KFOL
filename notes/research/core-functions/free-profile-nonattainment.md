# A maximal profile fibre has no least free extension

Mathematical research, without Lean claims. This strengthens the nonattainment
phenomenon from nonmaximal profile data to a maximal admissible profile tuple.
Two words with the same maximal profiles already have no common lower bound
among their free extensions. The obstruction uses two source coefficients at
one independent-status assignment.

The free coefficients and their recurrence are those of
[free profile persistence](free-profile-persistence.md). Words have no
constants or role switches, the finite owner set has at least three elements,
and different owners' passive flags may overlap.

## Persistence of a common source set

Fix positive profile demands `Phi_r(A_r)=1`, one for each old owner. Put

    C = intersection_r A_r.

Suppose the independent flag sets avoid C, so that each source coefficient
`C_(j,k)(E)` with j in C is defined on the same assignment E. Assume further

    E_h intersect intersection_(r!=h) A_r = empty
        for every old owner h!=k.                        (1)

Then every word satisfying the positive demands satisfies

    OR_(j in C) C_(j,k)(E) = 1.                          (2)

For an old observer k its own flag set is immaterial to the free recurrence;
it may be set to the empty set. For every other owner, avoidance of C follows
already from (1).

**Proof.** Track the aggregate coefficient on the left of (2). At a leaf it
is true exactly when the label belongs to C. The aggregate obeys the same
recurrence as one source coefficient, since the sibling profile filters do
not depend on the source label.

At a root owned by h, choose a child L with the positive h-profile bit.
Every other owner's positive profile bit passes to both children, so L has
all the positive demands. Induction gives aggregate coefficient one in L.
If h=k, the root takes the disjunction and retains it. Otherwise the sibling
cannot have `Phi_h(E_h)=1`: together with its positive bits at A_r for r!=h,
rainbow common-source persistence would put a label in the intersection
forbidden by (1). Its filter is therefore open, and the aggregate coefficient
of L reaches the root. At a leaf all the positive demands force its label
into C. This proves (2). QED.

Unlike the singleton-source theorem, this conclusion is a disjunction.
There need not be one member of C whose coefficient is forced individually.

## The ternary maximal tuple

Let the variables be X,Y,Z and choose two distinct owners a,b. Prescribe

    Phi_a = majority(X,Y,Z),
    Phi_b = majority(X,Y,Z),
    Phi_h = X AND Y AND Z       for every h outside {a,b}.

This tuple is admissible and maximal under pointwise enlargement of the
winning-coalition families. Admissibility follows because two subsets of a
three-element set of size at least two intersect, while the other owners
require the full set.

For maximality, enlarging either majority family adds a coalition of size
at most one, which is disjoint from an existing winning coalition for the
other majority owner. Enlarging an outside owner's unanimity family adds a
proper coalition A. Choose i outside A and majority coalitions for a and b
whose intersection is exactly {i}; the resulting rainbow has empty common
intersection. Both changes violate rainbow common-source persistence.

There are explicit realizers

    T_Z = (X choice_a Y) choice_b (Z choice_a (X choice_b Y)),
    T_X = (Z choice_a Y) choice_b (X choice_a (Z choice_b Y)).

Indeed the a-profile of T_Z is

    (X OR Y) AND (Z OR (X AND Y)) = majority(X,Y,Z),

and its b-profile is

    (X AND Y) OR (Z AND (X OR Y)) = majority(X,Y,Z).

Every other owner takes AND at every gate and therefore has unanimity on
the three-variable support. Swapping X,Z proves the same facts for T_X.

These are not different full winner operations. The
[tight-quota uniqueness theorem](near-unanimity-size.md), with
`d_a=d_b=1` and every other quota zero, identifies the unique core operation
with this profile tuple as

    U(w)={a} if at least two inputs are exactly {a};
         {b} if at least two inputs are exactly {b};
         w_X UNION w_Y UNION w_Z otherwise.

The two quorum cases cannot occur together. The same formula holds over
every ambient role extension when the words keep their old-owner gates.
In particular T_Z and T_X are two words for one fixed, uniquely determined
full operation U.

## Two incompatible free minima

Take an observer k outside {a,b}; it may be an old third owner or a fresh
unowned observer. Use the independent flags

    E_a = E_b = {Y},
    E_h = empty                 for every other old owner h.

This assignment is legitimate for both source X and source Z. Its overlap
at Y is essential.

Apply the common-source-set theorem with

    A_a = A_b = {X,Z},
    A_h = {X,Y,Z}               for every other owner h.

The common intersection is {X,Z}. Every required avoidance condition holds:
the a- and b-flags lie at Y, and the remaining flag sets are empty. Hence
every word S with the prescribed profiles satisfies the two-corner law

    C_(X,k)^S(E) OR C_(Z,k)^S(E) = 1.                    (3)

Nevertheless T_Z has `C_(X,k)(E)=0`. In its two inner words
`X choice_a Y` and `X choice_b Y`, the Y sibling blocks the source-X
contribution using its respective flag. No later gate can recreate that
source contribution. Its source-Z coefficient is one: in
`Z choice_a (X choice_b Y)` the sibling has a-profile zero at {Y}, and at
the outer b-gate the sibling `X choice_a Y` has b-profile zero at {Y}.
Thus

    (C_(X,k)^T_Z(E), C_(Z,k)^T_Z(E)) = (0,1).

By the X,Z symmetry,

    (C_(X,k)^T_X(E), C_(Z,k)^T_X(E)) = (1,0).

Each queried bit therefore has individual minimum zero in this maximal
profile fibre. Equation (3) prevents simultaneous attainment of those two
minima. More strongly, there is no word with these profiles whose free
extension is pointwise below both T_Z and T_X: such a word would have both
displayed coefficients zero, contradicting (3).

Consequently this maximal profile fibre has no least free extension. The
obstruction concerns simultaneous attainment, rather than failure of the
closed formula for either individual minimum.

## A greatest extension still exists

The [quota normal form](quota-normal-form.md) constructs a greatest
term-induced free extension of this same U. Its coefficients are

    C^max_(j,k)(E)=AND_(r!=k) [|E_r|<t_r],

where `t_a=t_b=2` and every other threshold is three. At the independent
assignment above it has coefficient pair (1,1). Thus the fibre has a
greatest free extension, while the coordinatewise infimum of all its free
extensions has the pair (0,0) and is not term-induced. This failure already
occurs for a globally minimal full winner operation with maximal admissible
profiles and a unique ordinary extension.
