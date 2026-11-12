# A maximal profile fibre has no least free extension

Mathematical research, without Lean claims. Common-source persistence couples
several free coefficients at one independent-status assignment. It rules out
a least free extension even for a maximal admissible profile tuple determining
one exact winner operation.

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

## Nonattainment in a maximal profile fibre

Take the ternary quota operation U with majority profiles at distinct
owners a,b and unanimity at every other owner. Its full winner operation
is unique: return {a} or {b} at an atomic quorum of two, and otherwise
the whole input union. These profiles are maximal admissible.

At E_a=E_b={Y}, with all other rival flags empty and observer k outside
{a,b}, choose A_a=A_b={X,Z} and all other coalitions equal to V.
Equation (2) gives

    C_(X,k)(E) OR C_(Z,k)(E)=1.

The five-leaf quota word with pivot Z has coefficient pair (0,1), and
the pivot-X word has pair (1,0). Their explicit formulas and evaluations
are proved in [the complete pattern analysis](free-pattern-amalgamation.md).
No common lower term-induced extension can exist: it would have pair
(0,0), contradicting the displayed disjunction. Thus pointwise minima
fail joint attainment even for maximal profiles determining one exact
full operation. Its greatest extension does exist and has pair (1,1).

For exactly three old owners, that same analysis determines the entire
old-observer free-extension fibre: thirteen extensions, including six
minimal ones, six intermediate ones and one greatest. The common-source
lemma above supplies one of its necessary clause families; compatibility
between different patterns supplies the other. No claim of thirteen
extensions for fresh observers or larger owner sets is made here.
