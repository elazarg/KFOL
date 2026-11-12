# A self-dual weighted-majority obstruction for the canonical D extension

Let

    f(a,b,c,d,e)=ab ∨ ac ∨ ade ∨ bcd ∨ bce.

Equivalently,

    f(x)=1 iff 3a+2b+2c+d+e ≥ 5.

The weights total 9, so f is exactly self-dual:

    f*(x)=1-f(1-x)=f(x).

The canonical essential-source extension D_f is NOT a pure bichain term
operation, nor a full (inf,sup,union) term operation.

This gives a weighted-majority counterexample, not merely a nonthreshold
counterexample. No Boolean restriction of f is P4 (or its dual/permutation),
since restrictions preserve threshold functions and P4 is not threshold.
For the latter, its true assignments ac,bd and false assignments ad,bc have
the same coordinatewise sum, ruling out a threshold separation.

## The root-support fact

For a pure term s with Boolean function g, every marked variable essential
for g on a partial-input cube Q forces s=P. The stable b/c outputs are
prescribed by g at the two corners. These are the standard threshold-corner
and observer-union monotonicity arguments from the P4 obstruction.

Take a smallest pure term realizing D_f. If its root is sup with Boolean
children g,h, then g,h≤f and g∨h=f. On every nonconstant cofactor Q of f,
any coordinate inessential for f|Q must also be inessential for g|Q and
h|Q: mark that coordinate P and all other free coordinates N. Otherwise
the responsible child gives P; neither child can give c because its Boolean
function is below f and f's lower corner on Q is 0. The root would give
an unwanted P.

Call a child g 'owning' a minterm S when g(1_S)=1. Every sup cover of f has
a child owning bcd. The five cofactors below force such a child to own all
five minterms of f, hence to equal f.

| Cofactor (fixed coordinates) | f restricted | Inessential coordinate | Forced implication |
|---|---|---|---|
| a=1,e=0 | b∨c | d | bcd → abc |
| b=1,d=e=0 | a | c | abc → ab |
| c=1,d=e=0 | a | b | abc → ac |
| a=0,b=e=1 | c | d | bcd → bce |
| c=0,d=e=1 | a | b | ab → ade |

For each implication first add the fixed true coordinates by monotonicity,
then remove the listed inessential coordinate. For example, the fourth row
uses g(bcd)=1⇒g(bcde)=1 and independence of d on the specified cofactor to
obtain g(bce)=1. The last row uses g(ab)=1⇒g(abde)=1, then removes b.

Thus g owns ab,ac,ade,bcd,bce. Since g≤f and is monotone, g=f. This child
itself realizes D_f: on f's nonconstant cubes its possible trace cannot
exceed the root's trace, while every essential marked source is forced;
on stable cubes its endpoint behavior is fixed by its Boolean function f.
This contradicts minimality of the original term.

An inf root is ruled out by self-duality: exchange b,c in the four-valued
algebra and exchange inf,sup, fixing N,P. This converts a realization of
D_f into another realization of D_{f*}=D_f, preserving term size and
changing an inf root to a sup root.

A leaf cannot realize this five-variable Boolean function. Therefore no
pure realization exists.

## Full union adds no canonical D realizations

More generally, for every monotone nonconstant f,

    D_f is a full term operation iff it is a pure term operation.

Indeed distribute inf and sup separately over union to expand a full term
as a nonempty union of pure terms. On each Boolean input, D_f is the stable
endpoint f(x), and a union can equal a stable endpoint only if every summand
has that endpoint. Hence every pure summand has Boolean function f. Union
absorbs P, so each summand's possible trace lies below D_f's trace. Essential
marked sources force the reverse inclusion, and the stable outputs are
already fixed by f. Every summand therefore realizes D_f. The converse is
immediate.

Applying this fact excludes a full realization of the weighted-majority
example as well.

## Computational checks

The truth-bit mask is 3941132456, with Boolean assignments indexed by the
subset bitmask s=0,...,31 and weights attached to a,b,c,d,e in that order.
The five-variable root-admissibility enumeration in
`df-five-root-obstructions.py` finds exactly one proper admissible OR child,
namely ab∨ac∨ade, confirming that the displayed proof isolates the omitted
minterm bcd. This enumeration is corroboration; the five-cofactor argument
above is the proof.
