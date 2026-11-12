# Neutral faces and the full projection-profile fiber

Proved uniformly in `KFOL/Core/GhostElimination.lean`, without an arity bound.
The role set has three distinguished owners; only the converse reset-lift
construction needs a finite role set. No new public semantic definitions are
introduced.

For a core term t(X,v), define its possibly empty residual by

    k ∈ D_X t(v) iff k ∈ t(I\{k},v).

This is zero or a lower-arity core operation. An ordinary variable occurrence
rules out zero. The constructive induction temporarily records whether a fresh
unowned winner survives. If a subtree is unmarked, substituting any ordinary
A for X leaves its residue unchanged. If marked, the value contains A and is
bounded by A union its residue; for ambiguous A equality holds.

If children s,u have nonzero compiled residues g,h, compile their r-choice as

    (g union s[h/X]) star_r (h union u[g/X]).

Put G=g(v) union h(v). The left operand is g(v) when s is unmarked,
and G when marked; similarly on the right. All four marking cases match the
ordinary residue of the ghost choice. A zero child uses only X and is deleted.
This avoids incorrectly treating the ghost as an empty-set unit: a ghost plus
an ordinary singleton is ambiguous and cannot become an absorbing singleton.

Consequently, among actual core operations, having exactly the singleton
outputs of X is equivalent to being X or g(v) reset X. The alternatives are
disjoint, g is unique as a full operation, and every core g has such a core
lift at finite K. Owned choices within this fiber all coincide with union.

## Direct meaning for canonical guards

Deleting a non-source variable X restricts its passive status to neutral.
Thus neutral faces of a jointly realizable source table must themselves be
jointly realizable at one lower arity. In a reset lift, the distinguished
X-source is unconditional. Every other source guard is an old residual guard
together with the literals excluding all rival-owner atoms at X. This explains
why even literal projection profiles retain the lower-arity global problem.
The displayed guard formula is a research consequence of the semantic theorem;
no separate public syntactic guard identity is asserted.

## What these faces miss

`KFOL/Core/CrownResiduals.lean` proves that every proper residual of the cyclic
noncore operation is simply input union. More generally, any nonempty family
of ambiguous inputs omitting k leaves only the union of inputs outside that
family visible to k. This holds for any selected set of exceptional cylinders
and any permutation, provided there are at least three variables.

The three-variable assumption is essential: with just two variables, an
exceptional cylinder can introduce b even though the sole other input is c.
The two strict regression files cover this and the ghost compiler boundaries.

Thus even all iterated lower-arity residual tests miss the crown's global
interaction. Adding one common full atomic realizer still does not suffice:
a four-variable research counterexample has explicit core realizers for its
atomic restriction and every neutral face, canonical monotone guards,
admissible profiles, whole-input provenance and omission independence.
Its observer trace is the nonterm essential-source extension of
AB OR AC OR BD. The [standalone gluing package](face-gluing/README.md)
gives the two-region definition, short witnesses and independent checks.
It is not yet a new Lean theorem or report claim.

## A different canonical shortcut fails

[The canonical blocker certificate](canonical-blocker-shortcut.md) shows that
checking every target cut against all input-column-sound heads does not remove
the need for invariant auxiliary support. Its explicit two-choice term already
violates the purported consequence. Repeatedly checking the blockers would
restore a closure computation rather than solve the direct structural problem.
