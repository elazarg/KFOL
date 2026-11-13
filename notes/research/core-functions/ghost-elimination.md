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

The current Lean proof compiles children s,u with nonzero residues g,h
using their original subwords:

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

## Local residual compiler and exact surviving profiles

A shorter mathematical proof is now in `core:cor:residual-compiler` in the
report; this stronger compiler/profile statement is not yet a Lean claim.
For each subword u track the flags

    S_u={r: Phi_r^u(V\{X})=1}.

They say precisely which deletion singleton predicates are nonzero.
The compiled residue preserves every such predicate exactly. Removed
leaves have zero residue and no flags; ordinary leaves retain their input
and have every flag. Discard a zero child. For nonzero child residues g,h
at an r-owned root use:

| r active on left | r active on right | Residue |
| --- | --- | --- |
| yes | yes | g choice_r h |
| no | no | g union h |
| no | yes | (g union h) choice_r h |
| yes | no | g choice_r (g union h) |

An active child's ghost equals the unmarked r atom exactly when its
residue is r. An inactive ghost never equals that atom. The unions prevent
an artificial singleton created by ghost removal from absorbing the other
child. The owner-r profile in a one-active row is
(g_r AND h_r) OR h_r = h_r; foreign profiles conjoin. This proves the
residue and profile assertions simultaneously.

All removed variables can be assigned the same ghost, so the construction
also deletes arbitrary input sets in one pass. With sharing, each original
choice emits at most four primitive choice gates: union takes three and
an optional outer choice takes one. A d-gate circuit therefore has a
residual circuit with at most 4d gates, or empty residual. Flag propagation
costs O(K(d+1)) Boolean operations.

For every fixed ambiguous menu A, the same residue C satisfies
C subseteq t(A,v) and C\A=t(A,v)\A. Its nonzero singleton predicates
are exactly those of that cofactor. Singleton menus instead use the
[fixed-menu erasure compiler](retained-sources.md).

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
