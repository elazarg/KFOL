# Exact relative-safety synthesis and why canonical child tests lose information

This is an auxiliary structural reduction, not the desired short closed clone
criterion. It was used to discover the six-variable counterexample; the final
negative proof does not rely on trusting the search implementation.

A marked cube is a partial Boolean assignment Q and one free coordinate j,
interpreted as the B input having P at j, N at the other free coordinates,
and b/c at fixed 0/1 coordinates. Let Z be a set of such marked cubes.
A state (g,Z) asks for a constant-free pure bichain term whose Boolean
function is g and whose output is never P at the inputs in Z. All Boolean
functions considered are monotone and endpoint-preserving.

## Normalization

Remove from Z every cube on which g is constant. Every pure term with Boolean
function g has the corresponding stable endpoint there, independently of its
syntax. If j is essential for g on a remaining marked cube, the state is
impossible by the essential-source lower bound.

At an AND or OR gate with Boolean function g, neither child can mask P on a
nonconstant g-cube: OR has no constantly-1 child and AND has no constantly-0
child. Therefore both children must inherit every constraint in normalized Z.
Each child then removes cubes where its own Boolean function is constant.
The budget thus shrinks by intersection with the nonconstant cubes of every
Boolean function along its ancestor path.

## An exact finite proof game

Normalize every state. Take the least family W of states satisfying:

1. A projection state belongs to W when the projection avoids all its marked
   constraints.
2. (g,Z) belongs to W when g is the OR of finitely many strict monotone
   functions h_i<g, and every normalized child state
   (h_i, Z restricted to nonconstant h_i-cubes) belongs to W.
3. The dual AND rule holds for strict functions h_i>g.

Only Boolean children inessential at every marked coordinate in Z need be
considered. The number of possible states is finite at each arity.

**Theorem.** A pure term realizes a state iff the state belongs to W.

Sufficiency composes child realizations by AND/OR. Neither basic operation can
create P without a P input. Necessity follows by a least-gate realization:
children inherit normalized Z by the unmasking observation. A child with the
same Boolean function g would already realize the parent state, contradicting
minimum gate count, so a minimum realization uses strict children at its root.
Apply induction on gate count to those child realizations.

This theorem does not require a child operation to be its canonical D extension.
Replacing every inherited child budget by all inessential-source constraints
of that child's Boolean function is an unsound strengthening. The canonical
safe-child closure can therefore fail even when the original relative state
is realizable.

## Safe children as preorder cuts

For normalized (g,Z), build a directed graph on g's true Boolean assignments:
include the Boolean inclusion edges, and reverse each j-edge inside any
marked cube (Q,j) in Z. A monotone h≤g is Boolean-admissible exactly when its
true set is an upper set of the resulting preorder. This is because inclusion
encodes monotonicity, and each reversed edge encodes j-independence on Q.
AND children are the dual false-set construction.

There is a proper admissible OR cover of g iff this graph has at least two
source SCCs. If there is only one source SCC, it reaches every true assignment
and cannot be covered by a strict upper set. With multiple sources, their
principal upper sets are proper and cover all true assignments.

Applying this source-SCC alternative separately to every Boolean cofactor
is necessary for canonical D realizability, but the six-variable example
shows it is insufficient. The lost information is the inherited relative
budget required when a source-principal child is selected inside a parent.
