# Public algebra side claims

Three required claims are complete, with no new semantic definitions:

- `Algebra/NoBooleanProduct.lean`: `WinnerSet.no_boolean_product_embedding`
  proves `cor:no-boolean-product` for arbitrary dependent products. In fact
  distributive lattice factors suffice, rather than requiring Boolean factors.
  Every owned operation may independently select meet or join in each
  coordinate. The proof supplies an explicit three-atom nondistributivity
  witness and reflects the coordinate identity through the assumed injection.
- `Algebra/PublicContexts.lean` proves `game:prop:obs`. Any public context with
  an arbitrary Boolean choice of active input leaves and arbitrary fixed
  winner-set parameters is constant or extensive. Hence any two ambiguous
  inputs have identical singleton observations in every such context. All
  differing winner sets have a separating membership observation already in
  the identity context. No finite-role or three-role hypothesis is needed.
- `Algebra/UnaryReset.lean` proves `sym:lem:reset` using the existing actual
  suppression syntax. A list covering every role fixes every atomic input,
  retains the exact output of an extensive unary term on each ambiguous input,
  and stays extensive. The public existence corollary requires only finite
  Role, with no K≥3 assumption and no arbitrary function-realization premise.

`tests/PublicPureClaims.lean` repeats complete original claim statements and
checks the reset existence theorem. Live build: 783 jobs; strict tests pass.
Temporary `/tmp/kfol-public-pure-audit.lean` imports all authored declarations,
checks transitive standard-three axioms and pure dependency boundaries: pass.

## Public semilattices and finite folds

`Algebra/Semilattice.lean` constructs `WinnerSet.choiceSemilattice r` as an
actual mathlib semilattice. Its explicit order is
`A ≤r B ↔ B={r} ∨ (A≠{r} ∧ A.val⊆B.val)`.
The custom order is referenced through the structure's explicit `toLE`;
it is not the winner subtype's existing ordinary-inclusion instance.
`choiceFold` uses mathlib's finite nonempty sup fold. It equals the owner's
atom iff an operand does; otherwise its membership is the exact union of
all input memberships. `Term.exists_choice_fold` builds an actual binary
owned-choice term for every finite nonempty family of arbitrary existing
continuations, agreeing with the fold on every valuation. Thus binary choice
suffices, without a certificate or an external multiary operation assumption.
No finite-role or three-role hypothesis is needed.
Live build723 jobs, strict `tests/PublicFolds.lean` passes.

## Explicit quotient orders

The reserved semantic append to `Definitions/Views.lean` adds exactly two
independent tables, `PlayerView.union` and `PlayerView.choice`. All prior
semantic definitions are unchanged. The tables use actual player labels and
observation constructors; they do not evaluate chosen representatives.
`Algebra/ViewOrders/Table.lean` proves `WinnerSet.view_choice`, the actual
quotient homomorphism for every owner and observer.
`ViewOrders/Order.lean` uses actual quotient surjectivity to construct a
mathlib `SemilatticeSup` whose join is that independent owned-choice table.
`order_layers` proves every one of the nine constructor cases: other atoms
are incomparable except for the absorbing owner's atom; nonabsorbing atoms
lie below impossible, then possible, then that absorber. When the observer
owns the choice, no absorber state exists. The statement requires only
`three : Fin 3 ↪ Role`, with no finiteness or decidability assumptions.
Live build993 jobs, strict `tests/ViewOrders.lean` passes. Its complete public
prototype repeats the actual quotient map and all order comparisons.

The combined temporary `/tmp/kfol-public-pure-audit.lean` now imports every
authored declaration of all these modules and the augmented semantic Views
file, checking the standard-three axioms and the pure import boundary.

