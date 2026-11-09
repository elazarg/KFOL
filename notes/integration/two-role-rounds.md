# Actual two-role round support and literal public folds

The complete report `two:prop:rounds` is proved for arbitrary actual finite
menus and canonical serial sequential-equilibrium distributions.

The root-owned foundation consists of `TwoPlayers/Stage.lean` (unique actual
winner law of every canonical mixed Nash stage using a designated pair),
`Values.lean` (complete scalar singleton for every actual game using that pair;
every `Game (Fin 2)` satisfies the restriction), and `Endpoints.lean` (the pure
zero endpoint iff an actual all-winning row exists, and the pure one endpoint
iff an actual all-winning column exists).

## Fold and support proof

- The generic fold theorem in `Algebra/Semilattice.lean` is pure mathlib/algebra. It proves a nonempty existing
  `WinnerSet.choiceFold` equals a nonowner atom iff every actual operand equals
  that atom. It uses the actual generated semilattice order, not an assumed
  independent three-value evaluator.
- `TwoPlayers/Support.lean` defines the literal nested public folds over the
  actual finite menus via `matrixAction`. Their four endpoint characterizations
  follow from proved owner absorption and nonowner unanimity. The two extreme
  implications are direct finite-menu quantifier implications.
- Every child game has an actual canonical SE singleton law. The proof derives
  nonempty child winner-set representatives and proves an actual representative
  is an atom iff that actual child law is the corresponding pure distribution.
- Applying the canonical stage endpoint theorems then identifies the actual
  parent support endpoints with those of the two public folds. Exhaustiveness
  of the already proved three-value winner carrier completes both formulas.

`round_support_folds` holds for every exact child winner-set readout `g`.
`exists_round_support_folds` proves these readouts exist and states the full
result with literal nested `choiceFold` expressions:

`Win(SE(round)) = (Sa.union Sb).val`, and
`Sa.union Sb = choice 1 (choice 0 Sa ({0}.union {1})) Sb`.

The witness condition is exactly `(g actions).val = possibleWinners` of the
actual child's canonical serial-SE values. There is no caller-supplied
unconnected certificate, no independently defined equilibrium recursion, and
no scalar-value premise. All finite menu sizes are allowed, including
singleton menus and unequal menu cardinalities.

`possibleWinners_context_congr` additionally proves equal possible-winner sets
are a congruence for every actual two-role round context, including repeated
independent occurrences. This is derived from the complete fold theorem.

## Validation

The production build through Support passes 3855 jobs. Strict
`tests/TwoRoleRounds.lean` repeats the complete existential finite-menu fold
proposition and checks singleton menus, a three-row/one-column actual menu,
and all-context coarse-observation congruence. The all-source transitive axiom
audit imports all five TwoPlayers modules, including private helpers, and
permits only `propext`, `Classical.choice`, and `Quot.sound`.
