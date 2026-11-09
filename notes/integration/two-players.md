# Two-player algebra

The strong-Kleene identification `two:prop:kleene` and several retained
main-text discussion clauses are complete. The finite Kleene basis clause
remains required and in progress; no known-result hypothesis discharges it.
The report's full term-function and complexity classifications are optional
and are not claimed by this slice. Two-player rounds remain with the strategic
workstream.

## Independent semantics

`Definitions/TwoPlayers.lean` names the three values using any equivalence
`labels : Fin 2 ≃ Role`, with top player `labels 0`, bottom player `labels 1`.
`value` sends the ordinary chain Fin 3 to bottom, ambiguity, top; `rank`
reads that position directly from the winner set. `forcingCoordinates` is
the pair of Boolean tests for equality to the two singleton atoms. No alternate
winner carrier or public evaluator is defined.

## Completed statements

- `Algebra/TwoPlayers/Algebra.lean` proves actual exhaustive enumeration of
  all nonempty winner sets, an actual equivalence with Fin 3, maximum and
  minimum tables for owned choice, and truth reversal for the role switch.
  `strong_kleene_identification` combines the complete operation-preserving
  equivalence in one statement. It uses only `labels`, no extra cardinality
  or decidability assumptions.
- `Degeneracies.lean` proves reset is its right projection, guarded choice
  and each policy operation are their root projection, every full-language
  term preserves atoms, every closed public term reaches an atom, and union
  is not definable in the full public syntax. Ambiguity is exactly the middle
  value.
- `CoreFailure.lean` proves every core operation increases along the truth
  chain, and constructs an actual idempotent full-language term
  `x ∨ (y ∧ ¬y)` equal to no core term on all winner valuations. This establishes
  semantic failure of the three-role core characterization, rather than only
  showing a redundant winner leaf in one expression.
- `Coordinates.lean` proves the two Boolean singleton tests jointly inject,
  commute with both owned operations as `(OR,AND)` and `(AND,OR)`, and exchange
  under the role switch. Their image consists exactly of the Boolean pairs
  with at most one true entry, giving the concrete asserted embedding in the
  two-player forcing algebra.

`tests/TwoPlayers.lean` repeats the complete identification and verifies
canonical Fin 2 examples, projection degeneration, union nondefinability and
the semantic core counterexample.

## Validation

- `lake build KFOL.Algebra.TwoPlayers.Coordinates`: 1110 jobs, success.
- Strict `tests/TwoPlayers.lean`: success.
- Temporary `/tmp/kfol-two-players-complete-audit.lean`: imports all authored
  declarations, standard-three-axiom audit and pure import boundary pass.

The general owned-choice idempotence and inclusion lemmas are now consolidated
in `Algebra/Basic`. Two-player degeneracies no longer import the unrelated
atomic one-constant proof module.
