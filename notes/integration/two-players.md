# Two-player algebra

The strong-Kleene identification `two:prop:kleene` and several retained
main-text discussion clauses are complete. The finite Kleene basis clause
is now also complete, with a direct proof and no external theorem hypothesis.
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

## Complete bounded Kleene presentation

`Definitions/Kleene.lean` lists the canonical five operation symbols (bottom,
top, meet, join, negation), raw independent laws and fifteen literal ternary
equations. The finite basis includes semilattice/distributive laws, both
absorptions and bounds, involution, De Morgan for meet, bottom complement,
and the Kleene inequality. `winnerStructure` interprets every symbol by the
actual existing winner constants, owned choices and role switch.

The eight modules under `Algebra/TwoPlayers/Kleene/` give the proof:
`Model` constructs mathlib bounded distributive lattice structure from the
raw laws; `NormalForm` proves signed DNF normalization for every generic FOL
term; `Monomials` proves the exact literal obstruction criterion by actual
three-valued probes; `Completeness` transfers every three-valued identity to
arbitrary bounded Kleene models; `Presentation` connects the explicit literal
equations to the raw laws and reconstructs arbitrary signature structures;
`Basis` invokes the proved generic equational completeness theorem; `Winner`
transfers via an actual language homomorphism; `Syntax` classifies all original
internal role permutations and translates every original full-language term
into the canonical signature, with exact evaluation preservation.

`Kleene.basis_winner` is a genuine `Equational.IsBasis` for the literal finite
basis on the actual winner carrier. `hasFiniteBasis_winner` is unconditional
apart from `labels : Fin 2 ≃ Role`. `inVariety_winner_iff_laws` characterizes
all models in an arbitrary carrier universe. `public_equational_completeness`
connects every original full-language identity to derivability of its
translated equation, so arbitrary internal switches are covered.
`tests/TwoPlayersKleene.lean` repeats the full finite basis/model claims and
checks an arity-zero derived equation and the original-syntax bridge.

No claim of minimality or independence of the fifteen equations is made.

## Validation

- `lake build KFOL.Algebra.TwoPlayers.Coordinates`: 1110 jobs, success.
- `lake build KFOL.Algebra.TwoPlayers.Kleene.Syntax`: success.
- Strict `tests/TwoPlayers.lean` and `tests/TwoPlayersKleene.lean`: success.
- Temporary `/tmp/kfol-two-players-complete-audit.lean`: imports all authored
  declarations, standard-three-axiom audit and pure import boundary pass (241 authored declarations, including the finite
  Kleene basis and original-syntax bridge).

The general owned-choice idempotence and inclusion lemmas are now consolidated
in `Algebra/Basic`. Two-player degeneracies no longer import the unrelated
atomic one-constant proof module.
