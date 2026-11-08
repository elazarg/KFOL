# Term representation decision

Use the native four-constructor `KFOL.Term` for this slice. It follows the
paper's full signature directly, permits role and variable types in separate
universes, and retains the existing status/pin proof's structural induction.
Winner sets use mathlib sets and permutations; native syntax is not a second
implementation of those general mathematical objects.

The comparison in `tests/SyntaxComparison.lean` was checked on Lean/mathlib
v4.35.0. It defines the same signature as a relation-free mathlib language:
one nullary winner symbol per role, one binary choice symbol per owner, and one
unary rename symbol per permutation. It checks:

- An encoding to mathlib terms and a decoding back, with `decode_encode`.
- Agreement of native evaluation and mathlib realization for every mathlib term.
- Transport of the complete pair-countervaluation theorem for arbitrary
  mathlib terms, including all three kinds of function symbol.
- Mathlib's substitution/realization theorem and operation-congruence examples
  on both interfaces. Native evaluation/substitution is proved in the library.

Both interfaces work. Mathlib supplies substitution generically; the native
proof is a four-case structural induction. Mathlib represents arguments by
`Fin n → Term`, which requires selecting positions when inspecting a choice or
rename. The native constructors give the status and pin inductions their
children directly, and suit the later tree/guard traversals. For this small
fixed signature, that favors retaining native syntax rather than requiring a
language structure and tuple indexing throughout the algebra proofs.

This does not block using mathlib's general algebra/model-theory machinery
later: the checked codec and semantic compatibility show how to cross that
boundary. The test retains only an isolated adapter to mathlib's existing
syntax/realization, and is not a second production evaluator or a dependency of
the paper. A general equational logic or HSP development has not been built as
part of this decision.

The initial successful comparison check took 1.42 seconds and about 1.1 GB peak
RSS on this workspace, including loading imported objects. That is a record of
the experiment, not a performance comparison between the two representations;
the decision rests on proof and traversal structure. Reproduce the check with
`make check-algebra`.
