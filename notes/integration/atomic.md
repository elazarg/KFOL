# Atomic function classification and binary operations

The S2 classification `gen:thm:S2` and determinacy corollary
`gen:cor:determinacy` are complete and compiled. The binary atom-preserving
classification `reset:thm:binary` is also complete, including both directions
and actual reset-term representation.

## Public statements

`Term.atomic_function_classification` in `Algebra/Atomic/Classification.lean`
states, for finite nonempty Role and finite Var, that an atomic function
`f : (Var → Role) → Role` has an actual full-language realizing term iff
it is essentially unary or has its whole output in one fixed pair.
`atomic_function_classification_with_preservation` additionally states the
term's atom-preserving property explicitly. The result includes zero arity;
there is no global lower bound on K. The paper's K≥3, positive-arity
statement follows by specialization. No Szendrei or other external theorem
is a hypothesis.

`Term.atomic_determinacy` in `Algebra/Atomic/Necessity.lean` states that,
for finite Var and any embedding `Fin 3 ↪ Role`, an atom-preserving term
fixing every constant atomic input agrees on all atomic valuations with
one fixed input position. Role need not be finite. Thus full winner-set
idempotence implies the stated determinacy corollary.

Complete paper-facing prototypes appear in `tests/Atomic.lean` with the
propositions written out, including the original full idempotence hypothesis.

`Term.binary_atom_preserving` in `Algebra/Atomic/Binary.lean` proves the
four alternatives for every idempotent, atom-preserving full-language binary
term: the two projections and the two oriented resets. Only an embedding
`Fin 3 ↪ Role` is needed for this direction.
`binary_operation_classification` is the complete iff for finite Role,
constructing actual core realizations of all four alternatives.
`binary_reset_representation` translates every such binary term to an actual
reset term agreeing on all winner-set valuations. `tests/AtomicBinary.lean`
contains the full original hypotheses and both complete public propositions.

## Proof architecture

The compact independent semantic file is `Definitions/Atomic.lean`:
repeated triples, at-most-two-valued functions, essentially unary functions,
relation preservation, atom preservation and exact atomic realization.
All use the existing public syntax and winner-set evaluator.

`Matrix.lean` proves that a nonconstant row of a matrix whose three rectangle
corners always repeat either restricts the entire matrix to a pair of values
or forces every row to agree pointwise. `FiniteProduct.lean` finds a sensitive
coordinate by finite coordinate updates and applies that matrix lemma. The
result is generic for finite coordinate sets and arbitrary nonempty input
and arbitrary output types. `Necessity.lean` connects actual term realizations
to the already-proved common-source theorem; three fixed atomic diagonals
exclude the two-valued branch and force a projection.

`Unary.lean` realizes every finite unary map by induction strictly increasing
its image: split one collision using an unused output, recurse, then wrap the
realization in the elementary merge `t ⋆_a (a b)(t)`. An injective finite map
is a permutation. `Boolean.lean` builds exact valuation tests from unary
label tests using finite conjunctions, then arbitrary functions into a fixed
pair by finite disjunctions. `Classification.lean` assembles both directions.

`OneConstant.lean` provides rigidity for the completed binary theorem:
actual core contexts with only one fixed atom either always discard the
varying input or retain all its possible winners. One distinct atomic test
therefore proves global constancy or inflationarity, including ambiguous
winner sets. It introduces no alternate term syntax.

`CoreSupport.lean` proves output support bounds and survival of an occurring
input atom when every singleton input has its label. `BinaryCore.lean` fixes
the atomic projected argument and applies one-constant rigidity; on ambiguous
inputs, support and atom survival prove the precise union. The presence of
the other argument selects reset, and its absence selects the projection.
`Binary.lean` uses the existing idempotent extraction theorem to apply this
to all full-language terms, then reuses the actual finite reset compilation
for the converse. No alternative syntax or evaluator is introduced.

## Validation

- `lake build KFOL.Algebra.Atomic.Binary`: 1107 jobs, success.
- `lake env lean -DautoImplicit=false -DwarningAsError=true tests/Atomic.lean`:
  success. The corresponding strict `tests/AtomicBinary.lean` regression also
  passes, including a four-role reset realization and reset-term representation.
  Regression examples include a two-output function depending on
  two positions, a noninjective unary map, and an arity-zero constant.
- Temporary `/tmp/kfol-atomic-complete-audit.lean` imports every authored source
  with `import all`, checks all 63 declarations' transitive axioms against
  `propext`, `Classical.choice`, `Quot.sound`, and rejects GameTheory,
  strategy/rounds and complexity imports: success.
- All modules remain in the pure mathlib layer.

The optional exact enumeration formula following the report proposition is
not proved by this slice. No count certificate or conditional clone theorem
is used in the completed statements.
