# Term representation decision

Use native four-constructor `KFOL.Term` for the public-language traversals and
existing algebra proofs, and mathlib's relation-free `FirstOrder.Language.Term`
for generic equational proofs. Their production boundary is an exact codec,
with no independently implemented generic syntax or substitution engine.

Native syntax follows the paper's full signature directly, allows role and
variable types in separate universes, and gives the status, pin and extraction
inductions their children directly. Winner sets, sets and permutations remain
mathlib objects. The initial comparison on Lean/mathlib v4.35.0 transported the
entire pair-countervaluation theorem and checked substitution and congruence
on both interfaces. It supported keeping these native traversals.

The shared equational milestone promotes the codec from the comparison test
to the production library. `Definitions/Equational.lean` supplies the full
signature (nullary winner, binary owned choice, unary permutation) and its
core reduct (only binary owned choice). `Equational/Native.lean` proves:

- Both round trips, for every generic term and every corresponding native term.
- Agreement of native evaluation and mathlib realization.
- Exact preservation of variable support.
- Substitution compatibility: full encoding and core decoding.

A native core term carries its independent `IsCore` proof at encoding; decoding
any core-signature term produces that proof. There is no ambient full signature
in a generic core identity, and the core signature has no ground terms.
`tests/SyntaxComparison.lean` now uses the production codec to transport the
pair theorem for arbitrary mathlib terms. It contains no duplicate codec.

Generic soundness, completeness, HSP preservation and generated-subalgebra
locality use mathlib terms directly. Completeness uses mathlib's term-algebra
quotient operations and an independently defined derivation relation. This
reuses the library's homomorphism, substructure and quotient APIs without
requiring the existing algorithmic proofs to inspect `Fin n` argument tuples.
Interpretations are explicit structure values used locally; different
operations on one carrier do not install competing global instances.

The source of meaning stays the shared winner-set operations. The codec's
semantic bridge connects the two representations for every term; generic
validity and derivation remain separate definitions. No general reverse HSP
representation theorem is claimed. Reproduce all boundary checks with
`make check-algebra`.
