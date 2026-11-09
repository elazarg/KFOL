# Complete seven-equation choice/union basis

The required core:prop:choice-union-basis is now proved directly, including
full completeness. Harding–Romanowska generation is not assumed as a
hypothesis or imported axiom.

## Exact public claim

`Dissemilattice.basis_winner` in `Core/ChoiceUnion/Basis.lean` proves
Equational.IsBasis (WinnerSet Role) theory for the actual two-operation
structure (union and the specified owner's raw choice). The only hypotheses
are `{Role : Type v}`, `three : Fin 3 ↪ Role`, and `owner : Role`.
In particular there is no finite-role assumption and no requirement that the
owner occupy a particular position in the supplied embedding.

`Dissemilattice.inVariety_winner_iff_laws` proves the whole generated variety
is exactly the nonempty models of the seven semantic laws, at arbitrary
carrier universe. `basis_three` and `inVariety_three_of_laws` prove direct
generation by the actual three-element dissemilattice.

The complete proposed Paper statement is repeated in
`tests/ChoiceUnionBasis.lean:16`. It includes the exact theory cardinality7,
finite axiomatization, IsBasis, and the full arbitrary-model characterization
with each of the seven equations written explicitly.

## Definitions and proof architecture

`Definitions/Dissemilattice.lean` is the compact independent semantic file:
a two-binary-operation language, operation getters, the seven-law predicate,
the literal seven finite-arity syntax pairs, their range theory, the actual
winner interpretation, and the actual Three tables. The two semilattice
orders are independent; no lattice absorption or second distributive law is
included.

- `Laws`: the literal seven identities are equivalent to the semantic laws;
  all hold in winner sets and Three. The independent join and meet
  semilattice structures are explicitly constructed from their own laws.
- `NormalForm`: every arbitrary term is a nonempty join of nonempty meet
  monomials. Supports are finite sets, with variable reuse justified by
  idempotence; finite distribution proves soundness for all models/arities.
- `Cover`: if, for every variable j in a monomial A, the other polynomial
  contains a support B⊆A containing j, those supports cover A. Their meet is
  exactly A, and join-monotonicity of multiplication gives absorption into
  the other polynomial. All reasoning uses only the seven laws.
- `Probe`: assign P to j, N to A\{j}, and B outside A. A monomial evaluates
  to P exactly when its support is contained in A and contains j. A finite
  join attains P exactly when a monomial does. Equality in Three therefore
  forces all the actual covering witnesses, without a certificate premise.
- `ThreeCompleteness`: the two directions of support cover give equality
  in every model. Existing generic equational completeness converts this
  into IsBasis for the exact literal seven-equation theory.
- `Embedding`: the Three points are the actual winner sets {a}, {a,b},
  {a,b,c}, for the specified owner a and two distinct other roles. This is
  an injective language homomorphism for both operations.
- `Basis`: the two variety inclusions and IsBasis for every winner carrier;
  the theory is finite and has exactly7 distinct identities. The latter
  count is proved by a separating syntactic node-count tag and exhaustive
  Fin7 case split, not native_decide. The other distributive law is proved
  false in the actual Three table.

## Validation and integration

`lake build KFOL.Core.ChoiceUnion` passes1056 jobs on Lean/mathlib4.35.
`lake env lean -DwarningAsError=true tests/ChoiceUnionBasis.lean` passes.
The concrete regression uses four roles with owner3 outside the supplied
0/1/2 embedding, verifies the exact axiom count, and checks failure of the
other distributive and lattice absorption laws.

The complete proposed Paper statement reports only propext,
Classical.choice and Quot.sound. A temporary import-all transitive audit
covers every255 authored declaration in this slice, including private
helpers and all independent definitions, and rejects strategic, round,
complexity and GameTheory imports. It passes.

Add the seven proof modules, root Core/ChoiceUnion aggregate and independent
Definitions/Dissemilattice file to full/pure audit imports and the declaration
index. Root Paper/inventory/audits and the manuscript are owned by the
coordinator and were not changed here. No commits or sibling edits were made.
