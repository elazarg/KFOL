# Uniform native core obstruction: integration-ready slice

This slice completes **core:prop:basis-arity** for arbitrary finite role types
with three distinct roles. It does **not** complete `core:thm:no-basis` or
`core:thm:core-nfb`, whose arbitrary-variable-bound padded-grid construction
remains necessary.

## Complete proposed public statement

`tests/CoreBasisStatement.lean` contains a compiled, complete proposition and
proof proposed for root `Paper.lean` as `core_variable_bound_obstruction`.
It quantifies over arbitrary `Role`, `DecidableEq Role`, `Fintype Role` and
`three : Fin 3 ↪ Role`, using local canonical core/native structures. It states:

- Native carrier cardinality is `K + 2`, where `K = Fintype.card Role`.
- Every core-valid identity using at most K **actual distinct variables** holds
  in the native algebra, without any bound on syntax size or declared arity.
- The explicit owner-exhaustion identity is valid on `WinnerSet Role`, fails in
  the native algebra, and uses exactly K+1 actual variables after expansion.
- The native algebra lies outside the core variety.
- No (even infinite) K-variable theory is a basis; every basis includes an
  equation using at least K+1 actual variables.

The separating syntax uses only the original owned-choice signature. Derived
union is the actual three-owner core term, and is proved to compute native
join as well as winner-set union. The nonempty exhaustion fold repeats the
first owner's summand as a base, so the displayed syntax is a harmless
idempotent repetition of the paper's finite nonempty sum; it introduces no
extra variables. The exact K+1 support count is proved, not inferred from
declared arity.

## Files owned by this slice

- `KFOL/Definitions/CoreBasis.lean`: independent native carrier/tables,
  quotient maps, explicit core terms/exhaustion identity, and Boolean profiles.
- `KFOL/Core/Native.lean`: exact atom/upper table laws, quotient preservation,
  native semilattice laws and the three-owner derived-union equation.
- `KFOL/Core/Quotients.lean`: each atom/upper omission as a substructure;
  explicit surjective quotient homomorphisms from winner sets; every proper
  native restriction D_R in the core variety, with the full role signature.
- `KFOL/Core/Locality.lean`: exact carrier count and a cardinality proof that
  at most K arbitrary generators miss one of K+1 distinguished elements;
  generated-subalgebra variety membership and all-K-variable identity transfer.
- `KFOL/Core/Profiles.lean`: monotonicity, common source for any injective
  owner family, and exact native atomic-output interpretation of profiles.
- `KFOL/Core/Exhaustion.lean`: valid separating syntax, native failure, exact
  variable count, and the universal basis variable lower bound.
- `KFOL/Core.lean`: pure aggregate.
- `tests/CoreBasis.lean`, `tests/CoreBasisStatement.lean`: computation,
  arbitrary-arity transfer specialization and the complete root proposal.

No shared definition file, Paper, audit, inventory, manuscript, toolchain or
sibling repository was edited by this agent.

## Validation

`lake build KFOL.Core` passes on Lean/mathlib4.35 with the updated root
production manifest. The core modules import only mathlib/shared algebra.
Both test files pass with `-DwarningAsError=true`. Kernel checks specialize the
carrier to 3,4,5 roles, inspect owned absorption and native union, and evaluate
an actual core-syntax exhaustion failure. A Fin4 identity-transfer test
quantifies over all terms/arities satisfying the actual variable bound.
No `native_decide`, axioms, admissions, semantic certificate hypotheses or
bounded term enumeration are used. The complete proposed root theorem reports
only `propext`, `Classical.choice`, `Quot.sound`.

The coordinator should add all seven new library imports (definition file,
five proof modules and aggregate) to the whole-source audit. Adding the pure
aggregate to `Audit/Algebra.lean` extends the independent import boundary to
this construction. The declaration index must include CoreBasis.lean as the
new independent definition surface.

## Work still required for uniform nonfinite basability

The new profile and native modules are preparation for, not a substitute for:

1. The rigid upper clone and its typed-cover HSP construction, including the
   generated-pair invariant below the reflecting element.
2. The finite padded rectangle rows and source columns, the three protected
   path arguments, and the exact three-element lower ideal.
3. Locality for **arbitrary coefficient generators** using duplicate Boolean
   row/column profiles and the typed cover.
4. Countermodels for every variable bound d; the current completed native
   obstruction only separates variable bound K for a fixed K-owner core.

Generic `Equational.not_hasFiniteBasis_of_bounded_countermodels` already
supplies the final logical reduction once those actual countermodels exist.

## Typed upper-clone cover completed

The next dependency `core:lem:typed-upper-clone-cover` is now also complete as
`Core.typed_upper_clone_cover` in `KFOL/Core/TypedCover.lean`. Its full statement
can be copied directly to Paper with the implementation proof invocation.
It quantifies over arbitrary core models C and P, a reflecting e, a proper R,
the actual eta ideal homomorphism, a surjective q, an atomic label homomorphism
and their exact compatibility. The conclusion is variety membership of the
independently defined Option-carrier rigid upper clone.

The proof constructs the subalgebra of P times D_R generated by the entire
labelled graph and the chosen upper generator. It proves the marker invariant
by closure induction, builds the explicit map to the upper clone, checks all
operation cases, proves surjectivity and applies the existing HSP preservation
API. It assumes neither a generated-pair invariant nor an HSP certificate.
The canonical derived-join model order/ideal and native atomic quotient are
proved in the supporting modules:

- `Core/ModelLaws.lean`: arbitrary-model transfer of the actual displayed core
  equations, each owner's semilattice laws, derived neutral semilattice,
  operation bound, closed lower ideal and absorption lemmas.
- `Core/AtomicNative.lean`: proper-signature atomic restriction and its actual
  upper/lower marker collapse homomorphism.
- `Core/PairModel.lean`: two-factor structure/projections and variety membership.
- `Core/TypedCover.lean`: the complete typed cover.

CoreBasis.lean has the new independent operation getter, derived join,
upperChoice/upperStructure and collapseUpper definitions. `Core.lean` imports
the new result. `tests/CoreBasisCover.lean` instantiates the complete theorem
on the one-point model with empty native typing, yielding its two-point upper
clone. The production build and strict regression pass; a whole Core import-all
closure audit in a temporary file reports only the standard three axioms.

The padded-grid countermodel and arbitrary-variable-bound local-cover arguments
remain to be implemented. The previous checklist's item1 (typed cover) is now
closed; items2–4 remain.
