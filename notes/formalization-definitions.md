# Definitions for the completed algebra slice

The public statements `KFOL.Paper.pair_countervaluations` and
`KFOL.Paper.optimal_test_domain` correspond to `sym:thm:pairs` and
`sym:thm:optimal`. Their project-defined meaning is in
`KFOL/Definitions/Public.lean`. The reusable finite-arity testing predicate
is in `KFOL/Definitions/TestDomains.lean`; root `Paper.lean` repeats its full
quantifiers. The intrinsic-core definitions are in `KFOL/Definitions/Core.lean`.
These definitions import no GameTheory, legacy Lean modules,
probability, or complexity libraries.

| Definition | Meaning and dependencies |
| --- | --- |
| `WinnerSet Role` | A mathlib `Set Role` with a proof of `Set.Nonempty`. No finite-role assumption is built into the carrier |
| `WinnerSet.singleton r` | The set `{r}`, with its nonemptiness proof |
| `WinnerSet.union A B` | Set union, with nonemptiness inherited from an operand |
| `WinnerSet.choice r A B` | `{r}` if either operand equals `{r}`; otherwise their union. These are equality tests, not tests of membership of r |
| `WinnerSet.rename p A` | The image of A under the mathlib permutation `p : Equiv.Perm Role` |
| `Term Role Var` | Winner leaves, input leaves, binary owned choices, and internal role permutations. Occurrences are syntactic tree nodes |
| `Term.eval valuation` | Structural evaluation by the preceding four operations. Repeated input leaves receive the same winner-set value, with no constraint tying strategies in different copies |

The other project definition in that file, `Term.subst`, is structural
substitution at input leaves. It is not needed to interpret the pair theorem's
type. `Term.eval_subst` proves that substitution agrees with evaluation; it
exercises the interface needed by later equational reasoning.

The public conclusion spells out the bound as
`∀ x, ∃ a b, (valuation x).val = {a, b}`. The witnesses may coincide, so this
means one or two winners. Nonemptiness is enforced by `WinnerSet`, including
for intermediate results. The theorem states an existential failed equation,
not just preservation of a failure direction already supplied by its caller.
It holds for arbitrary role and variable types, and hence specializes to the
finite role sets of the main paper without an extra hypothesis.

`WinnerSet.SameStatus` in the proof module is the relation saying that two
values agree on every singleton test. The private pin predicate records at most
one input membership. These support the proof; neither enters the public
statement. The proof uses their definitions to establish status preservation,
monotonicity within a status cell, preservation of a single output membership,
and a simultaneous refinement of the valuation.

The imported surface needed by the theorem type is mathlib's `Set`, singleton
and insert notation, nonemptiness, `Equiv.Perm`, and Lean's dependent subtype,
equality and quantifiers. The dependency is mathlib v4.35.0, locked to revision
`56a005855ea17e0b0958f73ec801ae140b0a1679` in `lake-manifest.json`.

Root `Paper.lean` guards each theorem's exact axiom list:
`propext`, `Classical.choice`, `Quot.sound`. `KFOL/Audit.lean` checks all authored
declarations in the slice, including private helpers, and the compiled
transitive module list. `scripts/check_algebra.py` checks that the audit's
explicit import list covers the slice's source modules. Run `make check-algebra`.

The sharp domain theorem adds no primitive term constructors or operations.
`Term.unionTerm` derives union from three distinct owners; `Term.exists_constant`
constructs every nonempty ground value using winner leaves and those derived
unions. Unary equations isolate each singleton and each distinct pair, proving
necessity in the actual signature. `CompleteTestDomain` quantifies over all
`n : ℕ`, pairs of terms with variables `Fin n`, and all valuations; the domain
restricts input values only. `IsLeast` uses the ordinary inclusion order on sets,
so it states both completeness and minimality and implies uniqueness.

The only role hypotheses for this characterization are `[Fintype Role]` and
`three : Fin 3 ↪ Role`, which explicitly provides three distinct roles. They
are local theorem hypotheses. The pair theorem and all shared definitions
remain available for two players. `card_pairValues` additionally proves the
count for every finite role type, including zero, one and two roles.

The count is `Nat.card {A : WinnerSet Role // ∃ a b, A.val = {a, b}}`.
`pairValuesEquiv` in `KFOL/Algebra/TestDomainCard.lean` identifies this subtype
with mathlib's `Sym2 Role`. Injectivity uses extensional equality of the
underlying sets; surjectivity uses the exhibited pair. Mathlib's count for the
symmetric square gives `K * (K + 1) / 2`. There is no enumerated certificate or
unchecked computation in this proof. Mathlib's `Fintype`, `Nat.card`, `Sym2`,
and `IsLeast` are the additional imported notions used in these statements or
their counting proof.

The algebraic clauses of `gen:thm:core` are now stated in root
`KFOL.Paper.idempotent_elimination`, with executable extraction in
`KFOL.Paper.checked_core_extraction`. Their additional project definitions,
all in `Definitions/Core.lean`, are:

| Definition | Meaning and dependencies |
| --- | --- |
| `Term.HasWinner` | Structural occurrence of at least one winner leaf, including below switches |
| `Term.inputOccurrences` | A list of input leaves and their accumulated mathlib permutations; switches multiply on the left, so `(p * q) a = p (q a)`; repeated entries remain distinct occurrences |
| `Term.IsCore` | Exactly the fragment generated by variables and owned choices; a predicate on the existing `Term`, with no second evaluator |
| `Term.pushRenames p` | Traverse with accumulated action `p`, transport owners, remove switches and discard action at inputs; correctness is conditional on the independently defined occurrence invariant |
| `Term.extractCore? p` | A checked finite-role traversal; reject winner leaves and nonidentity action at inputs, and return the transported core when both children succeed |
| `Term.size` | The number of constructor occurrences in the tree; it does not include the bit size of a role or permutation encoding |

`CleanUnder` in `Algebra/Idempotent.lean` says there are no winner leaves and
that `p * q = 1` at every recorded input occurrence `q`. It describes the
syntax independently of extraction. `WinnerSet.Ambiguous` in that proof module
means no singleton equality holds. Neither predicate is used to conceal the
idempotency condition in `Paper.lean`: it spells out diagonal evaluation and
the occurrence conditions.

The proofs use constant persistence within status cells, then survival of each
input contribution on the all-ambiguous cell. A pair avoiding a proposed
constant disproves idempotency; a pair containing a moved role and avoiding
its image forces each accumulated permutation to be identity. Equivariance
then proves extraction correct for all valuations. The algebraic results use
arbitrary role and variable types with three distinct roles, without a global
finiteness assumption. Only the checked extractor requires finite roles and
decidable equality.

The extractor's success is proved equivalent to idempotency for three or more
roles; every successful output has equal semantics at all valuations and no
more constructor nodes, without a three-role assumption for soundness. These
facts certify its functional behavior and output size. Polynomial machine
running time still needs a finite permutation encoding, an evaluation-cost
proof and the complexity-library bridge; the full `gen:thm:core` row remains
partial until those are checked.
