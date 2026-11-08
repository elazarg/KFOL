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
syntax independently of extraction. `WinnerSet.Ambiguous` in `Definitions/Public.lean` means no singleton
equality holds. Neither predicate is used to conceal the
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

The player-view claims are now fully stated in `KFOL.Paper.player_views`,
`KFOL.Paper.public_subdirect_representation` and
`KFOL.Paper.intrinsic_player_views`. The additional definitions are in
`Definitions/Views.lean`, except `IsPublic` in `Definitions/Core.lean`:

| Definition | Meaning and dependencies |
| --- | --- |
| `Term.IsPublic` | The reduct generated by winner leaves, variables and owned choices; internal role switches are excluded |
| `PlayerView k` | The explicit states `possible`, `other r` with `r ≠ k`, and `impossible`; the observing player's singleton belongs to `possible` |
| `WinnerSet.SameView k A B` | Equality of the observer's membership bit and every other role's singleton test |
| `WinnerSet.view k A` | Inspect membership first, then singleton equality; return `impossible` exactly for an ambiguous set omitting k |
| `PlayerView.representative three k` | Represent `possible` by `{k}`, another atom by its singleton, and `impossible` by the complement of k |
| `PlayerView.eval three k t` | Evaluate t on the representatives, then apply `view`; congruence preservation is proved separately |

The contextual statement allows arbitrary finite lists of winner-set
parameters. Terms have variables `Option (Fin n)`: `none` is the varying input,
and `some i` denotes the shared parameter value. It quantifies over all such
terms in the public reduct and all parameter assignments. This directly
captures polynomial contexts, including constants other than winner leaves.

`view_eq_view_iff` proves the observation kernel independently of contextual
equivalence. Canonical representatives prove surjectivity for at least three
roles. A bijection with `Option (Option {r // r ≠ k})` counts K+1 states, and
mathlib's kernel-quotient equivalence transfers this count to the actual
quotient. The full carrier count `2^K - 1` uses the finite powerset and removal
of its empty set. Joint injectivity follows from recovering every membership
bit. Omitting coordinate k identifies the top with its complement of k.

The homomorphism equation is proved for all public terms, and separately for
all idempotent full-language terms via the previous extraction theorem.
Operations on representatives are not assumed to preserve views. Regression
cases exhibit a switch that breaks one-player equivalence, an unrealized
`impossible` state with two roles, and incompatible product coordinates. The
representation is onto each factor, not necessarily onto their product.

`KFOL.Paper.semilattice_trace` covers all of `gen:cor:trace`, including the
clone and no-special-term clauses. Its remaining public definitions are:

| Definition | Meaning and dependencies |
| --- | --- |
| `Term.vars` | The finite set of variables syntactically occurring in the existing term; switches preserve it and choices take union |
| `WinnerSet.Ambiguous` | No singleton equality holds; the existing carrier already guarantees nonemptiness |

The clone portion is given by explicit finite-arity laws rather than introducing
a generic clone framework: every idempotent term has a nonempty union support;
two restricted operations agree exactly when their supports agree; every
nonempty finite support is realized by a core term; projections have singleton
supports; and substitution composes supports by `Finset.biUnion`, preserves
idempotency and commutes with evaluation. Together these laws give precisely
the surjective map from idempotent term operations to semilattice term
operations, with no additional category assumptions.

The same proper-pair/top test separates supports and witnesses essentiality of
every core argument. It excludes near-unanimity in every positive arity and
both Mal'cev identities, including terms with switches. Near-unanimity is
spelled out using `Function.update`; Mal'cev's two ternary substitutions are
explicit conditionals on `Fin 3`. Every valid core identity is regular. The
trace claims hold for arbitrary role types with three distinct roles; there
is no new global finiteness requirement. A regression case verifies that equal
supports can still give different results on atomic inputs, so the restriction
to ambiguous inputs is material.

`KFOL.Paper.common_source` now states all of `gen:thm:source`. Its only additional
project-defined notion is `Term.sourceOccurrences`, in `Definitions/Core.lean`:
a traversal list of pairs `(leaf, p)`, where `leaf : Role ⊕ Var` retains the
original winner or input label and `p` is its accumulated permutation. Internal
switches multiply on the left, choices concatenate their children's lists,
and repeated equal entries remain repeated. List membership therefore witnesses
an actual source occurrence. The theorem's existential quantifiers precede the
universal valuation index: the same occurrence and permutation meet every
constraint simultaneously, rather than a separately selected source per case.

The source value is written directly in `Paper.lean` as
`WinnerSet.rename p (leaf.elim WinnerSet.singleton (valuation i))`. No new
source evaluator or semantic predicate conceals its meaning. Regions are
ordinary mathlib sets, with `Pairwise (fun i j => Disjoint (regions i) (regions j))`.
The index, variable and role types may be infinite or empty where the terms
and valuations exist. There is no finiteness or three-role hypothesis.

With two distinct indices, that same source must be an input. Its membership
in the existing `inputOccurrences` list is also part of the conclusion;
`mem_inputOccurrences_iff` connects the two enumerations. At a winner source,
its fixed value `p r` would lie in two disjoint regions. The proof of existence
first chooses one child satisfying all constraints at a choice node and pulls
regions back through switches. It depends only on the shared core definitions
and elementary algebra, without depending on idempotent elimination.

`KFOL.Paper.atomic_repeated_triples` gives the immediate repeat-relation
consequence: if every input column repeats among three atomic valuations, and
the three outputs are atomic, those outputs repeat too. Atomicity is local to
those evaluations. `KFOL.Paper.no_atomic_if_then_else` rules out a selector
between any two distinct control labels, using three available roles. Both
statements spell out their atomic inputs and outputs directly; they do not
assume the external S2 classification, which remains a separate obligation.

The common-source regressions exercise necessary disjointness, the two-region
hypothesis for variable sources, permuted inputs and the empty-index case.
`checks/check_common_source.py` independently enumerates actual leaf paths and
applies their switches from the leaf outward, comparing with the existing
winner-set evaluator over 210 finite term cases. It is a finite cross-check;
the generic index- and role-polymorphic result is proved in Lean.
