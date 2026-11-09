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

The two testing notions now have complete characterizations and sharp counts.
Their reusable predicates remain together in `Definitions/TestDomains.lean`;
root `Paper.lean` expands all quantifiers in the theorem statements:

| Definition | Meaning and dependencies |
| --- | --- |
| `CompletePublicTestDomain D` | At every finite arity, agreement on valuations from D implies agreement everywhere for terms satisfying `IsPublic`; internal role switches are excluded |
| `CertifiesIdempotency D` | At every finite arity and for every full-language term, diagonal agreement with the identity on D implies diagonal agreement everywhere; this is not equation testing on all tuples from D |

`KFOL.Paper.reduct_test_domains` proves that completeness in the reduct is
equivalent to including every singleton and, for every observer k, an ambiguous
member omitting k. `exists_sameView_in_domain` supplies representatives within D
and the existing view congruence preserves a failed equation. Necessity uses
actual public unary equations: the singleton separator and a suppression fold
that fixes atoms while adding k on ambiguous inputs. This avoids requiring the
whole unary classification. Suppression remains a derived term construction;
no primitive reset or arbitrary set constant has been added.

`KFOL.Paper.minimum_reduct_test_domain` states leastness of the attained sizes:
six with three roles and K+2 with at least four. The lower bound counts the K
singletons and two distinct ambiguous values; with three roles coverage forces
all pairs as well. The upper bounds use the actual all-pairs domain at K=3, and
the singletons plus two disjoint pairs at K≥4. Finset inclusion, injectivity and
the previously proved unordered-pair count establish all counts generically.

`KFOL.Paper.idempotency_certificates` completes the supplementary report result
`gen:thm:idem-domain`; it remains optional in the scope inventory. For ambiguous
domains, certification is equivalent to omission of every role somewhere and
separation of any two roles by a membership test. These express empty
intersection and distinct incidence vectors, including the empty-family
convention. Both conditions are necessary even if singleton tests are allowed.
Sufficiency uses constant persistence and surviving input contributions on the
ambiguous cell. Finite permutation images contained in a test are equal to it;
incidence separation then forces every occurrence permutation to be identity.

The full diagonal size result permits arbitrary domains in the lower bound
and attains the optimum using ambiguous values alone. Roles inject into the
Boolean incidence words other than all-one, giving K≤2^m−1. `Nat.clog 2 (K+1)`
is mathlib's natural ceiling logarithm, characterized by K+1≤2^m. At least three
tests are necessary whenever three roles exist: with two tests, the conditions
would force every test to be a singleton, which an ambiguity-adder fixes
without being idempotent. The complements of singletons attain three at K=3.

For K≥4, the generic attaining construction selects K distinct proper subsets
of an m-element coordinate set, reserving all complements of coordinate
singletons. Each coordinate consequently contains at least two assigned roles,
so each test is ambiguous. Properness gives empty intersection; distinct labels
give incidence separation. Finset extension and cardinal equivalences prove
existence for every K, independently of a finite list of computed examples.
This co-singleton reservation is an alternative to the cycle used in the
written proof and establishes the same asserted minimum.

The regressions verify that two singleton tests on three roles can satisfy both
incidence conditions yet fail certification, and that a valid ambiguous domain
may omit a role from every test. Independent Python checks exhaust the small
reduct/domain cases (K=3,4) and check diagonal constructions through K=64;
these are cross-checks, not the cardinality proofs.

## Shared equational definitions

`Definitions/Equational.lean` is the fifth current definition module. It
imports `Definitions/Core.lean` and mathlib's model-theory substructures and
quotients. The generic proof modules add no primitive notion of validity.
These definitions prepare the required basis proofs; they do not themselves
complete any reset, forty-law or core nonfinite-basis statement in `Paper.lean`.

| Definition | Meaning and dependencies |
| --- | --- |
| `Equational.language σ` | A mathlib language with operation symbols `σ n` of arity n and no relation symbols |
| `Equational.Term σ Var` | Mathlib's term type; no new generic syntax datatype |
| `Equational.Identity σ` | A finite declared arity and two terms on `Fin arity`; arity zero is permitted |
| `Identity.Holds` | Equality of realizations at every valuation in the supplied algebra |
| `Identity.support`, `variableCount` | Union of actual variable supports on both sides and its cardinality, independent of unused declared variables |
| `Theory`, `Models`, `theoryOf` | Sets of identities, satisfaction, and the whole identity theory of a supplied algebra |
| `InVariety σ A B` | B is nonempty and satisfies every identity of A; independent of derivations or an HSP certificate |
| `Derives T` | Axiom instantiation, reflexivity, symmetry, transitivity, operation congruence and substitution; independent of semantic validity |
| `IsBasis`, `HasFiniteBasis` | The algebra's valid identities are exactly the derivable consequences of T; respectively existence of a finite such T |
| `HasVariableBound` | Every identity in the theory uses at most n distinct variables |
| `productStructure`, `termStructure` | Coordinatewise product operations and syntactic term constructors as operations |
| `derivationSetoid`, `termPrestructure` | Derivability as an equivalence relation and operation-compatible congruence, consumed by mathlib's quotient-structure API |
| `FullSymbol`, `CoreSymbol` | Exactly the full public and constant-free core signatures |
| `fullStructure`, `coreStructure` | Interpret these symbols using the existing shared winner-set operations |
| `Full.encode/decode`, `Core.encode/decode` | Structural codecs for the native syntax; core encoding requires `IsCore` |

All structure definitions are named values used locally, not global instances
on carriers. The left/right projection regressions give different operations
to `Bool` under the same signature and show that an identity can hold in just
one of them. Realization, structural substitution, homomorphisms, substructures,
closure and quotients are mathlib's imported definitions and belong to the
reviewed definition surface.

`Equational/Completeness.lean` proves soundness/completeness using the quotient
of the term algebra by derivability. For variables in `Type v` and symbols in
`Type u`, testing nonempty models in `Type (max u v)` suffices. The quotient is
inhabited by the term whose equality is being tested, even with no variables.
The finite-variable basis criterion therefore tests carriers in `Type u`;
soundness extends a resulting derivation to arbitrary carrier universes. There
is no universe-sized quantification over a type of all algebras.

`Equational/Preservation.lean` proves preservation by surjective homomorphisms,
substructures and arbitrary dependent products, and reflection through
injective homomorphisms. Variety membership requires nonemptiness explicitly;
substructures may be empty in mathlib. These are the HSP preservation laws,
not the reverse Birkhoff representation theorem.

`Equational/Locality.lean` transfers identities from closures of at most n
values using actual support. Evaluating a support-restricted term supplies an
inhabitant of its generated subalgebra, also for a nullary identity. A core
zero-generator closure can instead be empty; it is never assumed to be a
nonempty variety member. The generic bounded-countermodel lemma reduces a
nonfinite-basis proof to explicit finite countermodels at every support bound.
Constructing the paper's core countermodels remains separate unfinished work.

## Reset semantics and canonical tables

`Definitions/Reset.lean` adds the reset-specific definitions in one place,
bringing the current algebraic definition surface to six small modules. Reset
uses mathlib terms directly, with no new syntax datatype or evaluator recursion.

| Definition | Meaning and dependencies |
| --- | --- |
| `WinnerSet.reset A B` | Return B when B is atomic, and the union when B is ambiguous; the carrier enforces nonemptiness |
| `Reset.Symbol`, `Reset.Term` | One binary reset symbol, no constants; mathlib's relation-free terms |
| `Reset.structureOf op` | Interpret the symbol by an explicit binary operation on the supplied carrier; use locally |
| `Reset.Term.step` | Binary constructor selecting the two mathlib argument positions |
| `Reset.Term.root` | The rightmost syntactic variable, independent of semantics |
| `Reset.Term.Selected t B j` | Positive structural recursion describing selection at ambiguity-status set B |
| `Reset.Term.eval` | Mathlib realization with `WinnerSet.reset`; repeated variables retain their common valuation and independent syntactic copies |
| `Reset.Term.guards` | Finite structural collection of prerequisites for one output position, before minimization |
| `Reset.Term.minimize`, `table` | Delete nonminimal prerequisites; the resulting canonical antichain |
| `Reset.Term.composedGuards` | Finite unions of root-translated outer prerequisites with inner prerequisites; minimize to obtain the substituted table |
| `Reset.chainValue` | The fixed values {a}, {a,b}, {a,b,c}, from an embedding of `Fin 3` |
| `Reset.Laws op` | R1--R6 imposed independently on an arbitrary binary operation; no validity or derivability in the definition |
| `Reset.operation M` | Extract the binary operation from an arbitrary mathlib structure of the one-symbol signature |
| `Reset.basisAxiom`, `basis` | Six actual finite-arity identities and their range as a theory; these are syntax, not opaque predicates |
| `Reset.RootedAntimatroid Var` | A finite ground, feasible subsets, union closure, accessibility, and exactly one feasible singleton, with its unique element recorded |
| `RootedAntimatroid.Ready` | A feasible witness containing j and contained in B together with j; independent of the selector and term evaluation |
| `Reset.familyProduct` | Empty set together with unions of a left feasible set and a nonempty right feasible set |
| `Reset.TermFunction` | Actual functions on winner-set valuations that are represented by a reset term |
| `Reset.Term.feasible` | Subsets of the term's actual variable support all of whose positions are selected on their own ambiguity status |

`Reset/Selection.lean` proves every clause of `reset:lem:selection`, including
monotonicity and independence of j's own ambiguity when selecting j.
`Reset/Tables.lean` identifies table members with the actual minimal finite
status sets enabling j. It proves the upward-closure formula, antichain property,
unique empty guard at the root, and exclusion of j from its prerequisites.
`Reset/Chain.lean` separates every unequal pair of selectors on the fixed
chain and identifies table equality with validity, uniformly across role sets
with three distinct roles. `identity_holds_iff_table` exposes this directly to
the generic equational basis API. Selection and evaluation themselves require
no role-count assumption, and variable declarations need not be finite.

`Reset/Substitution.lean` proves the exact finite-table substitution formula
for actual mathlib term substitution, as well as the root and evaluation laws.
The proofs allow collisions between inner roots and repeated occurrences.
The finite union ranges over the outer term's actual variable support, so no
finite ambient variable type or arbitrary bound on variable names is assumed.

`Reset/Public.lean` supplies proof constructions `resetTerm` and `compile`,
using the existing three-owner union term and suppression traversal. A list
covering every role yields the same reset operation regardless of order or
repetitions. Compilation yields a genuine native core term and agrees on every
mixed valuation. Root `Paper.lean` states the existential expansion and full
selection result, the semantic clauses of canonical tables, and the explicit
substitution formula. Certified polynomial machine bounds remain a separate
obligation in the inventory. The six-law basis is now complete as described below.

## Six-law reset completeness

`KFOL.Paper.reset_basis` repeats the actual six identities in its statement and
asserts validity iff derivability from precisely that family, together with its
exact cardinality. The only role assumption is an embedding of `Fin 3`; variables
and roles need not be finite. `Reset.basis` is independently defined syntactic
data, `Reset.Laws` is a conjunction of ordinary algebra equations, and
`Equational.Derives` is the independently defined inference relation.
`models_basis_iff` proves that these two presentations of the six laws agree.

The proof constructions in `Reset/Basis` do not enlarge the paper theorem's
definition surface. `path` is a left-associated word with a fixed last value;
`Term.paths` constructs common-root path prefixes. `interpret` is a wrapper
around mathlib realization. `Below a b` means `op a b = a`; its reflexivity,
transitivity, antisymmetry and the needed monotonicity laws are proved from
R1--R6. It is used locally without installing global order or operation instances.

`Laws.lean` derives the needed algebraic identities. `Words.lean` proves
repetition deletion, path concatenation bounds and suffix absorption.
`NormalForm.lean` normalizes every term in an arbitrary six-law algebra.
`Coverage.lean` shows that selector coverage absorbs paths and that equal
selectors give equality in every such algebra. Paths may retain repeated
variables: proved deletion lemmas handle them, avoiding an additional
normalization algorithm or an assumption that occurrences are distinct.

`Presentation.lean` connects arbitrary language structures to the six laws and
proves concrete soundness for every role type. A kernel-checked injective
fingerprint of the six explicit syntax trees proves distinctness; the range of
`Fin 6` proves exhaustiveness and cardinality. `Basis.lean` then uses the existing
chain separator and generic equational completeness theorem to obtain actual
derivations, the independent `IsBasis` predicate and `HasFiniteBasis`.
Freese et al. (2002), introduction and Section 3, supply the proof reference;
the published theorem is not a hypothesis or a new Lean axiom.

## Antimatroid representation

`KFOL.Paper.reset_antimatroids` supplies an actual equivalence between semantic
term functions and finite rooted antimatroids. Its type repeats the subtype of
term functions and characterizes the image of every term by its ground, root,
feasible sets and readiness. `KFOL.Paper.reset_family_product` repeats the
feasible-family operation, allowing overlapping grounds and repeated labels.
The algebraic definition surface still occupies the same six definition files.

`RootedAntimatroid` uses the standard finite feasible-set axioms directly:
empty and full ground feasible, every feasible set inside the ground, binary
union closure, and removal of one element from every nonempty feasible set.
The recorded root is a feasible singleton and every feasible singleton equals
it. These axioms imply that the ground is nonempty, that every nonempty feasible
set contains the root, and that the family determines both ground and root.
Thus the record adds no arbitrary padding or extra choices to the represented
mathematical family. The ambient variable type can be infinite or empty.

`Reset/Antimatroid/Basic.lean` proves finite-union and accessibility lemmas and
recovers the family from readiness. `Product.lean` proves closure under the
independent family product and its readiness recursion. `Term.lean` interprets
reset syntax by that product and proves that readiness is exactly the existing
selector, with the stated actual-support feasible-set formula.

`Orders.lean` builds accessible orders using finite-cardinality induction.
`Paths.lean` reverses such orders into genuine left-associated reset paths and
proves that all their contributions are permitted by the family. `Synthesis.lean`
joins these paths to realize every rooted antimatroid, without a realizability
certificate supplied by the caller. This existence construction may enumerate
all feasible sets; compact polynomial table synthesis remains a separate task.

`Equivalence.lean` proves equality of these families iff equality of selectors,
and, with three distinct roles, iff equality of actual winner-set functions.
This makes choice of a representing term immaterial and proves both inverse
laws of the equivalence. Mathlib finite sets, powersets, list prefixes and
reversals supply the underlying APIs; no further library or category structure
is required. Tests include an independently specified family, overlapping
supports, distinct path orders, unused positions and both empty-domain types.
