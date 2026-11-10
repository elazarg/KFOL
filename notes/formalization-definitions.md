# Definitions and representation boundaries

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
`propext`, `Classical.choice`, `Quot.sound`. `KFOL/Audit.lean` checks every
authored declaration, including private helpers in the machine branch.
`KFOL/Audit/Algebra.lean` separately checks the compiled transitive imports of
the pure algebra and word semantics. `scripts/check_algebra.py` checks exact
source coverage by the whole-project audit and builds the pure target before
loading Paper and the machine proofs. Run `make check-algebra`.

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
assume the external S2 classification. Its full local proof and realizations are now checked in `Algebra/Atomic`, as documented below.

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
alongside the other algebraic definition modules. Reset
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
all feasible sets; the compact candidate-table construction below uses one path
per listed prerequisite instead.

`Equivalence.lean` proves equality of these families iff equality of selectors,
and, with three distinct roles, iff equality of actual winner-set functions.
This makes choice of a representing term immaterial and proves both inverse
laws of the equivalence. Mathlib finite sets, powersets, list prefixes and
reversals supply the underlying APIs; no further library or category structure
is required. Tests include an independently specified family, overlapping
supports, distinct path orders, unused positions and both empty-domain types.

## Compact candidate tables

All new definitions remain in `Definitions/Reset.lean`:

| Definition | Meaning and dependencies |
| --- | --- |
| `Reset.GuardTable` | A candidate root and finite prerequisite family at each ambient position; no assumed term or realizability proof |
| `GuardTable.Enabled` | Some listed prerequisite is contained in the supplied ambiguity set |
| `GuardTable.Constructible` | An inductive finite sequence of fresh enabled additions, independent of terms, antimatroids and checkers |
| `GuardTable.IsAntichain` | No distinct comparable prerequisites at the same output |
| `GuardTable.WellFormed` | Antichain minimality, exactly the root's empty guard, self-exclusion, and constructibility of all listed prerequisites |
| `GuardTable.entryCount` | The sum of prerequisite counts over finite ambient positions |
| `Term.guardTable` | The independently defined term root and canonical minimal tables |
| `GuardTable.advance`, `reached` | A parallel greedy round restricted to the target, and its finite iteration from the empty set |
| `GuardTable.constructibleCheck` | Test whether the target is reached after as many rounds as its cardinality |
| `GuardTable.badGuards`, `check` | Executable finite scans of listed guards and ambient positions; no search over arbitrary subsets |
| `Term.size` | Count of all variable and primitive reset occurrences in the expanded syntax tree |
| `Term.leafCount` | Number of variable leaves, including repeated copies |
| `Term.occurrences` | Syntactic occurrences of one variable, independent of guard extraction |
| `Term.collectGuards` | A structural traversal carrying child roots and one raw prerequisite entry per leaf |
| `Term.guardEntries` | The traversal's raw entry list, before duplicate removal and minimization |
| `Term.pathTerm`, `joinPaths` | Left-associated primitive paths and their common-root join; now colocated with the algorithm definitions |
| `GuardTable.greedyCandidates`, `greedyOrder` | Fresh enabled target positions and a bounded root-first order, choosing the least enabled position at each step |
| `GuardTable.greedyPath` | Reverse the computed order into a primitive reset path |
| `GuardTable.guardList`, `synthesisPaths` | Colexicographically list the supplied guards and construct exactly one path per prerequisite |
| `GuardTable.synthesize` | Return the joined primitive term when recognition succeeds, otherwise return `none` |

`KFOL.Paper.reset_table_realizability` repeats every candidate condition and
proves equivalence with an actual term whose size is at most `1 + 2nM`.
`reset_table_recognition` connects the executable Boolean recognizer to actual
realizations and states the bounded greedy criterion. The local completeness
condition is repeated in `reset_table_local_completeness`, with just the
self-exclusion hypothesis needed by its proof.

`Realizability/Constructible.lean` proves union closure, accessibility and
greedy progress directly from the inductive definition; cardinal induction
establishes equivalence with local completeness. `Model.lean` builds the finite
rooted antimatroid of constructible sets on exactly the active positions.
`Necessity.lean` uses minimality and accessible orders to prove that every
canonical prerequisite is itself feasible and constructible.

`Size.lean` counts path leaves, reset nodes and joining nodes.
`GreedyOrder.lean` proves that the executable greedy order stays feasible,
introduces no repeated positions, and covers every constructible target that
contains the root. Reversing this order yields a path with exactly the requested
support and only permitted selectors. `Synthesis.lean` proves that joining one
such path per listed prerequisite gives exactly the candidate selectors and
minimal tables, with at most `1 + 2nM` primitive occurrences.

`KFOL.Paper.reset_table_synthesis` states that the executable synthesizer
succeeds exactly when an actual realization exists, and that every returned
term has the requested root, canonical tables and size bound. The algorithm
requires `[LinearOrder Var]` locally. Mathlib's finite-set sorting and
colexicographic order list only supplied guards; no powerset is enumerated.
The order-free existence theorem is now a corollary of this same construction,
using an arbitrary finite enumeration inside its proof. The earlier separate
path-choice construction has been removed.

`Recognition.lean` proves correctness of the executable checker and its
at-most-target-cardinality greedy rounds. Polynomial machine-time bounds
remain obligations.

Regression cases independently specify alternative prerequisites, an unused
input, a dependency cycle, multiple empty-root guards, self-dependency and a
dominated guard. Acceptance yields an actual term and its size bound; rejection
of the cycle rules out any realizing term. The synthesis regressions inspect
actual output guards and occurrence counts and check that completed orders
remain unchanged with extra fuel. Finite computations use kernel `decide`
after proved sorting rewrites, with no `native_decide` or unchecked enumeration
assumption.

## Extraction and description size

`KFOL.Paper.reset_guard_extraction` connects the executable traversal to the
independent structural root, raw guards and canonical tables. Child roots are
carried in the recursive results. Filtering the entry list by output and
removing duplicates recovers the existing raw guards; antichain minimization
then gives exactly the existing canonical table. This correspondence holds
without a finite ambient variable type or an ordering of variable names.

`KFOL.Paper.reset_table_size` repeats the occurrence and description bounds.
For L variable leaves and n distinct occurring variables, there are at most L
raw or canonical entries, and each output has at most as many distinct guards
as its syntactic occurrences. The actual raw traversal list, including
duplicates, uses at most `1 + L²` label occurrences. The canonical description
uses at most `1 + nL`, hence also `1 + L²`. The description counts the root,
each output label and all its prerequisite labels. Every collected label is
in the term's actual support; unused ambient positions have empty tables.
The exact relation to the existing primitive-tree size is `size + 1 = 2L`.

`Reset/Extraction.lean` proves these results directly by binary syntax induction,
finite sums and cardinality bounds. It imports the table/substitution API and
does not depend on the antimatroid representation or its synthesis proof.
The elementary primitive-size constructor lemmas now live in `Reset/Basic.lean`.
`entryCount_guardTable_le` connects the support-based count to the earlier M
on arbitrary finite ambient input types. Binary label encodings and certified
machine running time belong to the separate complexity branch.

Regressions inspect complete traversal lists for alternative paths, duplicate
raw entries and self-dependencies removed by normalization. A term over the
infinite variable type ℕ, using labels 7 and 100000, checks that the bounds
depend on actual support rather than the size of an ambient declaration.
All finite checks use kernel `decide`.

## Word representations and the first machine component

The algebraic definition files remain independent of machine libraries.
The seventh definition file, `Definitions/Algorithms.lean`, adds the following
mathlib-only representations and program:

| Definition | Meaning and dependencies |
| --- | --- |
| `Algorithms.Bitset.encode` | One membership bit per position in `Fin n`, in increasing index order |
| `Algorithms.Bitset.decode` | Accept exactly width n and recover the represented finite set |
| `Algorithms.GuardWords.readBit` | Position lookup, returning false outside the word |
| `GuardWords.subsetStep` | Conjoin the previous flag with one coordinate implication |
| `GuardWords.subsetScan` | Visit each position below the ruler's length; ruler bit values do not control the iteration count |
| `GuardWords.subsetWord`, `subsetFn` | Reject unequal widths, test subset inclusion, and expose the fixed-arity word interface |

`Algorithms/GuardWords.lean` proves both directions of the exact codec, the
total word semantics and equivalence with finite-set inclusion. Its
`enabled_iff_subsetWord` theorem connects that test to the existing
`Reset.GuardTable.Enabled` predicate. These proofs import no complexity classes.

`Complexity/Language.lean` imports the successor native multitape-machine
predicate `Turing.MultiTapeTM.ComputableInPolyTime`, with explicit injective
input/output encodings. It quantifies over actual deterministic machines and
polynomial bounds. No project-specific efficiency predicate is introduced.
`Complexity/GuardSubset.lean` certifies the independent word scan using a typed
suffix fold with a one-bit accumulator. Root `reset_guard_subset_machine`
repeats the native certificate, exact codec, total semantics and enabling bridge.

This is a dense membership-word intermediate representation, already indexed
by `Fin n`. Sparse binary variable-name encodings, support compression, record
framing, native binary input-tree codecs and their size bounds are now checked
below; full machine traversals retain their separate obligations. The
primitive loops on input word lengths, with no decoded numeric-value clock.
Regressions cover coordinate order, failed inclusions, unequal widths, the
empty width, the actual certified fixed-arity function and guard enabling.

## Compact support dictionaries and binary records

`Definitions/Algorithms.lean` additionally defines `SupportIndex.labels`,
`locate`, `compress`, `expand` and `compressEntry`. The dictionary deduplicates
the collector's actual leaf labels. Lookup returns an optional finite index;
set compression records membership at dictionary positions and expansion maps
those positions back to their original labels. Unknown output labels are
rejected. Prerequisite coverage is proved for all actual collected entries.

`Algorithms/SupportIndex.lean` proves that the dictionary has no duplicates,
contains exactly the term's support and has length n equal to that support's
cardinality, with `n ≤ L` for L leaves. Mathlib's list indexing equivalence
identifies its positions with the supported labels. Compression and expansion
are inverse on covered sets, and the certified subset-word test remains exact
when the right status set contains extra unused labels. This extends the
guard-enabling bridge to arbitrary decidable variable types.

The representation definition file `Definitions/Encoding.lean` contains the
backend-independent binary-codec boundary. `KFOL.Words` defines minimal
little-endian names, exact decoding, doubled-bit framing, prefix parsing and
complete block parsing using mathlib only. Proofs are in `Algorithms/Words.lean`,
with attribution to the original v1 framing proofs. This preserves the earlier
word language without coupling it to a machine library:

| Definition | Meaning and dependencies |
| --- | --- |
| `GuardRecord.Record n` | A compressed output in `Fin n` and a prerequisite subset of `Fin n` |
| `GuardRecord.encode`, `decode` | One framed canonical binary output index followed by exactly n membership bits; reject invalid framing, index codes, ranges and widths |
| `GuardRecord.encodeList`, `decodeList` | Independently framed records with complete input consumption |
| `LabelDictionary.encode`, `decode` | Framed canonical binary names, preserving their list order; uniqueness comes from the support construction |

`Algorithms/Framing.lean` proves successful complete block parsing has no
unconsumed suffix and supplies exact list-codec lemmas. It uses the existing
library parser. `Algorithms/GuardRecord.lean` proves both directions of every
record, record-stream and dictionary codec. A record uses `2 * index.size + 2 + n`
bits; M framed records use at most `6M(n+1)` bits. The already encoded table
tail is not repeatedly doubled by nested framing.

`KFOL.Paper.reset_support_indexing` repeats the compact dictionary, indexing
equivalence and subset-preserving round trips. `reset_guard_record_codec`
repeats the exact codecs and bit-size statements. `reset_binary_guard_records`
constructs all records from the actual term, proves decoded expansion recovers
its occurrence list and canonical tables, and bounds their stream by
`6L(L+1)` bits. The binary dictionary costs at most twice the sum of input
leaf-label bit widths plus `2L`, using one copy of each distinct name.

These are representations and encoded output-size proofs. Complete descriptor
validation and shared-support identity checking are proved below; machine-time
certificates for record scans and complete table algorithms remain separate.
The codecs preserve a chosen dictionary and record order; comparison uses the
decoded canonical tables under a shared dictionary covering both supports.
The generic compression lemmas support that shared-dictionary use. Regressions use
widely separated labels, a nonzero root index, repeated occurrences, exact
bit counts and malformed fields or trailing data. Every finite check uses
kernel `decide`.

## Original binary input trees and extraction

`Definitions/Encoding.lean` also contains the entire original-input boundary;
no additional definition file is introduced:

| Definition | Meaning and dependencies |
| --- | --- |
| `TermCode.encode` | Prefix binary syntax: `false` followed by a framed canonical binary label for a variable; `true` followed by two successive child codes for reset |
| `TermCode.parse` | Partial tree parser returning the unconsumed suffix, with structural fuel on recursive depth |
| `TermCode.decode` | Supplies input bit length as fuel and accepts exactly one complete tree |
| `TermCode.extract` | Decodes the original input, runs the existing collector and support compressor, then pairs the binary dictionary with its raw record stream |

Only variable labels are framed. Subtree codes are concatenated directly,
so neither syntax depth nor repeated variables cause repeated framing of
an already encoded subtree. Numeric label values never provide a loop clock.
`Algorithms/TermCode.lean` proves the partial parser reconstructs the entire
input, including its returned suffix. Syntax size is sufficient fuel for any
suffix, and input bit length always provides enough fuel for complete decoding.
The exact two-sided codec, injectivity and rejection of every nonempty suffix
are repeated in `KFOL.Paper.reset_binary_input_codec`.

For a tree t with L leaves and S syntax occurrences, the code length is
`S + 2L + 2 * sum(label.size)`, where the sum counts every original leaf
independently. This relates the mathematical syntax measure to actual binary
input length, including sparse names and repeated occurrences.

`KFOL.Paper.reset_binary_extraction` states that the executable frontend
accepts exactly valid syntax and recovers the original raw occurrence list
and canonical tables. For N input bits the dictionary has at most N bits,
the raw stream has at most `6N(N+1)` bits, and the complete paired output has
at most `6N(N+1) + 2N + 2` bits. The proof supplies the output of the actual
program, without assuming a supplied guard certificate. Tests compute prefix
parses, fuel exhaustion, truncated trees, invalid labels, arbitrary suffixes,
sparse names, repeated leaves and the complete decoded frontend output using
kernel `rfl` and `decide`.

These are exact executable semantics and bit-size bounds. The parser and
frontend have not yet been certified in the machine model. Complete candidate
validation and shared support for identity inputs are now checked below;
record/table machine scans and full algorithm running times retain their own obligations.

## Complete descriptors and external table recognition

`Definitions/Encoding.lean` defines `GuardDescriptor` with a natural-name
dictionary, a proof that its names are distinct, and a list of records indexed
by its length. The descriptor allows unused dictionary positions and repeated
records. Its list order is preserved by the codec; it does not define a unique
representation of an algebraic function. No new definition file is introduced.

| Definition | Meaning and dependencies |
| --- | --- |
| `GuardDescriptor.encode`, `decode` | The frontend's paired dictionary/record format, with strict complete parsing and an explicit dictionary uniqueness check |
| `GuardDescriptor.guards` | The finite set of all listed prerequisites at an output; duplicate records merge, dominated guards remain |
| `GuardDescriptor.root?` | The first listed output with an empty prerequisite; it need not be dictionary position zero |
| `GuardDescriptor.table` | Candidate guards at a supplied root, independent of recognition |
| `GuardDescriptor.check` | Run the existing table checker at the inferred root, or reject if no root is listed |
| `GuardDescriptor.recognize` | Decode an external word and run the semantic check, rejecting malformed words |

`Algorithms/GuardDescriptor.lean` proves the exact two-sided codec and
injectivity. Successful decoding validates canonical name/index codes,
dictionary uniqueness, output ranges, prerequisite widths and complete framing.
Both dictionary length and record count are bounded by encoded input length.
Expanding and recompressing the records is exact, and enabling is precisely the
previously certified subset-word predicate applied to a listed record.
`KFOL.Paper.reset_binary_descriptor_codec` repeats these statements and connects
every original extraction output to its decoded descriptor and occurrence list.

The semantic check is equivalent to existence of a root satisfying all the
independent table conditions: antichains, exactly one empty-guard output,
self-exclusion and constructibility of every prerequisite. The unique
empty-guard condition justifies the root scan. The table's entry count equals
the number of distinct records, proved by mathlib's finite fiber-cardinality
formula. Reusing the existing realizability theorem yields an actual primitive
tree of size at most `1 + 2nM` for n dictionary positions and M listed records.
For N external input bits this gives a witness of size at most `1 + 2N²`.
`KFOL.Paper.reset_encoded_table_recognition` repeats the logical conditions and
the actual-term characterizations, including malformed-input rejection.

Parsing accepts raw descriptors produced by extraction. Semantic recognition
checks the listed guards as canonical tables: it rejects dominated guards or
self-dependencies rather than silently minimizing them. Tests exercise this
distinction, duplicate names and records, unused dictionary positions, a nonzero
root index, rootless and multi-root candidates, dependency cycles, wrong widths,
bad output ranges and incomplete frames. All computations use kernel `decide`.
The full encoded recognition running-time certificate is now in `Complexity/RecognitionMachine`.
Raw-to-canonical normalization and shared-dictionary identity checking are
now connected below.

## Binary normalization and shared-support identities

The existing `Definitions/Encoding.lean` adds these definitions:

| Definition | Meaning and dependencies |
| --- | --- |
| `GuardDescriptor.minimalRecords` | Filter a record when a strictly smaller prerequisite is listed at the same output; scan only explicit records |
| `GuardDescriptor.normalize` | A structural wrapper around that filter, preserving the dictionary, index type, order and multiplicity of minimal records |
| `GuardDescriptor.normalizeWord` | Decode a complete descriptor, normalize it and return its complete encoding; reject malformed inputs |
| `ResetEquation.labels` | A distinct dictionary covering both terms' actual supports |
| `ResetEquation.check` | Collect and compress both occurrence lists in that dictionary, normalize them, and compare the finite guards at every position |
| `ResetEquation.checkWord` | Parse a pair of binary original-tree codes and run the shared-support checker; reject malformed pairs or trees |

`Algorithms/Normalization.lean` proves the record filter yields exactly
`Reset.Term.minimize` at each output, preserves enabling, is idempotent and
cannot increase encoded size. Binary normalization succeeds exactly when
descriptor parsing succeeds and returns a valid stable output.
`KFOL.Paper.reset_record_normalization` repeats the complete statements.
This is not a unique byte representation of a term operation: dictionary
order and minimal duplicates are preserved.

The generic algebraic lemma `Reset.Term.minimize_image` proves minimal guards
commute with injective renaming. `Reset.Term.guardEntries_relabel` proves raw
extraction commutes with every mathlib variable relabeling, including noninjective
maps. These are pure mathlib proofs in `Reset/Tables.lean` and
`Reset/Extraction.lean`. A dictionary inverse renames actual original syntax
back to finite positions, giving an actual realization of its normalized
descriptor. `KFOL.Paper.reset_normalized_binary_extraction` proves these outputs
pass semantic recognition and expand to exactly the original canonical tables.

`Algorithms/SupportIndex.lean` generalizes compression to every distinct
dictionary covering a term. `Algorithms/ResetEquation.lean` uses this with the
union of two supports. The shared dimension is bounded by the sum of leaf counts
and by original input bits, independently of numeric name values. Comparing
normalized finite guards is equivalent to equality of the original natural-name
tables, including outputs absent from either side. The existing chain theorem
then identifies success with equality on every winner-set valuation for any
role type containing three distinct roles.

`KFOL.Paper.reset_binary_equation_checker` repeats both the term-level and
complete binary-language characterizations. It explicitly rejects malformed
equations and does not compare independently serialized descriptors. Regressions
include equal terms with different dictionary orders, distinct variables with
identical local record streams, nonassociativity, repeated-variable elimination,
normalization before recognition, exact bit counts and invalid equation framing.
This frontend uses the two representation files. Original-tree parsing/extraction, equality, descriptor normalization and recognition now all have native polynomial machine certificates.


## Native machine and strategic dependency interfaces

The machine model is the successor's native `Turing.MultiTapeTM` interface.
`encBits` preserves original words, `encNat` stores names in binary, and
`encUnary` is used only for word/list lengths that are bounded by input size.
`encOption`, `encList`, `encPair` and `encPi` specify typed intermediate data.
`Complexity.DescriptorValidation.descriptorEncoding` is the existing
`GuardDescriptor.encode` bundled with its proved injectivity; it adds no new
meaning. Full unconditional machine statements appear in
`Paper.binary_framing_machines` and `Paper.binary_descriptor_machines`.

`Audit/Dependencies.lean` compiles canonical GameTheory Nash, pure SPE, SE,
existence and minimax declarations and audits their transitive axioms. The KFOL
strategic and round compilers are still separate obligations. These imports
remain outside the pure algebra/word audit.

## Guarded-owner definitions

`Definitions/Owner.lean` is the ninth definition module. It defines H by the
existing choice/reset operations, a mathlib signature with reset and labelled
ternary H, root/evaluation/owner restrictions, raw occurrence guards and the
explicit three-role minimal valuation. A guard has a source, ambiguous-input
tests and non-owner-atom tests, represented as finite lists of conjunctions.
Coverage is exactly source equality, ambiguous-test inclusion and the displayed
source-discharge rule for non-owner tests. Separate occurrences produce separate
guards. No equilibrium concept or GameTheory import enters this signature.

`Owner/Completeness` proves exact implication/separators and one-outsider
identity checking. `Owner/Public` compiles actual owned-choice syntax and proves
idempotence, atomic-root preservation and the main H example. `Owner.Four`
is an independent four-state algebra, with concrete embedding and observer
projection proved in `Owner/Four.lean`. Both theory equivalence and minimum cardinality are proved.
`Owner/SmallModels` kernel-checks every three-element reset operation using
proved reconstruction from its off-diagonal cells. `SmallCarriers` transports
this to arbitrary finite carriers, and `Minimum` excludes every smaller
generator by complete finite-arity identity comparison, without an outside
classification hypothesis.

## Uniform native core obstruction

`Definitions/CoreBasis.lean` is the tenth definition module. The native carrier
has one atom per role plus lower/upper ambiguity markers, with explicit join
and owned-choice tables. Omission/quotient maps, the derived pure-core union,
owner-exhaustion identity and Boolean profiles are independent definitions.
`Core/Quotients` and `Core/Locality` prove proper omission membership and locality
for arbitrary generated sets. `Paper.core_variable_bound_obstruction` proves
that the K+2-element algebra transfers every <=K-variable identity, fails the
explicit valid exhaustion identity with K+1 actual variables, and excludes
all bases restricted to K variables. Full nonfinite basability needs the
subsequent typed-cover and padded-grid construction for every variable bound.


## Minimum reset generator and the typed upper clone

`Reset/Generator.lean` interprets the reset symbol on `Fin 3` by
`if j = 0 then 0 else max i j`. `Paper.reset_minimum_generator` compares every
finite-arity identity with the winner-set interpretation and excludes every
smaller finite carrier. `Algebra/SmallCarriers.lean` supplies the shared fact
that any idempotent operation on at most two elements is associative. The
three-point reset table is explicitly nonassociative. No additional semantic
definition or external classification is used.

`Definitions/CoreBasis.lean` also defines `Core.operation` as the interpretation
of the actual owned symbol, `Core.join` by three distinct owned symbols,
`upperChoice`/`upperStructure` on `Option C`, and `Native.collapseUpper`.
`none` is the new upper-clone element; `some c` is the old element. Products
with the new element use the displayed multiplication in the report.
`Core.ModelLaws.ideal hC three e` is the induced substructure on
`{c | Core.join three c e = e}`; its closure is proved from core identities.
`Native.atomicRestriction R` has the lower marker and the atoms in R.
`Native.restriction R` additionally has the upper marker; `collapseHom`
identifies its upper and lower markers. These bundled proof constructions
carry the induced operations, without new operations supplied by the user.
`Paper.core_typed_upper_clone_cover` repeats every reflecting, typing, model,
surjectivity and compatibility premise from the report. It builds the generated
pair subalgebra and map rather than assuming a cover certificate.

## Whole descriptor machine certificates

`Complexity/RawRecords.lean` translates decoded dependent records to binary
index/word pairs with exact two-way encoding bridges. `OptionTraversal.lean`
proves charged traversal and optional-result composition rules in the native
machine model. `NormalizeMachine.normalize_polyTime` and `normalizeWord_polyTime`
certify the existing functions, including order and duplicate preservation.
`ReachMachine.constructible_view` identifies the bounded record scan with the
independent inductive `Constructible` predicate for every candidate table.
`RecognitionMachine.check_polyTime` and `recognize_polyTime` certify the actual
checker and external recognizer. Binary values never supply an uncharged clock:
rounds are bounded by word width and every lookup scans actual encoded records.
The public semantic and machine claims are combined in
`Paper.reset_encoded_table_recognition` and `reset_record_normalization`.


## Public strategic interpretation

`Definitions/Strategic.lean` is the eleventh definition module. It imports the
narrow canonical GameTheory equilibrium core; pure algebra never imports it.

| Definition | Meaning |
| --- | --- |
| `Strategic.Tree` | Finite binary public game with a role at each decision and a winner at each leaf |
| `Strategic.Profile`, `winner` | Complete actions in both subtrees, including unreached ones; the selected terminal winner |
| `Deviation i p q` | Every choice of other roles stays fixed; all choices of i may change simultaneously |
| `IsNash` | Any unilateral deviation that wins for i already wins for i in the original profile |
| `Restriction` | Restriction to any actual subtree, without a reach-probability condition |
| `IsSubgamePerfect` | Every restricted profile is Nash; neither backward induction nor local optimization occurs in the definition |
| `possibleWinners` | Roles winning under some complete profile satisfying that independent SPE definition |
| `assemble`, `gameForm` | Canonical GameTheory deterministic strategic form: one plan per role, reading only each actual owner's entries |
| `winningPreference` | A law is preferred exactly when its probability of the player's own victory is at least the alternative's |
| `OpponentDeviation`, `CanForce` | Joint changes by all opponents preserving the designated player's actions; a full plan winning against every such change |
| `Tree.rename`, `Profile.rename`, `compile` | Internal role switches affect owners and leaves; full public terms compile to trees with independent repeated occurrences |

A player-indexed strategic-form plan contains redundant entries at other
owners' nodes. The evaluator ignores them. Both directions of unilateral
replacement correspondence are proved in `Strategic/Basic.lean`, so redundancy
introduces no extra profitable deviations. `spe_iff_gameTheory` identifies the
independent definition with the library's canonical Nash predicate in every
subtree. This public perfect-information branch needs no protocol compiler or
belief model. It does not identify historywise optimality and subgame perfection
in hidden games.

`Strategic/Adequacy.value` bundles `possibleWinners` using the proved existence
of an SPE. `neutralTree` is explicitly the three-node, four-copy term.
`Strategic/Forcing` proves the singleton characterization from independent
opponent deviations. `Strategic/Compilation` proves the entire term interpreter,
including switches. Regressions distinguish Nash from SPE at an unreached
subgame and reproduce the three-role example with an extra inactive role.

## Owner synthesis and variable obstruction

The canonical-table and synthesis definitions were consolidated into the existing
`Definitions/Owner.lean`. `GuardPair` is the finite ambiguity/non-owner test pair;
`GuardTable` records an independent root and an explicit source/guard list.
`Canonical` states root, self-exclusion, disjointness, minimality and duplicate
conditions. `Enabled` gives table meaning for arbitrary status and membership
sets. `Realizes` asserts fixed root, single-owner syntax and exact outsider
semantics on every winner-set valuation; it mentions no checker or saturation.

`SaturationState` stores accumulated ambiguity/non-owner tests. `Below` means
both sets of effective tests strengthen; `rank` counts their finite sizes.
`target`, `UpdateAllowed`, `run`, `accepts`, `guardPath`, `check` and `synthesize`
are the report's explicit finite scans and actual native syntax construction.
`Listed` requires an explicit dictionary covering every relevant position and
permits unused/repeated entries. Fixed-point/order-independence and raw-occurrence
necessity are proved in the Owner proof modules. The returned primitive tree
has size at most `1+M*(10n+7)`, including every copied variable.

`Owner.BasisObstruction` in the same definition file contains the separate
four-element W table, proper-subalgebra embeddings and the literal four-variable
root-expansion identity. Every <=3-actual-variable identity transfers to W,
even with padded arity and unbounded depth; root-expansion fails. The complete
root claim repeats that identity and the lower bound for every basis.

## Complete original-tree machine certificates

`TermMachine.termEncoding` is exactly the original `TermCode.encode` together
with its proved injectivity. The stack parser is proved equal to the original
decoder on every word. Its reusable charged-fold certificate allows any
polynomial-size cached annotation with certified leaf/node operations.
`TermSupport` computes the existing rightmost-deduplicated support dictionary;
`GuardExtraction` accounts for every original occurrence and prerequisite.
`GuardCompression` uses binary name membership/index scans and proves exact
agreement with dependent finite-index records. `ResetEquality` normalizes both
sides under one actual shared dictionary and compares the sets of records,
ignoring their incidental order and duplicate representation.
`Paper.reset_binary_equation_checker` combines exact semantics, malformed-input
rejection and native polynomial-time machines for the original typed and binary
word inputs. Whole owner-table recognition and synthesis now have native certificates too. Other signature frontends and reductions remain separate.

## Boolean disclosure protocol gate

`Definitions/Rounds.lean` is the twelfth definition module. `bitDisclosure`
uses GameTheory's finite-horizon monitoring language: each role commits a bit,
the complete tuple is the next public signal, and private signals are unit.
`observed` is its canonical FOSG specialization. `serial` invokes the explicit
schedule serializer, adding one hidden commitment slot per role and a resolver.
No equilibrium, continuation recursion or compositional category is defined
by these wrappers.

`Rounds/Disclosure.hidden_prefix` proves equality of actual information views
for different hidden prefixes at every supplied public history. `serial_information`
connects that view to the accepted canonical information model. `public_step`
proves exact complete publication; `appendPublicHistory` constructs a canonical
realized continuation history with no strategy-reach hypothesis. Two-bit,
two-round regressions inspect first- and second-round prefixes. These are
operational/information results. Product Bayes beliefs, consistency and the
full strategic round correspondence remain unproved by this gate.


## Shared hardness-reduction interface

`Definitions/Reductions.lean` is the thirteenth definition module and remains
mathlib-only. `ResetUnion.Symbol` has exactly the two binary native operations;
its terms use the existing equational language, with independent winner-set
validity and the full binary language. `Code` specifies prefix terms and
complete equation framing. `Reductions.CNF` is a list of literal lists, with
independent existential Boolean satisfiability, including empty cases.
`Reductions.ResetUnion` constructs the report's actual tree equation from the
listed variable support plus a harmless dummy Boolean variable. This ensures a
nonempty consistency list and avoids loops on numeric name maxima. Its anchor
and literal names are explicit and disjoint. The proof modules `Reductions/ResetUnion*` establish exact CNF correctness and expanded linear size. `Complexity/ResetUnion*` certify the generator and finite-algebra countervaluation verifier, yielding full fixed-role coNP-completeness for the same native codec and full binary language. Malformed words are included; uniform-K complexity remains separate.


## Completed basis and congruence definitions

The independent owner definition module also contains the literal `Fin 40`
family `Owner.FiniteBasis.basisAxiom`, its theory, arbitrary-model laws and the
one-owner winner structure. `Owner/Basis` proves arbitrary-model normalization,
two-source absorption, full completeness and transport to winner sets. Forty
counts indexed equations; no unproved distinctness of all forty is asserted.

`Definitions/CoreBasis.lean` supplies the native core structures, Boolean
profiles and explicit exhaustion syntax used by the full grid proof. The
finite countermodels are actual algebras, with locality for arbitrary small
generator sets. `Core/NonfiniteBasis` excludes every bounded-variable basis,
even infinite, and every finite basis, for both the winner core and ambient
native algebra. Identity satisfaction and basis remain the independent shared
equational notions.

`Definitions/Congruences.lean` is the fourteenth definition module. It defines
ordinary/symmetric owned-choice congruences independently of the classification,
admissible closure/fixed-family conditions, and ambiguity thresholds. The proof
modules construct unique representations, classify the symmetric chain, count
actual quotients, and identify thresholds with mathlib uniform matroids,
including ground, independent sets, rank and closure. No bespoke matroid
predicate replaces the imported `Matroid` structure.

`Definitions/Dissemilattice.lean` is the fifteenth definition module. It gives
the two binary symbols, all seven syntax equations, arbitrary-model laws and
independent three-state operation tables. `Core/ChoiceUnion` proves full
seven-law generation/completeness directly. The two semilattice orders remain
distinct; only the stated meet-over-join distributivity is used. The actual
set of equations is proved to contain exactly seven members.


## Atomic classification, policies and two-player semantics

`Definitions/Atomic.lean` is the sixteenth definition module. Its repeat
relation, essentially-unary/two-output classes and atomic preservation/realization
refer directly to ordinary functions and the existing winner evaluator.
`Algebra/Atomic` proves the finite-product classification directly and constructs
actual realizing terms. Determinacy and the complete four-operation binary
classification use no external clone hypothesis. One-constant rigidity uses the
same core terms with a Boolean marker selecting varying versus fixed leaves.
General choice identities and inclusion lemmas live in `Algebra/Basic`.

`Definitions/Policies.lean` is the seventeenth module. It defines the labelled
reset/policy signature, actual set-blocking semantics, root/occurrence guards,
independent passing patterns and the exact chain-or-intersection/repetition
criterion. The syntax-only checker and normalized guard comparisons are
independently specified. Their correctness is proved for both tractable family
branches; repeated-pattern observations are equation-complete. Strict G
nondefinability uses actual reset syntax and the displayed two-owner expression.
Native non-easy family CNF reductions are now proved, including calibration and width-three expanded sizes; machine runtime/class transport remains required.

`Definitions/TwoPlayers.lean` is the eighteenth module. Any `Fin 2 ≃ Role`
identifies the existing nonempty winner sets with the ordinary `Fin 3` chain.
Max/min/reversal and Boolean forcing coordinates are proved, rather than imposed
as new winner operations. Reset and policy degeneration, full-language atomicity,
union nondefinability and semantic failure of idempotent core extraction are
checked. Finite Kleene-basis completeness is now implemented in the nineteenth definition module and its proofs below.

## General finite menus and native syntax output

The existing `Definitions/Rounds` now also specifies finite-menu trees, intrinsic
public prefixes, legal append, actual observed execution and the accepted explicit
serial implementation. Public and private information remain canonical GameTheory
interfaces. Finite histories, reachability, proper public subgames, recall,
serial decision recall and SE existence are proved; exact serial fibers contain
only earlier current commitments. `notes/integration/rounds.md` distinguishes
these foundations from the required Bayes/consistency/value bridge.

`Definitions/Encoding` additionally defines the reusable finite-signature prefix
codec: explicit finite operation alphabet, framed binary operation indices and
exact arities/children, including nullary and ternary symbols. The codec proofs
establish exact parsing, reconstruction and injectivity. Native constructors
reuse that original format; the complete original generic decoder and cached annotation fold now have native machine certificates. The `Equational.language` record is now a transparent `abbrev`, allowing
these dependent syntax interfaces to elaborate without representation changes.

`Complexity/OwnerRuntime` owns the backend encodings at the machine seam.
Input is a unary dimension together with original finite-table guard bitsets;
root and output positions are binary labels. The complete source checker is
certified uniformly in that dimension without a canonicality promise.
`OwnerSynthesisBridge.outputEncoding` injectively pairs the unary dimension with
the fully expanded generic original tree, relabeling finite positions by their
natural values. Its source theorem certifies the actual `GuardTable.synthesize`,
including rejection, all saturation frames, both finishing branches and every
output tree occurrence, for a fixed finite role alphabet.


## Complete two-player basis and public observation operations

`Definitions/Kleene.lean` is the nineteenth definition module. Its five-symbol
signature has bottom/top, join/meet and involution, with explicit fifteen-law
syntax and independent raw model laws. `Algebra/TwoPlayers/Kleene` proves signed
normal forms and arbitrary-model separation, full equational completeness, and
transport to the existing winner carrier. `ofPublic` translates every original
term, including constants and every internal permutation; evaluation commutes.
The main full-signature finite-basis assertion is complete. The unused separate
lattice-reduct assertions in its composite report proposition remain optional.

`Definitions/Views` now specifies `PlayerView.union/choice` directly by their
finite tables. `ViewOrders/Table` proves actual winner-view homomorphisms before
`Order` derives the quotient semilattices and all layer comparisons. No
representative choice or three-role embedding appears in the operations;
the local three-role premise supplies surjectivity for their order proofs.
`Algebra/Semilattice` uses mathlib's semilattice construction from the owned
choice laws and its standard nonempty finite fold. These small generic
constructions are documented semantic interfaces; the ordinary winner-set
inclusion order is kept explicit and distinct from the owner-top join order.

## Completed native one-owner boundary

`Owner/GuardEncoding` proves the exact outsider guard-list bridge and encoded
annotation bound for any finite numbering of the fixed Unit signature.
The original codec and complete generic cached tree-fold machine then produce
raw guards without depending on the ambient role set. `OwnerWordFrontend`
decodes the complete original binary equation, compares guards, and rejects
all malformed or trailing input. Its correctness interprets the same Unit
trees via `withOwner` in every role type containing three roles. This closes
the uniform-K original one-owner equality gate. Generic fold bounds charge
captured context, actual source trees, every annotation and binary name;
fixed finite operation numbering is not asserted uniform in a varying alphabet.

The source `Owner/Basis/TwoSource` also proves literal actual guard coverage
implies equational two-source absorption. Its premises/conclusion are genuine
`Equational.Derives` judgments and native `Covers`, with no external word-witness
certificate. The completed basis is used noncircularly after independently
proving the explicit two-new-source guard decomposition.

## Independent round values and product beliefs

The existing round definition module now defines `sequentialValues` by canonical
serial assessments, Kreps-Wilson consistency and sequential rationality, and
`observedValues` by canonical whole-policy Nash in every proper public subgame.
Both contain actual winner PMFs from canonical runners. The total winner
readout extends leaf labels; the terminal certificates ensure nonterminal
readouts are never scored. Indicator expected utility equals the corresponding
winner PMF coordinate. The independent stage `GameForm` and `roundOperator`
choose a continuation at every actual tuple and use its canonical mixed Nash
predicate; they do not define the equilibrium of a round tree by recursion.

`DecisionSites` and `InformationFibers` identify actual serial decision sites
and their complete history fibers. `PrefixLaw.currentLaw/prefixLaw` construct
ordinary independent scheduled probability products; `productBelief` maps them
to those actual fibers. These construction definitions live beside their small
probability proofs, while equilibrium definitions stay in `Definitions/Rounds`.
Exact canonical reach factorization and Bayes normalization imply unique
product beliefs in every consistent assessment, including zero-reach limits.
`Consistency` constructs consistent beliefs for every supplied strategy via
uniform trembles and imported assessment compactness. `TerminalErasure` proves
exact terminal source/serial law equality at every public boundary and profile.
`SerialRun` identifies actual finite prefix and terminal continuation laws under arbitrary whole-policy replacements. `Correspondence` proves canonical sequential rationality exactly equivalent to public whole-policy SPE, then equality of the independently defined SE/SPE value sets and the complete all-tuples round recursion. No reachability-of-equilibrium-play hypothesis is used.


## Native raw reductions and role-count identities

The existing `Definitions/Reductions` now also contains the two-binary-operation
raw syntax interpretation, actual CNF gates for all three hard raw pairs,
and the reset/union complete-graph identities. Names remain ordinary sparse
natural variables; there are no implicit certificate valuations. Actual native
tree sizes are charged after expansion. `Colouring.embedWinnerSet` is the
nonempty image along an injective role map, proved to preserve union/reset;
its native equation uses exactly root, marker and graph-vertex inputs.
The smaller-carrier validity and explicit next-carrier separation prove strict
inclusion of complete independently defined identity theories.

The round definition module also adds binary-menu sizes, literal public choice
and diagonal game constructors, reciprocal game trees, the threshold trees and
possible winners (`∃ p ∈ E, p i ≠ 0`). These are syntactic/probability definitions
without equilibrium assumptions. The scalar game proofs remain separate.


The shared fixed-finite-value numbering, lookup and witness construction is
now consolidated in `Complexity/FiniteValueWitness`, with the original binary
verifier namespace/API preserved. `FiniteSignatureVerifier` extends the same
charged native traversal to arbitrary finite arities and independent finite
interpretations/binary relations. `GuardedPairCompleteness` instantiates it for
native H-only equations and exact third-role observation. These are fixed-role
certificates; finite enumeration is not asserted uniform in K. Policy syntax's
`toPublic` proof interpretation uses the actual complete role dictionary and
finite selective folds, proves evaluation commutes and preserves core syntax,
then transfers the full pair-countervaluation theorem. That possibly large
proof translation is not executed by the policy verifier.


## Complete disclosed-round and scalar surface

`Definitions/Rounds` remains the single round-facing semantic definition file.
It now also collects the actual one-active-role public constructor, diagonal
constructor, reciprocal and threshold trees, the public-tree interpretation,
possible winners, independent `Context`/`fill` syntax, `UsesOnly` (only the
named pair has nontrivial menus or wins), and `BooleanMenus`. The actual menu
size parameter is one less than its nonempty cardinality. No role-count lower
bound is built into these definitions.

The same file contains `ScalarTerm` with leaves, diagonal, complement and
public extrema, its literal game interpretation, rational `rate`, and
`UnaryGenerated` (only leaves, complement and D(_,one)). The arithmetic formula
`Scalar.parallel`, actual PMF `Scalar.distribution`, reciprocal distribution,
ordinary probability `Public.segment`, and concrete `Public.nonconvexTree`
were consolidated there from their proof modules without changing their
names or bodies. Scalar rate correctness is an actual canonical SE theorem,
not the definition of the game or of its equilibrium values.

`Public/Menus` constructs the exact two owner actions and proves their marginal
law; `Stage` proves the exact mixed-Nash endpoint conditions; `Values` derives
the one-active-role mixture equation. `Support` connects public tree mixed
winners to independently defined pure full-profile SPE, and `Nonconvex`
calculates the concrete two-segment value set and omitted/attained midpoint.
`Scalar` proves diagonal payoff uniqueness, parallel laws, reciprocal games,
thresholds, rational synthesis and all-round-context full abstraction.
`closedContext`, `thresholdContext` and the synthesized comparison context are
literal syntax constructions; the general context congruence follows from the
proved actual SE round equation, including repeated holes.

`TwoPlayers/Stage` proves unique actual winner laws for any finite menu stage
with only two effective players/winners, by crossed Nash deviations. `Values`
extends this to all finite games satisfying `UsesOnly`, and proves every game
on `Fin 2` does so. `matrixAction` is the standard dependent Fin-two product
equivalence, identifying actual row/column menus. `Endpoints` derives the
all-winning-row/column criteria from actual mixed-Nash support. `Support`
uses actual nonempty child winner sets and literal `WinnerSet.choiceFold`
serializations to prove their union is the parent support and that support is
a congruence for all two-role round contexts. Its small `serialZero/serialOne`
helpers are exactly those displayed folds. The generic nonowner-atom fold
lemma belongs to the pure `Algebra/Semilattice` module.

The fixed-signature raw and policy machine theories have explicit independent
semantic equations and full word languages in `RawPairCompleteness` and
`PolicyCompleteness`. Every word-language theorem existentially decodes a
complete actual original equation and excludes malformed words. Native
3SAT/CNF transports are internal theorems; source width is checked before
expanded policy macros are executed. These fixed-signature results are not
asserted uniform in a varying alphabet. `Canonicalization` proves the generic
machine-level P=NP consequence with both canonicalization and an arbitrary
Boolean comparator charged; its original-core instantiation remains tracked.


The completed fixed-family policy frontend computes actual `normalGuards`,
including collision normalization, and performs all blocking/dominance/coverage
scans on their native encodings. Its proved annotation-byte bound is cubic in
the original input code, with a fixed-family constant for label widths. The
chain branch checks every observer; the intersection/repetition branch uses
the complete palette. `PolicyWordFrontend` decodes full original equations and
rejects malformed/trailing words. Root `policy_family_dichotomy` repeats both
the passing-pattern criterion and the complete original word language; it
asserts polynomiality for the positive criterion and coNP-completeness for
its complement, without assuming that these complexity classes differ.


The twentieth definition module, `Definitions/Circuits.lean`, gives the
independent graph model: a gate list with typed finite argument vectors,
strictly earlier references, two actual output indices, safe cached evaluation,
and validity requiring wellformedness and equal actual outputs. A failed parse
or evaluation is never interpreted as an identity. Proof-only unfolding connects
graph semantics to the existing term algebra; native machines evaluate the
original shared graph. The CNF graph program and concrete chain valuation live
in `Definitions/Reductions.lean`.

`Raw.Operation`, `Raw.Symbol selected`, `Raw.Valid` and `Raw.Language` in
`Definitions/Reductions.lean` specify an actually selected binary signature.
Its complete word language existentially encodes original terms and quantifies
over every winner-set valuation. Cardinality cases cover the empty signature,
each singleton operation and all four possible hard pairs. The polynomial
frontends scan sparse original labels or translate each reset node once.

`Owner.Valid` and `Owner.Language` in the same module restrict every H owner to
the selected finite family, then quantify over actual winner-set evaluations
and an explicit relation. The relation can be equality, membership implication
or membership equivalence. `Owner.Term.compileObservation` in
`Definitions/Owner.lean` replaces an observer-owned H by two resets, preserving
each source child once. All other H nodes are relabeled to Unit. Exact raw guard
preservation justifies reusing the certified one-owner guard frontend; semantic
completeness still requires at most one other owner. `jointObservationEquation`
and `jointObservationValuation` explicitly exhibit the two-owner observational
counterexample and its third-role separator on four inputs.

`FullTermCode` in `Definitions/Encoding.lean` uses an infinite-payload raw
signature for original full terms: binary winner/owner labels and explicit
forward permutation arrays. Binary K is stored once in the outer input. The
pure decoder checks bounds, exact array length and bijectivity. It never
constructs an exponential alphabet of permutations. The extraction algorithm
in `Algorithms/FullTermCode/Core` uses source annotations and stored arrays;
its native runtime bound charges actual original bytes, including malformed
words, and remains uniform for K=0,1,2 and larger K. The shared full/core
complexity languages separately restrict to K≥3 at their theorem boundary.


`FullHardness.originalTermEncoding K` is exactly `FullTermCode.encode (view term)`.
Its core restriction `originalCoreTermEncoding K` uses the existing subtype
`{term // term.IsCore}` with that same code, without adding a new term language
or changing any evaluator. `originalEquationEncoding K` is the fixed-K
instance of the uniform complete original equation word, including its binary
K header. These three small embeddings are proof-transport interfaces in
`Complexity/FullHardness.lean`, independently inspectable beside the codec
roundtrips. The canonicalizer statement permits any polynomial comparator
whose result agrees with actual semantic equivalence on this subtype.

Circuit word languages use `Circuit.Code.encode` in `Definitions/Encoding.lean`
and `Algorithms/CircuitCode.lean`: an original list of gate records, explicit
binary variable/reference labels and binary outputs. Operation arity is checked
against the exact stored reference list; topological wellformedness is checked
by actual safe cache evaluation. `Circuit.Code.Language` existentially encodes
the original graph and uses the independent `Equation.Holds`, requiring both
wellformedness and equal evaluated outputs for every valuation. Root Paper
repeats that complete language with the wellformedness/evaluation quantifiers.
The Fin-three multiplication table is `if j=0 then 0 else max i j` and is
proved to be the actual reset-chain generator, not an unchecked finite table.


The complete uniform complexity layer uses three independent languages on the
same `FullTermCode.EquationInput` and original equation encoding. `FullLanguage`
has no syntactic restriction, `PublicLanguage` requires `IsPublic` on both terms
(no renamings), and `CoreLanguage` requires `IsCore` (no winner constants or
renamings). All require K≥3 locally. `FullCounterVerifier` proves the polynomial
sparse-pair countercertificate checker and correctness under arbitrary padding;
`FullPublicReduction` provides the no-permutation filter; `FullCompleteness`
combines six fixed/uniform endpoints. No permutation alphabet or carrier is
enumerated in the uniform machine.

Native reset synthesis reuses the existing independently defined
`Algorithms.GuardDescriptor`, its canonical table, realizability checker and
primitive `Reset.Term` syntax. The pure helper `GuardDescriptor.recordTerm` in
`Reset/Realizability/Records` joins a path for every original raw record,
retaining duplicate records and unused dictionary slots. The native functions
`Complexity.ResetSynthesis.synthesize`, `synthesizeWord` and `synthesizeCode`
in `Complexity/ResetSynthesisMachine` construct the actual primitive tree,
validate the complete original word and emit its original prefix-tree bytes.
Their correctness is connected to independent root/table and winner semantics,
with `1+2*n*m` nodes for physical dictionary width n and raw record count m.
Root selection is the first genuine empty-prerequisite record and is proved
correct; it does not assume dictionary position zero is the root.


The [readable review index](paper-definition-surface.md) and machine-readable
[public-type dependency surface](paper-definition-surface.json)
records each of the 128 Paper theorem types, its reachable project definitions
and inductive constructors, and imported boundary interfaces. Its extractor
follows semantic/computational definition bodies and types, erases proof-valued
subterms under binders, and never follows theorem proof bodies. Source hashes
and per-theorem slices make the report reproducible; it supplements the manual
meaning/index above and the separate transitive axiom audit.
