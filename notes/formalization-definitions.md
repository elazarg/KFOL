# Definitions and representation boundaries

Read [Paper.lean](../Paper.lean) with the vocabulary below. It contains 75
mathematical statements and no definitions. [Report.lean](../Report.lean)
contains 44 further mathematical statements. Their proofs name library theorems;
definitions must still be reviewed independently against the manuscripts.

The [audit guide](audit-guide.md) gives the reading order. The generated
[Paper definition surface](paper-definition-surface.md) and
[Report definition surface](report-definition-surface.md), with JSON graphs
beside them, identify every project definition reached from the respective
theorem types. They erase proof-valued subterms and never follow theorem proofs.

| Entry point | Theorem types | Semantic declarations | Source files | Central definition files | Written review units |
| --- | ---: | ---: | ---: | ---: | ---: |
| Paper | 75 | 629 | 35 | 23 | 329 |
| Report | 44 | 530 | 28 | 17 | 227 |

These counts are separate slices and overlap. The vocabulary files organize
the presentation; they do not replace their underlying mathematical definitions.

## Winner algebras

Start with [PaperAlgebra.lean](../KFOL/Definitions/PaperAlgebra.lean). It adds
seven ordinary mathematical predicates/functions, rather than abbreviations
for whole theorem statements:

| Name | Meaning |
| --- | --- |
| `Term.Equivalent s t` | Equality under every independent winner-set valuation |
| `Term.Idempotent t` | Every constant diagonal input is fixed |
| `WinnerSet.ObservationallyEquivalent k A B` | All public unary polynomial contexts agree on k's possible victory |
| `Reset.Term.Equivalent Role s t` | Equality of reset operations on this role carrier |
| `Owner.Term.Equivalent s t` | Equality of guarded-owner operations |
| `PlayerView.Below r p q` | The explicit layered player-view order for owner r |
| `Reset.markerValuation three j A` | The distinguished input receives the top of the three-chain, other requested ambiguous inputs its middle, and all remaining inputs its atom |

The underlying definitions are grouped by subject:

| Module under `KFOL/Definitions` | Mathematical surface to inspect |
| --- | --- |
| `Public` | Nonempty winner sets, singleton/union/owned choice, role renaming, full term syntax/evaluation/substitution |
| `Core` | Winner and input occurrences, accumulated permutations, public/core fragments, finite support and syntax size |
| `Views` | Player-view states, observations and induced owned operations |
| `TestDomains` | Completeness of a test domain over every finite arity |
| `Atomic` | Atomic preservation/realization and the repeat-triple relation |
| `Reset` | Reset syntax, rightmost root, selection, minimal guard tables, rooted antimatroids and table realizability |
| `Owner` | Guarded-owner syntax, root/status, guards, coverage, the independent four-state algebra, literal 36-equation action presentation, its five-variable exchange replacement and six-element obstruction to four-variable axiomatization |
| `Policies` | Indexed policies, passing patterns, selective reset, native syntax and the chain/intersection/repetition criterion |
| `Congruences` | Operation-compatible equivalence relations, admissible closure families and ambiguity thresholds |
| `Equational` | Identities, satisfaction, derivation, bases, variable bounds and generated varieties |
| `CoreBasis` | The finite padded-grid algebras and native core interpretation used for nonfinite basability |
| `Dissemilattice` | The seven explicit choice/union laws and their independent algebra structure |
| `TwoPlayers`, `Kleene` | The three-element two-role carrier, switch, Kleene signature and literal finite basis |

`WinnerSet Role` is a nonempty `Set Role`, without a built-in K≥3 assumption.
Owned choice returns the owner's atom if an operand is that atom, and otherwise
takes union. It tests equality with the atom, not membership of the owner.
Repeated variables have equal winner values but denote independent game copies.

Each owner has a different semilattice order. The proofs select the desired
`choiceSemilattice` explicitly; they do not identify it with ordinary subset
inclusion or install competing global instances.

Guard tables are defined from actual selection and minimality. The semantic
marker theorem connects them to winner observations. Coverage, canonicality
and realizability are specified independently of the algorithms deciding them.
The four-state owner algebra and finite countermodels have their own operations;
they are not defined by satisfaction of the theorem they certify.

Equational satisfaction universally quantifies over valuations. Derivability
has independent inference rules. `Equational.IsBasis` asserts that the two
notions coincide; its definition does not make completeness automatic.
Basis cardinalities concern the actual expanded equation families.

## Public games and arbitrary-domain quantifiers

[Strategic.lean](../KFOL/Definitions/Strategic.lean) defines finite binary public
trees, full profiles, winners, whole-player deviations, subtree restrictions and
SPE. Nash means no player can turn a loss into its own victory by replacing all
of its decisions. SPE imposes this in every subtree, including unreached ones.
The backward-induction recurrence is proved afterward.

`Strategic.value` in [Adequacy.lean](../KFOL/Strategic/Adequacy.lean) bundles the
actual SPE winner set after nonemptiness has been proved. The strategic-form
bridge reuses GameTheory's Nash definition. Compilation substitutes complete
trees at occurrences, without a shared-strategy condition for repeated inputs.

[Quantified.lean](../KFOL/Definitions/Quantified.lean) is the corresponding
arbitrary-branching public model:

| Name | Meaning |
| --- | --- |
| `QuantifiedTree` | A well-founded public tree with a nonempty action type at every decision; later types may depend on history |
| `Profile`, `Deviation`, `IsNash`, `IsSubgamePerfect` | Complete contingent profiles and whole-player Nash optimality at every subgame, independently of any algebraic recurrence |
| `DepthLE n G` | A uniform bound of n decisions along every play |
| `Prunes bound G G'` | Retain the original owner and a nonempty finite subset of at most bound original actions at each retained node |
| `Prunes.PreservesValues` | Each retained subgame has the same actual SPE winners as its matched original subgame |
| `BinaryFold` | A binary tree assembled from a list of children, with every helper node owned by the given owner |
| `Compiles G' B` | Recursively compile every retained child exactly once, using a duplicate-free exhaustive action list and that owner's binary fold |

`Prunes` is structural. `Compiles` contains no semantic equality premise.
Thus the binary representation in Paper is certified as an actual fold, rather
than merely an unrelated tree with the same winners. The regression rejects a
wrong-owner compilation even when its SPE winner set agrees.

The K−1 support theorem uses finite K≥2. Supports are chosen from original
continuation values and may vary with history. The inherited depth bound is
for the pruned quantified tree; binary folding may insert extra decision levels.
The library also proves the construction for all well-founded trees.

## Sealed rounds

Start with [PaperGames.lean](../KFOL/Definitions/PaperGames.lean), then
[Rounds.lean](../KFOL/Definitions/Rounds.lean):

| Name | Meaning |
| --- | --- |
| `Rounds.Game.value G` | E(G), the actual behavioral sequential-equilibrium winner laws of the serial implementation |
| `playerOrder` | A fixed enumeration of the finite role set, used only to select a serialization schedule |
| `HasScalarValue G a b x` | G has the unique law x δ_a + (1−x) δ_b with x in [0,1] |
| `ContextuallyEquivalent k G H` | Every round context agrees on k's possible victory |
| `SameContextualWinners G H` | Every round context gives equal complete possible-winner sets |
| `midpointLaw` | The actual half-and-half probability mixture |
| `WinnerSummary` | A carrier, encoding of Boolean-menu games, a public-choice operation, and an adequate possible-win observation |
| `matrixAction`, `serialZero`, `serialOne` | The two-player joint action and the two literal public owned-choice folds |

The value definition uses `sequentialValues`, not the observed-game recursion.
It quantifies actual GameTheory behavioral assessments: sequential rationality
and consistency as a limit of completely mixed strategies. The equality with
observed mixed SPE and independence of serialization order are theorems.

`roundOperator` independently selects an equilibrium continuation law at every
joint action and an independent mixed Nash equilibrium of the resulting finite
stage. Zero-probability actions retain their continuation selections.

`UsesOnly a b` restricts both effective actors and terminal winners.
`BooleanMenus` is purely syntactic. `WinnerSummary` has an encoding domain of
only Boolean games, so the impossibility theorem assumes no extension to other
games. Its composition and observation laws describe a candidate semantics;
its definition contains no impossibility assertion.

## Decision problems and representations

[Complexity.lean](../KFOL/Definitions/Complexity.lean) contains natural semantic
languages and input/output relations. A language is never defined by a checker's
acceptance. `encodedLanguage code valid` means that the word is the exact code
of an original instance satisfying the independently specified predicate.
The code is an embedding, so distinct instances have distinct words. Malformed
words have no witness.

| Names | Surface to inspect |
| --- | --- |
| `PublicSignature`, `Admissible`, `fullEquations` | C, A and A^sym, their syntax restrictions and universal equation validity |
| `fullEquationEncoding`, `uniformFullLanguage`, `termCode` | Original tree words, binary K, binary names and explicit role-permutation arrays |
| `rawLanguage`, `ownerLanguage`, `policyLanguage` | Validity/observational problems for the indicated original signatures |
| `resetLanguage`, `oneOwnerLanguage` | Fixed-format equality problems whose same checkers work for every ambient role carrier |
| `resetTableLanguage`, `ResetSynthesis` | Semantic table realizability and exact original encoded-tree synthesis, including output-size bounds |
| `OwnerTableRealizable`, `OwnerSynthesisOutput` | Independent canonicality, rooted one-owner realization and primitive output-size bounds |
| `CoreExtractionOutput` | Equivalent core output with no larger constructor count and the original binary-K encoding |
| `resetCircuitLanguage`, `resetChainCircuitLanguage` | Actual shared-graph evaluation on winner sets or the fixed three-element algebra |

`PolynomialTime` is the unchanged native
`Turing.MultiTapeTM.ComputableInPolyTime` class. P and coNP-completeness use
ComplexityLib/Cslib's independent machine definitions and reductions. The
uniform checker claims quantify one pair of programs before the ambient role
carrier; they do not enumerate a carrier of binary-encoded size K.

`Encoding`, `Algorithms`, `Reductions` and `Circuits` supply the underlying
word formats and original syntax. Descriptor lists and bitsets are representation
details, retained below the façade. Duplicate records and unused dictionary
positions are charged at their actual input sizes. Typed owner-table inputs
carry their explicit unary position dimension; this is part of their encoding.
A size bound on a mathematical term alone is not a native polynomial-time proof.

## Report navigation queries

[Queries.lean](../KFOL/Definitions/Queries.lean) defines a fragment of two-way
Core XPath independently of winner evaluation: paths denote binary relations,
tests denote node predicates, and composition/filtering have their ordinary
meanings. The canonical document has one role node per role and an input mark
below it exactly for membership in that input. Correctness and equivalence are
relative to this schema, including nonempty inputs.

`nonOwner` compiles a linear Boolean existence test; `compile` uses parent
navigation to evaluate that test at the common root. The compiler is defined
only on public terms, with the `IsPublic` proof excluding internal switches.
Its output has quadratic constructor size. `relation` is a separate regular
representation for a fixed owner on `Option Role`; it must not be confused
with the document's child axis. These definitions import neither GameTheory
nor machine complexity, and are included in the pure import audit.

[Relational.lean](../KFOL/Definitions/Relational.lean) defines the zero
extension on all subsets and the general right regular relation. Empty operands
annihilate; nonempty operands use the original independently defined choice.
The fresh point records membership in the represented set; an ordinary row
records right multiplication by that set. No associativity, distributivity or
representation law is built into these definitions. The finite powerset theorem
proves representation for any associative, union-preserving product with zero;
owned choice also satisfies the atomic expansion needed for infinite role types.

## Nonfinite bases with constants and permutations

The actual signatures are `Equational.CoreSymbol` (owned choices),
`PublicSymbol` (choices and winner constants) and `FullSymbol` (also internal
role permutations). Their independent winner structures are in
[Equational.lean](../KFOL/Definitions/Equational.lean).

[Envelope.lean](../KFOL/Definitions/Envelope.lean) defines
`Option (Equiv.Perm Role × M)`. Every winner denotes `none`, which absorbs
all owned choices. In a copy labelled g, owner r uses the payload's owner
`g⁻¹ r`; mixing labels gives `none`. A role permutation acts by left
multiplication on the labels and fixes `none`. These definitions assume no
identity, variety membership or finite-basis conclusion. The root Report
statement proves that the envelope belongs to each expanded variety exactly
when its payload belongs to the core variety, and states its exact size.

The Paper statement uses independently defined actual variable support,
semantic variety membership and equational derivability. Its finite witnesses
satisfy every identity within each requested support bound and fail a genuine
identity; it has no residual-bound or classification hypothesis. Purity,
shadow evaluation and the transfer proof are library lemmas.

## Preservation and verification

[Results/Certificates.lean](../KFOL/Results/Certificates.lean) retains every one
of the former 140 complete contracts, including codecs, intermediate invariants
and native machines. [audit-relocations.json](audit-relocations.json) records
original signatures; the surface checker verifies the pinned corpus. No weaker
façade statement replaces or removes those library results.

Every root file has one failing namespace axiom audit. The separate whole-source
`KFOL/Audit` checks authored library declarations and private helpers. The pure
algebra audit excludes GameTheory and ComplexityLib. Neither audit proves that
the definitions match the manuscript; that is the human review above.

Regenerate both definition indexes with:

```sh
python3 scripts/export_definition_surface.py
python3 scripts/export_definition_surface.py --entrypoint Report
```

The earlier detailed implementation notes remain in repository history at
revision `51e9725`; the current proof and representation contracts are in the
single production library.
