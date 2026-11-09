# Supporting libraries for the main paper formalization

The foundation is the user's **GameTheory library plus mathlib**, with its intended updated ComplexityLib integration for computational claims. The current extension's machine API is now validated on KFOL's v4.35.0 toolchain for a first primitive; the successor and strategic integration gates remain separate. Mixed Nash existence, minimax, independent sequential equilibrium, finite SE existence, and machine-based complexity foundations have existing implementations. The remaining work is predominantly the paper's algebra and the bridges from its syntax to those implementations.

The target is the entire **main paper and its necessary report dependencies**. General real quantifier elimination, the semantic/syntactic dependent-calculus development, and the full ambiguity appendix are not prerequisites. The main-paper scope edit `6dff3f0` removed the private-store connection claim and the two numerical free-algebra lists. A pointer to an appendix does not import every theorem in that appendix into the target; substantive mathematical assertions made in the main text still count.

This assessment is not a fresh GameTheory integration build certification. The independent KFOL algebra has been built and audited on v4.35.0. A separate downstream gate now also builds the currently pinned ComplexityLib Cobham/FPn interface on that release, without dependency source patches, and checks its standard axiom list. KFOL uses that compatible pin for its first prerequisite-subset machine certificate. The successor integration and GameTheory strategic/analytic gates remain separate; no build, dependency update, or source edit was performed in the sibling GameTheory checkout.

## Pins and package boundaries

The inspected sibling GameTheory revision is `c6650cd861d4a05a64adb2e4fd99a4feafa231b0`. It selects Lean `v4.35.0`, mathlib `v4.35.0` (resolved revision `56a005855ea17e0b0958f73ec801ae140b0a1679`), and the fixed-point package `elazarg/fixed-point-theorems-lean4` at `f06449c5fb1ca49f14ea2b5331ddf71bd2dcd232`.

Its optional `extensions/complexity` package pins ComplexityLib at `257ad90ec5f547894cc20f27bd828839b1bf7bbf` and CSLib at `94ea80f41a5678fce997a004f0d8d12dbe47cc4b`. That package's published base GameTheory pin is `c7cd6bed7498b9a16edb22262e9522ceff90648c`, which differs from the sibling checkout. Its documented local path override selects the sibling version, but this combination still needs a downstream integration build.

KFOL now directly pins the current extension's ComplexityLib and CSLib revisions, overriding their inherited mathlib snapshot with v4.35.0. This validates that API for the first machine component; it does not settle the intended successor migration. The pure word definitions are independent, and `KFOL.Complexity.Language` confines the imported interface. GameTheory's analysis imports remain confined to the planned round branch. No full GameTheory or complexity umbrella is imported to obtain the primitive.

GameTheory itself stays out of the pure algebraic import closure. `Definitions/Public.lean` contains shared syntax and winner-set evaluation using mathlib; `Definitions/Strategic.lean` imports it and provides the GameTheory interpretation. Views, reset, guards, identities and nonfinite basability depend on the former only. Adequacy connects algebraic evaluation to SPE in the strategic branch. Complexity proofs can import the pinned ComplexityLib directly and reuse GameTheoryComplexity's implementation ideas without importing that companion's game modules. The [plan](formalization-plan.md) specifies independent build targets and transitive import checks. A single Lake package still resolves its declared dependencies; a separate algebra package is needed only if avoiding even GameTheory downloads or the shared toolchain becomes a requirement.

The former ComplexityLib upstream URL now redirects to [`SamuelSchlesinger/complexitylib-v1`](https://github.com/SamuelSchlesinger/complexitylib-v1). Its successor is [`cslib-community/complexitylib`](https://github.com/cslib-community/complexitylib), whose toolchain at inspection was [Lean 4.36.0-rc2](https://github.com/cslib-community/complexitylib/blob/main/lean-toolchain). Follow GameTheory's planned update to that successor, then verify the selected source-level APIs and pins. The legacy theorem names below establish prior availability of the foundations; they are not promises that the successor preserves those names.

## GameTheory fit

Paths below are relative to `../GameTheory/`. Declaration names are source-checked anchors; final public declarations must still discharge their exact premises.

| Need in the main paper | Existing API | Fit and KFOL work remaining |
| --- | --- | --- |
| General deviations and equilibrium | `Core/Signature`, game forms, `Core/Utility`, canonical `IsNash` and `Profile.update` | Reuse the canonical strategic definitions. Compile KFOL syntax; prove pure profiles, entire-player replacements, terminal winners, and utilities agree with the existing Std development. Preserve decisions at all occurrences. |
| Pure SPE and backward induction | `Protocol/SubgamePerfect`, `Protocol/Backward`, `Protocol/HistoryBackward`; `Languages/EFG/SubgamePerfect` | `IsSubgamePerfect` compares whole plans at information-set-closed subgame roots. `IsHistorywiseOptimal` is a stronger separate predicate. Under KFOL public perfect information prove every subtree root is a proper subgame and establish the exact equivalence to the paper's SPE. Instantiate well-foundedness and the one-shot theorem's `ActsOnceWhereItMatters` and expectation hypotheses; do not conflate historywise optimality with SPE in hidden games. |
| Observation-local strategies | `Protocol/Information`, `Protocol/BehavioralAssessment` | Policy arguments are information states, and menus are information-local with an adequacy proof. Reuse this enforcement rather than functions on hidden state plus an informal promise. Prove KFOL's visibility model produces the stated information sets. |
| Simultaneous rounds | `Languages/FOSG` | A suitable execution/information target. Encode finite menus and fully public boundaries as a restricted FOSG model with independent current decisions and winner outcomes. No general FOSG equilibrium theorem by itself proves the round recursion. |
| Serial hidden commitments | `Languages/Bridges/FOSGToEFG`, `.../FOSGToEFGStrategic` | Serializes one hidden choice slot per player followed by a resolver. `isNash_serialized_iff_source` preserves whole-profile behavioral Nash and law erasure. KFOL must show the resolver/full-publication boundary agrees with the paper, prove corresponding subgame structure, and separately prove the SPE/SE correspondence. The serializer does **not** currently export that correspondence. |
| Independent SE definition | `Analysis/Protocol/Sequential`; `Protocol/BehavioralAssessment`, `BehavioralBayes`, `BehavioralTerminal`; EFG adapter `Analysis/Protocol/EFG` | `BehavioralAssessment.IsSequentialEquilibrium` combines whole-policy terminal rationality with `IsSequentiallyConsistent`, a pointwise limit of fully mixed Bayes assessments. This is the intended independent definition; specialize it instead of introducing another SE predicate. Prove finite-coordinate convergence matches the paper's finite-game convention. |
| SE one-shot and localization arguments | `Analysis/Protocol/SequentialOneShot`, `InformationLocalization`, `SubgameLocalization`, `SequentialLimits` | Useful proof infrastructure for restriction/pasting. Still prove the restricted round structure, off-path continuation choices, cancellation of public reach factors, and product beliefs at commitment sites. A Nash transport theorem cannot replace these obligations. |
| Finite SE existence | `Analysis/Protocol/EFGExistence`: `Game.exists_isSequentialEquilibrium`; generic `Analysis/Protocol/SequentialExistence`: `InformationModel.exists_sequentialEquilibrium` | Finite histories, decision recall, total fallback policies, finite players and terminal well-foundedness suffice. A finite KFOL round tree with nonempty menus can supply these. No new general existence proof is needed. Existence is useful, but does not characterize the set of all equilibrium winner laws. |
| Finite mixed Nash existence | `Analysis/Nash`: `GameTheory.exists_isNash_mixed` | Has finite player and strategy assumptions, nonempty strategy carriers, and `HasIntegrableUtility`. The finite joint-action stage with bounded winner payoffs supplies them. Avoid accidental integrability assumptions in the public theorem; prove them from finiteness. |
| Constant-sum values and scalar uniqueness | `Analysis/Minimax`: `exists_value`, `exists_isSaddlePoint`; `Core/ZeroSum`: Nash/security equivalences and `IsSaddlePoint.value_eq` | Reuse after an explicit payoff shift from constant sum one to zero sum and an active-player restriction to `Fin 2`. Prove inactive roles have no strategic effect, and preserve all equilibrium winner coordinates. KFOL's diagonal formula and constructor laws remain paper-specific. |
| Finite real simplexes and PMFs | `Math/Probability/Simplex`: `simplexWeights`, `PMF.ofSimplex`, `ofSimplex_toReal`, `ofSimplex_toReal_weights`; `Product`, `Expectation`, `UniformTremble`, `Convergence`, `ProductConditioning` | Prefer ordinary `PMF` as the semantic probability carrier. Use the existing simplex equivalence for coordinate inequalities and topology. This removes a new competing probability representation. Product and tremble lemmas help with the off-path belief proof but do not complete it by themselves. |
| Optional report-only dependent fragment observations | `Protocol/Information`, `Protocol/Knowledge`; `Epistemic/Knowledge` | Reuse information partitions, knowledge and canonical profile updates where their carrier assumptions fit. They do not define typed telescopes, stable cell identities, or the paper's legal-view strategy space. In particular, `S_i(P;W)` may have dependently typed answers and may be empty, while a protocol action carrier is fixed per player. Any adapter must handle this honestly. The semantic private-store connection theorem still requires a local construction. |

The reusable declarations can be inspected in the pinned [Nash module](https://github.com/elazarg/GameTheory/blob/c6650cd861d4a05a64adb2e4fd99a4feafa231b0/GameTheory/Analysis/Nash.lean), [SE definition](https://github.com/elazarg/GameTheory/blob/c6650cd861d4a05a64adb2e4fd99a4feafa231b0/GameTheory/Analysis/Protocol/Sequential.lean), [finite SE existence](https://github.com/elazarg/GameTheory/blob/c6650cd861d4a05a64adb2e4fd99a4feafa231b0/GameTheory/Analysis/Protocol/EFGExistence.lean), [serializer strategic bridge](https://github.com/elazarg/GameTheory/blob/c6650cd861d4a05a64adb2e4fd99a4feafa231b0/GameTheory/Languages/Bridges/FOSGToEFGStrategic.lean), and [simplex interface](https://github.com/elazarg/GameTheory/blob/c6650cd861d4a05a64adb2e4fd99a4feafa231b0/GameTheory/Math/Probability/Simplex.lean).

## Complexity libraries

The pinned legacy ComplexityLib already contains the foundations the first plan proposed as potentially new work:

- `Complexitylib.Classes.NP`, `Classes.NP.Reduction`, `Classes.NP.CoNP`: machine-based NP/coNP, polynomial many-one reductions, `coNPComplete`, reduction transport and complement duality.
- [`SAT.CookLevin.Assembly`](https://github.com/SamuelSchlesinger/complexitylib-v1/blob/257ad90ec5f547894cc20f27bd828839b1bf7bbf/Complexitylib/SAT/CookLevin/Assembly.lean): `SAT.NPHard_language`, `SAT.NPComplete_language` and an actual polynomial-time reduction machine.
- [`SAT.ThreeSAT.Completeness`](https://github.com/SamuelSchlesinger/complexitylib-v1/blob/257ad90ec5f547894cc20f27bd828839b1bf7bbf/Complexitylib/SAT/ThreeSAT/Completeness.lean): `ThreeSAT.NPComplete_language` and the CNF-to-3CNF reduction.
- [`Classes.NP.CoNP`](https://github.com/SamuelSchlesinger/complexitylib-v1/blob/257ad90ec5f547894cc20f27bd828839b1bf7bbf/Complexitylib/Classes/NP/CoNP.lean): `NPComplete.compl`, `coNPComplete.transfer`, and closure of polynomial reductions under complement.

Use these definitions and theorems, with a narrow KFOL complexity facade. GameTheoryComplexity provides examples of exact serialization, malformed-input handling and verified polynomial machines. Its constrained-Nash NP-completeness result is not a reduction to KFOL identities and should not be cited as proving their hardness.

The new work is to implement each KFOL reduction as an actual polynomial-time map, connect it to the semantic guard certificates, encode countervaluations for NP membership of inequivalence, and prove the checkers' machine bounds. Syntax size alone does not prove runtime. The pair theorem supplies short witnesses even when K is input, but role-label/permutation costs, malformed encodings and native tree/DAG differences must be included.

The 3SAT complement includes malformed words as members. A reduction whose mathematical theorem is only for well-formed 3CNFs needs a constant valid-equation fallback on malformed inputs, or a proved equivalence to a well-formed UNSAT language. Otherwise the many-one reduction can have the wrong truth value on invalid codes.

This supports retaining full coNP-completeness in the definition of done. Proving only reduction correctness and sizes is a useful intermediate deliverable, not a completed main-paper complexity theorem. No need to rebuild Cook–Levin locally.

## Algebraic supporting libraries

**Mathlib is the main reusable algebraic substrate.** Its relation-free [`FirstOrder.Language`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/ModelTheory/Basic.html), [`Term` syntax](https://leanprover-community.github.io/mathlib4_docs/Mathlib/ModelTheory/Syntax.html), [`Substructure`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/ModelTheory/Substructures.html), and [quotient](https://leanprover-community.github.io/mathlib4_docs/Mathlib/ModelTheory/Quotients.html) APIs cover much of the structural machinery. Finite sets, permutations, closure operators, finite orders, products and quotient types are useful independently of the syntax choice.

**The Equational Theories Project has an existing completeness proof, with a signature mismatch.** Its [`Completeness.lean`](https://github.com/teorth/equational_theories/blob/main/equational_theories/Completeness.lean) contains `Soundness`, `Completeness`, a free term quotient, and a universal property. Inspection of [`FreeMagma.lean`](https://github.com/teorth/equational_theories/blob/main/equational_theories/FreeMagma.lean) shows a single binary magma operation. This is a strong proof reference for reset's binary signature and for a generalization, but it is not immediately a many-operation, ternary-operation and permutation-signature library. Its inspected toolchain is Lean 4.29.1, also different from GameTheory's.

Implementation: `KFOL/Equational` now proves generic soundness and completeness
for arbitrary finitary operation signatures using mathlib's own terms and
quotient operations. The Equational Theories Project remains a proof reference;
no code or permanent dependency is imported, and operation labels are not
encoded as algebra elements. Production full/core codecs connect this interface
to the retained native traversals. HSP preservation and support-based
subalgebra locality are also checked; reverse HSP representation is not claimed. A direct reset completeness proof through tables is still needed: generic equational completeness alone does not establish that six particular equations generate the theory.

**Lean UALib is a proof reference, not a compatible dependency.** The inspected [`UniversalAlgebra/lean-ualib` package](https://github.com/UniversalAlgebra/lean-ualib/blob/master/leanpkg.toml) targets Lean 3.4.1. The maintained [Agda Universal Algebra Library](https://agda-algebras.universalalgebra.org/) has signatures, varieties and HSP proofs in Agda. Either can inform a Lean proof, but neither gives an importable Lean 4 theorem.

No ready-to-import Lean proof of the exact antimatroid representation, repeat-triple clone classification, Freese order-algebra basis/minimum-generator results, or Harding–Romanowska generation theorem was identified in the inspected sources and targeted searches. This is a search outcome, not a nonexistence claim. The reset six-law special case is now implemented in `KFOL/Reset/Basis` by
arbitrary-algebra path normalization and suffix absorption, followed by the
shared equational completeness theorem. Freese et al.'s introduction and
Section 3 are the proof reference; their basis theorem is not an imported
hypothesis. Continue direct proofs of the remaining special cases used by the
main paper, using representation and normalization where practical.

## Supporting syntax libraries and the dependent claim

[`CSLib/Foundations/Syntax`](https://github.com/leanprover/cslib/tree/main/Cslib/Foundations/Syntax) contains interfaces for contexts, substitution, well-formedness, alpha equivalence and congruence. These may reduce boilerplate if the paper eventually needs a syntactic calculus; they do not supply a dependent-data normalization/conservativity theorem by themselves. The current [`CSLib language directory`](https://github.com/leanprover/cslib/tree/main/Cslib/Languages) includes lambda calculus and process calculi, not a demonstrated implementation of this paper's dependent disclosure language.

[`Lean4Lean`](https://github.com/digama0/lean4lean/blob/master/README.md) has formal typing/metatheory and a verified checker, but its README explicitly distinguishes executable checker targets from proof targets. Lean's full kernel theory is a larger and different calculus than the small interface required here. It should not become a prerequisite merely to instantiate scripts with semantic dependent families.

The scoped main paper no longer asserts `dep:thm:connection`. Its semantic typed-store, strategy-factorization and sealing proof is report-only, so no adapter or dependent-data calculus is needed for the current formalization target. The library observations above are references for a possible future extension, not required integration work.

## Historical open games and real quantifier elimination

The main paper's related-work paragraph asserts failed unit and associativity laws and cites an already checked historical artifact. Retain the immutable `v1-final` revision `02898a2d8b918f9b106a683420ca78c99867560e`; the current GameTheory rewrite is a different API and does not automatically contain its historical modules. A separate pinned proof target can check the needed failure theorems. The full convex-repair and incomparable-bracketing development need not be ported into KFOL merely to re-establish that sentence. Never install the refuted composition as a category.

Real quantifier elimination and the general semialgebraicity claim belong to report results not needed for the main-paper round theorem or scalar full abstraction. Exclude them from the required dependency graph. For a later extension, [MathComp real-closed](https://github.com/math-comp/real-closed/blob/master/index.md) supplies an existing Rocq/Coq QE proof, not a Lean import. No compatible completed Lean QE dependency was established here, and none is needed to complete the selected target.

## Revised integration gates

The [plan's mathlib-only pair-countervaluation delivery milestone](formalization-plan.md) is complete on v4.35.0. The following dependency gates come afterward.

1. In an isolated downstream workspace, resolve the updated GameTheory, fixed-point, mathlib and ComplexityLib pins on their mutually compatible toolchain. Reconcile successor complexity APIs, compile narrow imports and inspect transitive axioms. Do not change the sibling repositories.
2. Compile a public binary game with an unreached decision; prove its full-profile/SPE bridge and winner recurrence. This tests whether the strategic integration preserves the paper's semantics.
3. Compile a single sealed two-bit round and its serializer; verify information sets, outcome-law erasure, finite histories and decision recall. Prove the local product-belief and consistency bridge, then test a two-round game with an unreachable public history to exercise off-path cancellation and pasting. Existing root Nash transfer alone does not pass this gate.
4. Implement one reset/union reduction on the pinned 3SAT codec, including malformed words and a polynomial-time certificate. Reuse `NPComplete.compl` and transfer to the same encoded KFOL equation language. Record the reusable machine components separately from fragment-specific work, then assess policy-family and DAG reductions before extrapolating the total cost or number of machines.
5. Use the native-versus-mathlib syntax decision already made in the first algebra milestone. Reopen it only if a concrete strategic or complexity consumer exposes a defect; do not repeat the comparison routinely.

The current-pin Cobham/FPn subgate has passed in isolation and in the production
package, with only `propext`, `Classical.choice` and `Quot.sound`. The actual
width-independent prerequisite-subset program is connected to finite-set
inclusion and the existing guard-enabling predicate. This is a reusable machine
component, not completion of Gate 1's successor/GameTheory integration or
Gate 4's end-to-end reduction. Compact support indexing and exact framed
binary record/dictionary codecs are now also checked. They reuse mathlib's
list-indexing equivalence and ComplexityLib's existing codecs and block parser.
The native binary input-tree codec and executable extraction frontend now also
have exact semantics and bit-size bounds: a single framed output recovers the
actual raw guards, with size quadratic in original input bits. Whole descriptor
validation, shared-support identity inputs, and machine certificates for the
parser and record/table scans remain the next work.

These gates test the actual reuse seams. Once they pass, the remaining effort can be estimated from the paper-specific proof obligations, rather than from rebuilding foundations already available in the user's libraries.

The [plan's editorial proposals](formalization-plan.md) distinguish this current target from possible manuscript changes. Moving the serial-SE correspondence or a discussion-level report claim out of the main text would change the required dependency graph; no such edit is assumed by this library assessment.

The main antimatroid representation is now proved in `KFOL/Reset/Antimatroid`
using mathlib finite sets and lists. The model uses the finite feasible-family
axioms directly, proves both constructions and inverse laws, and identifies
actual winner-set term functions through the existing selector/chain interface.
It imports no external representation theorem. Compact table realizability,
executable recognition and synthesis, and raw/canonical extraction-size bounds
are now also checked. Their full encoded machine-time statements remain partial.
