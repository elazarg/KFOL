# Supporting libraries for the main paper formalization

The current dependency selection uses the user-authorized GameTheory branch
`port/cslib-complexity`, pinned at `6f1af625b77215dd9e4454e6120275dbd8b61f51`.
Its successor ComplexityLib pin is `054834a4a4e6ac3ec50ed770bacea7fc42eccc7d`,
CSLib is `254e30e6d4299c51323aaeaf5f51a4763b375d4a`, and Lean/mathlib remain
4.35.0 (`56a005855ea17e0b0958f73ec801ae140b0a1679`). The fixed-point package
remains `f06449c5fb1ca49f14ea2b5331ddf71bd2dcd232`.

The selected native machine and GameTheory protocol gate passed 3266 jobs in an
isolated downstream package. Production imports of canonical SPE, Nash,
minimax and finite SE existence passed 3803 jobs and the explicit standard-axiom
check in `KFOL/Audit/Dependencies.lean`. These are dependency gates; compiling the
interfaces does not prove the KFOL strategy or round correspondences.

GameTheory is resolved by the root package but excluded from the pure algebra
and binary frontend import closure. The machine branch imports successor
ComplexityLib directly. The paper word language now has its own mathlib-only
codec, retaining the previously proved exact serialization across the backend
change. Paper pairing has length `2*left.length+2+right.length`; native `encPair`
has length `2*left.length+1+right.length`. The two are never identified.

The target is the main paper and necessary report dependencies. The private-store
connection, dependent calculus, numerical free-algebra lists and general real
quantifier elimination remain outside required scope. No sibling repository was
modified; the earlier v1 pin and API observations are retained in delivery history.

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

Production uses the native successor predicate
`Turing.MultiTapeTM.ComputableInPolyTime` with explicit injective input/output
encodings. The facade is `KFOL/Complexity/Language.lean`. Native composition,
list folds and input-length-clocked iteration charge full encoded context,
state and output; these replace the earlier Cobham/FPn implementation.

Current certified consumers are `GuardSubset`, `Framing`, `BlockScan`,
`Dictionary` and `DescriptorValidation`. The last theorem certifies the actual
dependent descriptor decoder under its existing injective paper encoding.
Malformed-input validation followed by copying the original exact code realizes
that decoder; it assumes no caller certificate or decoded-value clock.

The remaining computational work is complete record normalization/equality,
recognition, synthesis/substitution, encoded countervaluation verifiers and
hardness reductions. Use the successor library's machine-based P/NP/coNP and
reduction APIs; no complexity foundations are re-proved in KFOL. Check the exact
source problem codec and malformed-word convention when assembling the first
3SAT reduction, rather than transporting only well-formed formula correctness.
The first complete reset/union reduction and coNP transport gate remains open.

## Algebraic supporting libraries

**Mathlib is the main reusable algebraic substrate.** Its relation-free [`FirstOrder.Language`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/ModelTheory/Basic.html), [`Term` syntax](https://leanprover-community.github.io/mathlib4_docs/Mathlib/ModelTheory/Syntax.html), [`Substructure`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/ModelTheory/Substructures.html), and [quotient](https://leanprover-community.github.io/mathlib4_docs/Mathlib/ModelTheory/Quotients.html) APIs cover much of the structural machinery. Finite sets, permutations, closure operators, finite orders, products and quotient types are useful independently of the syntax choice.

**The Equational Theories Project has an existing completeness proof, with a signature mismatch.** Its [`Completeness.lean`](https://github.com/teorth/equational_theories/blob/main/equational_theories/Completeness.lean) contains `Soundness`, `Completeness`, a free term quotient, and a universal property. Inspection of [`FreeMagma.lean`](https://github.com/teorth/equational_theories/blob/main/equational_theories/FreeMagma.lean) shows a single binary magma operation. This is a strong proof reference for reset's binary signature and for a generalization, but it is not immediately a many-operation, ternary-operation and permutation-signature library. Its inspected toolchain is Lean 4.29.1, also different from GameTheory's.

Implementation: `KFOL/Equational` now proves generic soundness and completeness
for arbitrary finitary operation signatures using mathlib's own terms and
quotient operations. The Equational Theories Project remains a proof reference;
no code or permanent dependency is imported, and operation labels are not
encoded as algebra elements. Production full/core codecs connect this interface
to the retained native traversals. HSP preservation and support-based
subalgebra locality are also checked; reverse HSP representation is not claimed. The six-law reset completeness proof is now implemented in KFOL/Reset/Basis; generic completeness is its final logical bridge.

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

The successor selected-closure and production native-machine/analytic import
gates are complete at the pins above. The KFOL public-SPE, sealed-round and
end-to-end reduction gates remain. Exact reset binary semantics, normalization
and shared-support identity checking are already connected; complete parser,
dictionary and descriptor-validation machines are now certified as well.

These gates test the actual reuse seams. Once they pass, the remaining effort can be estimated from the paper-specific proof obligations, rather than from rebuilding foundations already available in the user's libraries.

The [plan's editorial proposals](formalization-plan.md) distinguish this current target from possible manuscript changes. Moving the serial-SE correspondence or a discussion-level report claim out of the main text would change the required dependency graph; no such edit is assumed by this library assessment.

The main antimatroid representation is now proved in `KFOL/Reset/Antimatroid`
using mathlib finite sets and lists. The model uses the finite feasible-family
axioms directly, proves both constructions and inverse laws, and identifies
actual winner-set term functions through the existing selector/chain interface.
It imports no external representation theorem. Compact table realizability,
executable recognition and synthesis, and raw/canonical extraction-size bounds
are now also checked. Their full encoded machine-time statements remain partial.
