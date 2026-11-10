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
check in `KFOL/Audit/Dependencies.lean`. These are dependency gates. The paper-specific public-strategy and complete
observed-SPE/serial-SE correspondences have since been proved in KFOL, as
recorded below; they are not consequences of those import checks alone.

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

Paths below are relative to the pinned GameTheory checkout. Declaration names
are source-checked anchors. The KFOL bridges discharge their finite-menu,
termination, recall and expectation hypotheses explicitly.

| Need in the main paper | Existing API | Implemented fit and boundaries |
| --- | --- | --- |
| General deviations and equilibrium | `Core/Signature`, game forms, `Core/Utility`, canonical `IsNash` and `Profile.update` | Canonical strategic definitions are reused. KFOL public-tree restriction and whole-player replacement agree with the independently defined full-profile SPE predicate, preserving decisions at every occurrence. |
| Pure SPE and backward induction | `Protocol/SubgamePerfect`, `Protocol/Backward`, `Protocol/HistoryBackward`; `Languages/EFG/SubgamePerfect` | Public adequacy uses canonical `IsNash` at every actual subtree and proves both directions of the independent whole-plan SPE bridge. Hidden rounds use canonical behavioral subgame perfection at every proper public subgame; no hidden-game equivalence with historywise optimality is assumed. |
| Observation-local strategies | `Protocol/Information`, `Protocol/BehavioralAssessment` | KFOL source and serial policies use the information-local action menus. Intrinsic histories and actual serial decision fibers are identified with public prefixes plus earlier commitments. |
| Simultaneous rounds | `Languages/FOSG` | Actual finite nonempty menus, independent current decisions and fully public boundaries instantiate the source FOSG. KFOL proves its winner-law recursion and canonical mixed-SPE characterization. |
| Serial hidden commitments | `Languages/Bridges/FOSGToEFG`, `.../FOSGToEFGStrategic` | The accepted serializer supplies execution and root strategic transport. KFOL separately proves terminal-law erasure at every public history, the product posterior at every commitment site, and complete serial-SE/observed-SPE equivalence in `Rounds/Correspondence`. |
| Independent SE definition | `Analysis/Protocol/Sequential`; `Protocol/BehavioralAssessment`, `BehavioralBayes`, `BehavioralTerminal`; EFG adapter `Analysis/Protocol/EFG` | The actual `BehavioralAssessment.IsSequentialEquilibrium` predicate is used, including whole-policy terminal rationality and limits of fully mixed Bayes assessments. No recursive equilibrium predicate replaces it. |
| SE one-shot and localization arguments | `Analysis/Protocol/SequentialOneShot`, `InformationLocalization`, `SubgameLocalization`, `SequentialLimits` | KFOL proves off-path continuation selection, public reach-factor cancellation, product beliefs and arbitrary whole-policy deviation transport. These discharge the serial rationality bridge beyond the imported root Nash theorem. |
| Finite SE existence | `Analysis/Protocol/EFGExistence`: `Game.exists_isSequentialEquilibrium`; generic `Analysis/Protocol/SequentialExistence`: `InformationModel.exists_sequentialEquilibrium` | KFOL supplies finite histories, decision recall, total fallback policies and terminal well-foundedness. Imported general existence is instantiated, and the independently proved correspondence characterizes every equilibrium winner law. |
| Finite mixed Nash existence | `Analysis/Nash`: `GameTheory.exists_isNash_mixed` | The actual finite joint-menu stage and bounded winner-indicator payoffs discharge finite, nonempty and integrability hypotheses. Stage equilibria are used in the complete round recurrence and nonemptiness proofs. |
| Constant-sum values and scalar uniqueness | `Analysis/Minimax`: `exists_value`, `exists_isSaddlePoint`; `Core/ZeroSum`: Nash/security equivalences and `IsSaddlePoint.value_eq` | KFOL proves pair-supported winner-law uniqueness, endpoint characterizations and the diagonal formula using actual stage Nash inequalities. PMF and mixed-Nash foundations are reused; no minimax conclusion is left as an external theorem hypothesis. |
| Finite real simplexes and PMFs | `Math/Probability/Simplex`: `simplexWeights`, `PMF.ofSimplex`, `ofSimplex_toReal`, `ofSimplex_toReal_weights`; `Product`, `Expectation`, `UniformTremble`, `Convergence`, `ProductConditioning` | Ordinary `PMF` is the winner-law carrier. Product convergence and uniform tremble infrastructure support the actual Bayes/consistency proof, including zero-probability public histories. |
| Optional report-only dependent fragment observations | `Protocol/Information`, `Protocol/Knowledge`; `Epistemic/Knowledge` | Reuse information partitions, knowledge and canonical profile updates where their carrier assumptions fit. They do not define typed telescopes, stable cell identities, or the paper's legal-view strategy space. In particular, `S_i(P;W)` may have dependently typed answers and may be empty, while a protocol action carrier is fixed per player. Any adapter must handle this honestly. The semantic private-store connection theorem still requires a local construction. |

The reusable declarations can be inspected in the pinned [Nash module](https://github.com/elazarg/GameTheory/blob/6f1af625b77215dd9e4454e6120275dbd8b61f51/GameTheory/Analysis/Nash.lean), [SE definition](https://github.com/elazarg/GameTheory/blob/6f1af625b77215dd9e4454e6120275dbd8b61f51/GameTheory/Analysis/Protocol/Sequential.lean), [finite SE existence](https://github.com/elazarg/GameTheory/blob/6f1af625b77215dd9e4454e6120275dbd8b61f51/GameTheory/Analysis/Protocol/EFGExistence.lean), [serializer strategic bridge](https://github.com/elazarg/GameTheory/blob/6f1af625b77215dd9e4454e6120275dbd8b61f51/GameTheory/Languages/Bridges/FOSGToEFGStrategic.lean), and [simplex interface](https://github.com/elazarg/GameTheory/blob/6f1af625b77215dd9e4454e6120275dbd8b61f51/GameTheory/Math/Probability/Simplex.lean).

## Complexity libraries

Production uses the native successor predicate
`Turing.MultiTapeTM.ComputableInPolyTime` with explicit injective input/output
encodings. The facade is `KFOL/Complexity/Language.lean`. Native composition,
list folds and input-length-clocked iteration charge full encoded context,
state and output; these replace the earlier Cobham/FPn implementation.

Native machine certificates cover complete reset parsing, sparse support,
guard extraction/compression, descriptor normalization/recognition and original
binary-tree equality. Reset/union, the native raw-pair fragments, guarded-owner
reductions and fixed-policy-family reductions have actual original-word class
transports. One-owner recognition, synthesis and equality are certified; the
restricted one-owner checker is independent of the number of ambient roles.
The generic fixed-algebra verifiers have constants depending on that fixed
algebra, as their statements require.

The exact sparse-CNF reset DAG generator, original shared-graph word codec,
cached finite-algebra verifier and both complete reset DAG class endpoints
(winner sets and the actual three-element multiplication table) are certified.
Original explicit-array full/public/core lower bounds and the actual-core
canonicalizer/comparator collapse are complete. The uniform binary-K
full/public/core verifiers and all six fixed/uniform coNP-completeness
endpoints are production-certified. Full witnesses have proved exact framed
length at most `16*(originalWordBytes+1)^2`, including arbitrary padding and
malformed-word soundness. Native polynomial reset-table synthesis is also complete, with exact original primitive-tree bytes, root/table/node-size correctness and arbitrary-role winner semantics.
The main substitution formula is proved; encoded substitution runtime is
report-only. No complexity foundations are re-proved in KFOL.

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
hypothesis. The minimum reset and owner generators and the seven-law generation special case are also now proved directly. The atomic-clone/determinacy/binary classification is also now proved locally: finite rectangles and coordinate updates give necessity; explicit unary and Boolean term synthesis gives the converse. Finite Kleene-basis completeness and full original-syntax translation are also now proved directly.

## Supporting syntax libraries and the dependent claim

[`CSLib/Foundations/Syntax`](https://github.com/leanprover/cslib/tree/main/Cslib/Foundations/Syntax) contains interfaces for contexts, substitution, well-formedness, alpha equivalence and congruence. These may reduce boilerplate if the paper eventually needs a syntactic calculus; they do not supply a dependent-data normalization/conservativity theorem by themselves. The current [`CSLib language directory`](https://github.com/leanprover/cslib/tree/main/Cslib/Languages) includes lambda calculus and process calculi, not a demonstrated implementation of this paper's dependent disclosure language.

[`Lean4Lean`](https://github.com/digama0/lean4lean/blob/master/README.md) has formal typing/metatheory and a verified checker, but its README explicitly distinguishes executable checker targets from proof targets. Lean's full kernel theory is a larger and different calculus than the small interface required here. It should not become a prerequisite merely to instantiate scripts with semantic dependent families.

The scoped main paper no longer asserts `dep:thm:connection`. Its semantic typed-store, strategy-factorization and sealing proof is report-only, so no adapter or dependent-data calculus is needed for the current formalization target. The library observations above are references for a possible future extension, not required integration work.

## Historical open games and real quantifier elimination

The main paper's related-work paragraph asserts failed unit and associativity laws and cites an already checked historical artifact. Retain the immutable `v1-final` revision `02898a2d8b918f9b106a683420ca78c99867560e`; the current GameTheory rewrite is a different API and does not automatically contain its historical modules. The isolated historical target has been rebuilt and its five theorem closures
audited; `notes/integration/open-game-v1.json` records the exact sources and
`scripts/check_external_open_game.py` reproduces the check. The full convex-repair and incomparable-bracketing development need not be ported into KFOL merely to re-establish that sentence. Never install the refuted composition as a category.

Real quantifier elimination and the general semialgebraicity claim belong to report results not needed for the main-paper round theorem or scalar full abstraction. Exclude them from the required dependency graph. For a later extension, [MathComp real-closed](https://github.com/math-comp/real-closed/blob/master/index.md) supplies an existing Rocq/Coq QE proof, not a Lean import. No compatible completed Lean QE dependency was established here, and none is needed to complete the selected target.

## Integration gates and current boundary

All five original gates have passed on Lean 4.35.0:

1. Authorized dependency resolution, selected imports and transitive axiom checks.
2. Complete public-tree full-profile/SPE bridge, including unreached decisions.
3. Actual finite-menu source and serial histories, information fibers, terminal
   erasure, off-path product beliefs, consistency, and full SE/SPE correspondence.
4. Exact original reset/union CNF generation and pinned machine-level 3SAT
   transport, including the complete binary target language's malformed words.
5. The shared mathlib equational interface and native frontend syntax choice,
   with full original-syntax evaluation/support/substitution bridges.

The round gate was completed with the original SE-based definition retained.
`Rounds/Observed` proves the mixed-SPE recurrence independently;
`Rounds/SerialRun` and `Rounds/Correspondence` connect every actual public
history and whole-policy deviation to the canonical serial SE predicate.
Specific diagonal, reciprocal and threshold games, public nonconvexity, scalar
rational synthesis/full abstraction, and arbitrary-menu two-player support
follow from those semantic bridges. No refuted mixed-open-game category law
enters this implementation.

The antimatroid representation is proved in `KFOL/Reset/Antimatroid` from
mathlib finite sets and lists, with both constructions and inverse laws and
actual winner-set term functions. Compact table realizability, executable
recognition/synthesis, the main substitution formula, and raw/canonical
extraction-size bounds are checked. Encoded recognition and original-tree
comparison and actual descriptor-to-primitive-tree synthesis have native
polynomial-time certificates. Report-only encoded substitution runtime
does not block main-paper completion.

The other required pure branches are proved locally: uniform core
nonfinite-basis countermodels and local covers, congruence/threshold and
uniform-matroid identification, the seven-equation choice/union basis,
atomic-clone/determinacy/binary classification, one-owner thirty-six-law
completeness with its four-variable lower bound, and the two-role Kleene
identification and finite basis. Their cited literature is attribution and a
proof reference, not a theorem assumption in the Lean statements.

All required paper-facing mathematical and runtime endpoints are now
complete and recorded in the live claim inventory. The dependent/private-store
fragment, unrelated report results, numerical free-algebra enumeration and general real quantifier
elimination remain optional; no completion claim depends on moving a retained
main assertion out of scope.
