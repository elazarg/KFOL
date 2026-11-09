# Congruence classifications and exact symmetric quotient sizes

## Completed claims and public statements

The closure/kernel and fixed-family classification of view:thm:congruences is
complete. The symmetric threshold classification, exact K congruence count,
chain order, endpoints, and all quotient cardinalities in view:thm:sym are
complete. Full proposed Paper propositions are compiled as
`KFOLTest.Congruences.congruence_classification` and
`KFOLTest.Congruences.symmetric_congruence_chain` in `tests/Congruences.lean`.
They repeat their entire claims, including every converse direction.

The common hypotheses are `{Role : Type u} [Finite Role] [Nonempty Role]` and
`three : Fin 3 ↪ Role`. The Nonempty instance is logically supplied by the
embedding and can be introduced locally as `⟨three 0⟩` in Paper. No chosen
Fintype or decidable role equality is required by the final public results.

Anchors:

- `Congruences/Classification.lean`: `Congruence.equivAtomClosures` and
  `Congruence.exists_unique_closure`.
- `Congruences/Families.lean`: `Congruence.equivFamilies`,
  `Congruence.equivFamilies_rel_iff`, `Congruence.exists_unique_family`.
- `Congruences/SymmetricClassification.lean`:
  `SymmetricCongruence.exists_unique_threshold`, `equivThresholds`, `card`;
  `threshold_kernel_antitone`, `threshold_zero`, `threshold_last`.
- `Congruences/Quotients.lean`: `thresholdQuotientEquiv` and
  `card_thresholdQuotient`. The latter uses Nat.card of the actual Setoid
  quotient and the exact sum `1 + sum j in Icc 1 m, (Nat.card Role).choose j`.
  It holds for every 0<=m<K, including the universal one-point quotient.

## Definitions and proof architecture

The compact independent semantic file `Definitions/Congruences.lean` defines
WinnerSet.Congruence by extending mathlib Setoid with all owned-choice
compatibility, SymmetricCongruence by additional compatibility with every
internal permutation, the singleton closure condition, admissible fixed
families, the explicit intersection formula, and threshold functions.
Constants impose no additional congruence condition beyond reflexivity.

The proofs use mathlib ClosureOperator, the inherited subset partial order on
nonempty winner sets, finite-poset maximal members, ambient permutations
extended from equivalences of finite subsets, standard Setoid quotient
bijections, and powersetCard cardinalities. There is no custom category layer.

`Basic` proves union compatibility from the actual three-owner derived term,
the singleton-collapse-to-full law, and an actual greatest member of every
finite class. `Closure` constructs the class-maximum ClosureOperator and
proves that every closure satisfying the owner condition has an actual
operation-compatible kernel. `Classification` proves both inverse laws.
`Families` proves the full arbitrary-intersection fixed-family equivalence
and the paper's intersection-of-supersets closure formula.

`Symmetry` proves that the class-maximum closure commutes with permutations.
A swap of two roles outside a set shows that any extra point in its closure
forces the whole full set; finite ambient permutations then make all smaller
cardinalities closed. `Thresholds` proves the full invariant-closure
classification and establishes that each threshold is itself an admissible
invariant closure. `SymmetricClassification` proves unique threshold ranks,
the actual equivalence with Fin K, and the chain/endpoints.

`Quotients` gives an actual bijection from the entire threshold quotient to
Option of the small nonempty winner sets. It then gives an actual finite
representative family and partitions it exhaustively by subset cardinality;
mathlib's card_powersetCard supplies each binomial coefficient. These are
proved counts, not unchecked computations or native_decide certificates.

## Validation and integration

- `lake build KFOL.Congruences` passes (1013 jobs) on Lean/mathlib4.35.
- `lake env lean -DwarningAsError=true tests/Congruences.lean` passes.
- Concrete regressions prove 3 and 4 symmetric congruences for K=3 and K=4,
  and actual quotient cardinalities 4, 7 and 11 for the selected thresholds.
- Both complete proposed Paper statements report exactly propext,
  Classical.choice and Quot.sound.
- A temporary import-all transitive axiom audit covers all 179 authored
  declarations in Congruences and Definitions/Congruences, including helpers,
  and rejects GameTheory, complexity, rounds and strategy imports. It passes.

The coordinator owns Paper, inventory and full/pure audits; add all eight
Congruences proof modules, the root aggregate, and Definitions/Congruences to
the appropriate audit imports and declaration index. No sibling repository,
root manifest, manuscript or shared audit was modified here.

The report's separate ordinary congruence-count prose18/626 has not been
enumerated. It is not used by the completed classifications or symmetric
quotient-size proofs. The uniform-matroid comparison is completed below.

## Uniform-matroid clause completed

`Congruences/UniformMatroid.lean` now closes the cited identification too.
`KFOL.uniformMatroid rank` is an actual mathlib Matroid constructed using
IndepMatroid.ofFinite, with cardinal augmentation proved explicitly. Its
independent sets are exactly I.ncard<=rank; when rank<=K its bases have exactly
that size and its actual eRank is rank. At rank m+1 its Matroid.closure is
S↦if S.ncard<=m then S else univ, including empty inputs. The WinnerSet
threshold is proved to be its literal restriction to nonempty inputs.

`WinnerSet.uniform_matroid_identification` states the full existential
Matroid proposition with ground, independence, rank and restricted closure.
The complete proposed clause is repeated in
`tests/CongruencesUniformMatroid.lean`. Its strict regression proves rank3,
the fixed-pair/full-triple boundary on four roles, and empty closure at rank1.
The dedicated live module build passes1035 jobs. The transitive import-all
axiom and pure-boundary audit now passes202 authored declarations; the new
complete statement reports only the standard three axioms. Add this ninth
proof module to the full/pure audit imports as well.

This supersedes the earlier uniform-matroid limitation above. The separate
ordinary congruence-count prose18/626 remains optional and unenumerated.
