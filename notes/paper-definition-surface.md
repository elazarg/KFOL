# Paper theorem-type definition surface

85 public theorem types reach 699 project semantic declarations in 42 source files. 30 of those files are under `KFOL/Definitions`. Generated declarations are grouped into 378 written source review units; 11 derived declarations have file-level locations. Theorem proof bodies are excluded.

This is a review index. Definitions still require human review against the manuscript; the separate proof/axiom and import audits remain necessary.

| Source | Reachable declarations | Central definitions |
| --- | ---: | --- |
| [Paper.lean](../Paper.lean) | 85 |  |
| [KFOL/Definitions/Owner.lean](../KFOL/Definitions/Owner.lean) | 75 | yes |
| [KFOL/Definitions/Rounds.lean](../KFOL/Definitions/Rounds.lean) | 65 | yes |
| [KFOL/Definitions/Encoding.lean](../KFOL/Definitions/Encoding.lean) | 48 | yes |
| [KFOL/Definitions/Equational.lean](../KFOL/Definitions/Equational.lean) | 48 | yes |
| [KFOL/Definitions/Reset.lean](../KFOL/Definitions/Reset.lean) | 43 | yes |
| [KFOL/Definitions/Complexity.lean](../KFOL/Definitions/Complexity.lean) | 41 | yes |
| [KFOL/Definitions/Reductions.lean](../KFOL/Definitions/Reductions.lean) | 37 | yes |
| [KFOL/Definitions/Quantified.lean](../KFOL/Definitions/Quantified.lean) | 36 | yes |
| [KFOL/Definitions/Strategic.lean](../KFOL/Definitions/Strategic.lean) | 33 | yes |
| [KFOL/Definitions/CoreNormalForm.lean](../KFOL/Definitions/CoreNormalForm.lean) | 31 | yes |
| [KFOL/Definitions/Circuits.lean](../KFOL/Definitions/Circuits.lean) | 23 | yes |
| [KFOL/Definitions/Kleene.lean](../KFOL/Definitions/Kleene.lean) | 21 | yes |
| [KFOL/Definitions/Public.lean](../KFOL/Definitions/Public.lean) | 19 | yes |
| [KFOL/Definitions/Dissemilattice.lean](../KFOL/Definitions/Dissemilattice.lean) | 18 | yes |
| [KFOL/Definitions/Policies.lean](../KFOL/Definitions/Policies.lean) | 18 | yes |
| [KFOL/Definitions/AtomicBasis.lean](../KFOL/Definitions/AtomicBasis.lean) | 17 | yes |
| [KFOL/Definitions/Core.lean](../KFOL/Definitions/Core.lean) | 17 | yes |
| [KFOL/Definitions/Views.lean](../KFOL/Definitions/Views.lean) | 17 | yes |
| [KFOL/Complexity/OwnerRuntime.lean](../KFOL/Complexity/OwnerRuntime.lean) | 12 |  |
| [KFOL/Definitions/Congruences.lean](../KFOL/Definitions/Congruences.lean) | 11 | yes |
| [KFOL/Definitions/CoreInterpolation.lean](../KFOL/Definitions/CoreInterpolation.lean) | 9 | yes |
| [KFOL/Definitions/PaperAlgebra.lean](../KFOL/Definitions/PaperAlgebra.lean) | 8 | yes |
| [KFOL/Definitions/PaperGames.lean](../KFOL/Definitions/PaperGames.lean) | 8 | yes |
| [KFOL/Complexity/OwnerTermMachines.lean](../KFOL/Complexity/OwnerTermMachines.lean) | 5 |  |
| [KFOL/Definitions/Atomic.lean](../KFOL/Definitions/Atomic.lean) | 5 | yes |
| [KFOL/Complexity/PolicyTermMachines.lean](../KFOL/Complexity/PolicyTermMachines.lean) | 4 |  |
| [KFOL/Definitions/CoreBasis.lean](../KFOL/Definitions/CoreBasis.lean) | 4 | yes |
| [KFOL/Complexity/GuardedPairMachines.lean](../KFOL/Complexity/GuardedPairMachines.lean) | 3 |  |
| [KFOL/Definitions/CoreFunctions.lean](../KFOL/Definitions/CoreFunctions.lean) | 3 | yes |
| [KFOL/Definitions/Counting.lean](../KFOL/Definitions/Counting.lean) | 3 | yes |
| [KFOL/Definitions/StrategicCounting.lean](../KFOL/Definitions/StrategicCounting.lean) | 3 | yes |
| [KFOL/Algebra/Semilattice.lean](../KFOL/Algebra/Semilattice.lean) | 2 |  |
| [KFOL/Complexity/CircuitGeneratorRecords.lean](../KFOL/Complexity/CircuitGeneratorRecords.lean) | 2 |  |
| [KFOL/Complexity/OwnerSynthesisBridge.lean](../KFOL/Complexity/OwnerSynthesisBridge.lean) | 2 |  |
| [KFOL/Definitions/TestDomains.lean](../KFOL/Definitions/TestDomains.lean) | 2 | yes |
| [KFOL/Algorithms/CircuitCode.lean](../KFOL/Algorithms/CircuitCode.lean) | 1 |  |
| [KFOL/Complexity/FiniteTermMachines.lean](../KFOL/Complexity/FiniteTermMachines.lean) | 1 |  |
| [KFOL/Complexity/OwnerSynthesisMachine.lean](../KFOL/Complexity/OwnerSynthesisMachine.lean) | 1 |  |
| [KFOL/Definitions/Algorithms.lean](../KFOL/Definitions/Algorithms.lean) | 1 | yes |
| [KFOL/Definitions/TwoPlayers.lean](../KFOL/Definitions/TwoPlayers.lean) | 1 | yes |
| [KFOL/Strategic/Adequacy.lean](../KFOL/Strategic/Adequacy.lean) | 1 |  |

External interfaces are recorded without unfolding them:

- ComplexityLib/Cslib interface: 11 boundary constants.
- GameTheory: 45 boundary constants.
- Lean/Std: 164 boundary constants.
- mathlib: 155 boundary constants.

Review per public theorem:

| Public theorem | Semantic declarations | Project modules |
| --- | ---: | ---: |
| [atomic_functions](../Paper.lean#L237) | 21 | 2 |
| [atomic_quotient_basis](../Paper.lean#L469) | 41 | 3 |
| [atomic_quotient_near_unanimity](../Paper.lean#L489) | 12 | 2 |
| [atomic_quotient_subvariety](../Paper.lean#L480) | 28 | 4 |
| [atomic_repeated_triples](../Paper.lean#L225) | 19 | 2 |
| [binary_atom_preserving_iff](../Paper.lean#L247) | 25 | 5 |
| [canonicalization_collapse](../Paper.lean#L584) | 51 | 6 |
| [choice_union_basis](../Paper.lean#L400) | 40 | 3 |
| [common_source](../Paper.lean#L216) | 25 | 2 |
| [congruence_classification](../Paper.lean#L127) | 11 | 2 |
| [core_extraction_polynomial](../Paper.lean#L619) | 55 | 6 |
| [core_guard_peeling](../Paper.lean#L426) | 65 | 5 |
| [core_no_finite_relation_basis](../Paper.lean#L448) | 23 | 3 |
| [core_nonfinite_basis](../Paper.lean#L458) | 31 | 2 |
| [core_not_finitely_related](../Paper.lean#L440) | 22 | 3 |
| [core_prime_guard_equality](../Paper.lean#L419) | 44 | 4 |
| [core_prime_guard_normal_form](../Paper.lean#L409) | 49 | 4 |
| [determinacy](../Paper.lean#L241) | 20 | 3 |
| [equational_complexity](../Paper.lean#L527) | 61 | 5 |
| [expanded_nonfinite_basis](../Paper.lean#L496) | 43 | 2 |
| [finite_depth_quantifier_reduction](../Paper.lean#L57) | 60 | 2 |
| [guarded_choice_example](../Paper.lean#L272) | 7 | 3 |
| [guarded_pair_complexity](../Paper.lean#L566) | 34 | 8 |
| [idempotent_elimination](../Paper.lean#L190) | 28 | 3 |
| [infinite_winner_algebra](../Paper.lean#L644) | 51 | 2 |
| [intrinsic_player_views](../Paper.lean#L196) | 29 | 3 |
| [joint_owner_observation_failure](../Paper.lean#L381) | 23 | 5 |
| [minimum_reduct_test_domain](../Paper.lean#L185) | 22 | 3 |
| [neutral_union](../Paper.lean#L70) | 4 | 1 |
| [no_atomic_if_then_else](../Paper.lean#L232) | 18 | 1 |
| [no_boolean_product](../Paper.lean#L82) | 4 | 1 |
| [one_constant_rigidity](../Paper.lean#L254) | 21 | 2 |
| [optimal_test_domain](../Paper.lean#L172) | 19 | 2 |
| [owned_choice_semilattices](../Paper.lean#L75) | 4 | 1 |
| [owner_count_dichotomy](../Paper.lean#L540) | 39 | 7 |
| [owner_definability](../Paper.lean#L266) | 7 | 3 |
| [owner_guard_completeness](../Paper.lean#L335) | 35 | 4 |
| [owner_minimum_generator](../Paper.lean#L353) | 44 | 5 |
| [owner_one_table](../Paper.lean#L346) | 36 | 5 |
| [owner_root_status](../Paper.lean#L329) | 22 | 4 |
| [owner_table_algorithms](../Paper.lean#L610) | 80 | 12 |
| [owner_table_synthesis](../Paper.lean#L363) | 45 | 4 |
| [owner_thirty_six_equation_basis](../Paper.lean#L371) | 42 | 4 |
| [pair_countervaluations](../Paper.lean#L166) | 19 | 2 |
| [player_view_orders](../Paper.lean#L104) | 19 | 3 |
| [player_views](../Paper.lean#L88) | 28 | 4 |
| [policy_family_dichotomy](../Paper.lean#L556) | 42 | 7 |
| [public_backward_induction](../Paper.lean#L25) | 29 | 3 |
| [public_forcing](../Paper.lean#L48) | 31 | 3 |
| [public_mixed_support](../Paper.lean#L639) | 75 | 5 |
| [public_optimal_realizability](../Paper.lean#L37) | 34 | 4 |
| [public_realizability](../Paper.lean#L33) | 26 | 3 |
| [public_subdirect_representation](../Paper.lean#L96) | 31 | 3 |
| [quantifier_fold](../Paper.lean#L52) | 51 | 2 |
| [raw_pair_dichotomy](../Paper.lean#L533) | 41 | 6 |
| [reduct_test_domains](../Paper.lean#L180) | 23 | 3 |
| [reset_antimatroids](../Paper.lean#L314) | 28 | 3 |
| [reset_basis](../Paper.lean#L309) | 33 | 4 |
| [reset_circuit_complexity](../Paper.lean#L571) | 53 | 8 |
| [reset_circuit_large_tables](../Paper.lean#L519) | 39 | 3 |
| [reset_definability](../Paper.lean#L261) | 23 | 3 |
| [reset_minimum_generator](../Paper.lean#L301) | 20 | 3 |
| [reset_selection](../Paper.lean#L279) | 22 | 3 |
| [reset_table_recognition_polynomial](../Paper.lean#L601) | 33 | 5 |
| [reset_table_semantic_definition](../Paper.lean#L285) | 26 | 4 |
| [reset_table_synthesis](../Paper.lean#L324) | 27 | 2 |
| [reset_table_synthesis_polynomial](../Paper.lean#L604) | 42 | 5 |
| [reset_tables_semantics](../Paper.lean#L293) | 26 | 4 |
| [role_count_identity_theories](../Paper.lean#L576) | 21 | 4 |
| [round_recursion](../Paper.lean#L631) | 42 | 2 |
| [semilattice_trace](../Paper.lean#L205) | 26 | 3 |
| [status_cell_provenance](../Paper.lean#L158) | 19 | 1 |
| [strict_two_owner_policy](../Paper.lean#L389) | 17 | 3 |
| [switching_observation](../Paper.lean#L121) | 18 | 1 |
| [symmetric_congruence_chain](../Paper.lean#L138) | 13 | 2 |
| [two_owner_selective](../Paper.lean#L394) | 40 | 7 |
| [two_player_degeneracies](../Paper.lean#L664) | 27 | 6 |
| [two_player_finite_basis](../Paper.lean#L672) | 43 | 3 |
| [two_player_identification](../Paper.lean#L656) | 6 | 2 |
| [two_player_round_contexts](../Paper.lean#L685) | 55 | 2 |
| [two_player_round_support](../Paper.lean#L677) | 49 | 4 |
| [uniform_equality_algorithms](../Paper.lean#L592) | 56 | 7 |
| [uniform_matroid_identification](../Paper.lean#L152) | 3 | 2 |
| [unique_winner_observations](../Paper.lean#L112) | 22 | 2 |
| [winner_budget](../Paper.lean#L43) | 21 | 2 |

The JSON contains every theorem's complete project slice, exact declaration/type/body edges, external interface types, declaration locations and source fingerprints.

Reproduce with `python3 scripts/export_definition_surface.py --check`.
