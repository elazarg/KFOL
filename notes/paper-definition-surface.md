# Paper theorem-type definition surface

81 public theorem types reach 676 project semantic declarations in 40 source files. 28 of those files are under `KFOL/Definitions`. Generated declarations are grouped into 360 written source review units; 11 derived declarations have file-level locations. Theorem proof bodies are excluded.

This is a review index. Definitions still require human review against the manuscript; the separate proof/axiom and import audits remain necessary.

| Source | Reachable declarations | Central definitions |
| --- | ---: | --- |
| [Paper.lean](../Paper.lean) | 81 |  |
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
| [KFOL/Complexity/GuardedPairMachines.lean](../KFOL/Complexity/GuardedPairMachines.lean) | 3 |  |
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
| [KFOL/Definitions/CoreFunctions.lean](../KFOL/Definitions/CoreFunctions.lean) | 1 | yes |
| [KFOL/Definitions/TwoPlayers.lean](../KFOL/Definitions/TwoPlayers.lean) | 1 | yes |
| [KFOL/Strategic/Adequacy.lean](../KFOL/Strategic/Adequacy.lean) | 1 |  |

External interfaces are recorded without unfolding them:

- ComplexityLib/Cslib interface: 11 boundary constants.
- GameTheory: 45 boundary constants.
- Lean/Std: 161 boundary constants.
- mathlib: 154 boundary constants.

Review per public theorem:

| Public theorem | Semantic declarations | Project modules |
| --- | ---: | ---: |
| [atomic_functions](../Paper.lean#L236) | 21 | 2 |
| [atomic_repeated_triples](../Paper.lean#L224) | 19 | 2 |
| [binary_atom_preserving_iff](../Paper.lean#L246) | 25 | 5 |
| [canonicalization_collapse](../Paper.lean#L545) | 51 | 6 |
| [choice_union_basis](../Paper.lean#L399) | 40 | 3 |
| [common_source](../Paper.lean#L215) | 25 | 2 |
| [congruence_classification](../Paper.lean#L126) | 11 | 2 |
| [core_extraction_polynomial](../Paper.lean#L580) | 55 | 6 |
| [core_five_local_obstruction](../Paper.lean#L439) | 22 | 3 |
| [core_guard_peeling](../Paper.lean#L425) | 65 | 5 |
| [core_nonfinite_basis](../Paper.lean#L446) | 31 | 2 |
| [core_prime_guard_equality](../Paper.lean#L418) | 44 | 4 |
| [core_prime_guard_normal_form](../Paper.lean#L408) | 49 | 4 |
| [determinacy](../Paper.lean#L240) | 20 | 3 |
| [equational_complexity](../Paper.lean#L488) | 61 | 5 |
| [expanded_nonfinite_basis](../Paper.lean#L457) | 43 | 2 |
| [finite_depth_quantifier_reduction](../Paper.lean#L56) | 60 | 2 |
| [guarded_choice_example](../Paper.lean#L271) | 7 | 3 |
| [guarded_pair_complexity](../Paper.lean#L527) | 34 | 8 |
| [idempotent_elimination](../Paper.lean#L189) | 28 | 3 |
| [infinite_winner_algebra](../Paper.lean#L605) | 51 | 2 |
| [intrinsic_player_views](../Paper.lean#L195) | 29 | 3 |
| [joint_owner_observation_failure](../Paper.lean#L380) | 23 | 5 |
| [minimum_reduct_test_domain](../Paper.lean#L184) | 22 | 3 |
| [neutral_union](../Paper.lean#L69) | 4 | 1 |
| [no_atomic_if_then_else](../Paper.lean#L231) | 18 | 1 |
| [no_boolean_product](../Paper.lean#L81) | 4 | 1 |
| [one_constant_rigidity](../Paper.lean#L253) | 21 | 2 |
| [optimal_test_domain](../Paper.lean#L171) | 19 | 2 |
| [owned_choice_semilattices](../Paper.lean#L74) | 4 | 1 |
| [owner_count_dichotomy](../Paper.lean#L501) | 39 | 7 |
| [owner_definability](../Paper.lean#L265) | 7 | 3 |
| [owner_guard_completeness](../Paper.lean#L334) | 35 | 4 |
| [owner_minimum_generator](../Paper.lean#L352) | 44 | 5 |
| [owner_one_table](../Paper.lean#L345) | 36 | 5 |
| [owner_root_status](../Paper.lean#L328) | 22 | 4 |
| [owner_table_algorithms](../Paper.lean#L571) | 80 | 12 |
| [owner_table_synthesis](../Paper.lean#L362) | 45 | 4 |
| [owner_thirty_six_equation_basis](../Paper.lean#L370) | 42 | 4 |
| [pair_countervaluations](../Paper.lean#L165) | 19 | 2 |
| [player_view_orders](../Paper.lean#L103) | 19 | 3 |
| [player_views](../Paper.lean#L87) | 28 | 4 |
| [policy_family_dichotomy](../Paper.lean#L517) | 42 | 7 |
| [public_backward_induction](../Paper.lean#L24) | 29 | 3 |
| [public_forcing](../Paper.lean#L47) | 31 | 3 |
| [public_mixed_support](../Paper.lean#L600) | 75 | 5 |
| [public_optimal_realizability](../Paper.lean#L36) | 34 | 4 |
| [public_realizability](../Paper.lean#L32) | 26 | 3 |
| [public_subdirect_representation](../Paper.lean#L95) | 31 | 3 |
| [quantifier_fold](../Paper.lean#L51) | 51 | 2 |
| [raw_pair_dichotomy](../Paper.lean#L494) | 41 | 6 |
| [reduct_test_domains](../Paper.lean#L179) | 23 | 3 |
| [reset_antimatroids](../Paper.lean#L313) | 28 | 3 |
| [reset_basis](../Paper.lean#L308) | 33 | 4 |
| [reset_circuit_complexity](../Paper.lean#L532) | 53 | 8 |
| [reset_circuit_large_tables](../Paper.lean#L480) | 39 | 3 |
| [reset_definability](../Paper.lean#L260) | 23 | 3 |
| [reset_minimum_generator](../Paper.lean#L300) | 20 | 3 |
| [reset_selection](../Paper.lean#L278) | 22 | 3 |
| [reset_table_recognition_polynomial](../Paper.lean#L562) | 33 | 5 |
| [reset_table_semantic_definition](../Paper.lean#L284) | 26 | 4 |
| [reset_table_synthesis](../Paper.lean#L323) | 27 | 2 |
| [reset_table_synthesis_polynomial](../Paper.lean#L565) | 42 | 5 |
| [reset_tables_semantics](../Paper.lean#L292) | 26 | 4 |
| [role_count_identity_theories](../Paper.lean#L537) | 21 | 4 |
| [round_recursion](../Paper.lean#L592) | 42 | 2 |
| [semilattice_trace](../Paper.lean#L204) | 26 | 3 |
| [status_cell_provenance](../Paper.lean#L157) | 19 | 1 |
| [strict_two_owner_policy](../Paper.lean#L388) | 17 | 3 |
| [switching_observation](../Paper.lean#L120) | 18 | 1 |
| [symmetric_congruence_chain](../Paper.lean#L137) | 13 | 2 |
| [two_owner_selective](../Paper.lean#L393) | 40 | 7 |
| [two_player_degeneracies](../Paper.lean#L625) | 27 | 6 |
| [two_player_finite_basis](../Paper.lean#L633) | 43 | 3 |
| [two_player_identification](../Paper.lean#L617) | 6 | 2 |
| [two_player_round_contexts](../Paper.lean#L646) | 55 | 2 |
| [two_player_round_support](../Paper.lean#L638) | 49 | 4 |
| [uniform_equality_algorithms](../Paper.lean#L553) | 56 | 7 |
| [uniform_matroid_identification](../Paper.lean#L151) | 3 | 2 |
| [unique_winner_observations](../Paper.lean#L111) | 22 | 2 |
| [winner_budget](../Paper.lean#L42) | 21 | 2 |

The JSON contains every theorem's complete project slice, exact declaration/type/body edges, external interface types, declaration locations and source fingerprints.

Reproduce with `python3 scripts/export_definition_surface.py --check`.
