# Paper theorem-type definition surface

78 public theorem types reach 635 project semantic declarations in 35 source files. 23 of those files are under `KFOL/Definitions`. Generated declarations are grouped into 333 written source review units; 7 derived declarations have file-level locations. Theorem proof bodies are excluded.

This is a review index. Definitions still require human review against the manuscript; the separate proof/axiom and import audits remain necessary.

| Source | Reachable declarations | Central definitions |
| --- | ---: | --- |
| [KFOL/Definitions/Rounds.lean](../KFOL/Definitions/Rounds.lean) | 87 | yes |
| [Paper.lean](../Paper.lean) | 78 |  |
| [KFOL/Definitions/Owner.lean](../KFOL/Definitions/Owner.lean) | 73 | yes |
| [KFOL/Definitions/Encoding.lean](../KFOL/Definitions/Encoding.lean) | 48 | yes |
| [KFOL/Definitions/Reset.lean](../KFOL/Definitions/Reset.lean) | 43 | yes |
| [KFOL/Definitions/Complexity.lean](../KFOL/Definitions/Complexity.lean) | 41 | yes |
| [KFOL/Definitions/Reductions.lean](../KFOL/Definitions/Reductions.lean) | 37 | yes |
| [KFOL/Definitions/Quantified.lean](../KFOL/Definitions/Quantified.lean) | 36 | yes |
| [KFOL/Definitions/Strategic.lean](../KFOL/Definitions/Strategic.lean) | 33 | yes |
| [KFOL/Definitions/Equational.lean](../KFOL/Definitions/Equational.lean) | 31 | yes |
| [KFOL/Definitions/Circuits.lean](../KFOL/Definitions/Circuits.lean) | 23 | yes |
| [KFOL/Definitions/Kleene.lean](../KFOL/Definitions/Kleene.lean) | 21 | yes |
| [KFOL/Definitions/Public.lean](../KFOL/Definitions/Public.lean) | 19 | yes |
| [KFOL/Definitions/Dissemilattice.lean](../KFOL/Definitions/Dissemilattice.lean) | 18 | yes |
| [KFOL/Definitions/Policies.lean](../KFOL/Definitions/Policies.lean) | 18 | yes |
| [KFOL/Definitions/Core.lean](../KFOL/Definitions/Core.lean) | 17 | yes |
| [KFOL/Definitions/Views.lean](../KFOL/Definitions/Views.lean) | 17 | yes |
| [KFOL/Complexity/OwnerRuntime.lean](../KFOL/Complexity/OwnerRuntime.lean) | 12 |  |
| [KFOL/Definitions/Congruences.lean](../KFOL/Definitions/Congruences.lean) | 11 | yes |
| [KFOL/Definitions/PaperGames.lean](../KFOL/Definitions/PaperGames.lean) | 11 | yes |
| [KFOL/Definitions/PaperAlgebra.lean](../KFOL/Definitions/PaperAlgebra.lean) | 8 | yes |
| [KFOL/Complexity/OwnerTermMachines.lean](../KFOL/Complexity/OwnerTermMachines.lean) | 5 |  |
| [KFOL/Definitions/Atomic.lean](../KFOL/Definitions/Atomic.lean) | 5 | yes |
| [KFOL/Complexity/PolicyTermMachines.lean](../KFOL/Complexity/PolicyTermMachines.lean) | 4 |  |
| [KFOL/Complexity/GuardedPairMachines.lean](../KFOL/Complexity/GuardedPairMachines.lean) | 3 |  |
| [KFOL/Algebra/Semilattice.lean](../KFOL/Algebra/Semilattice.lean) | 2 |  |
| [KFOL/Complexity/CircuitGeneratorRecords.lean](../KFOL/Complexity/CircuitGeneratorRecords.lean) | 2 |  |
| [KFOL/Complexity/OwnerSynthesisBridge.lean](../KFOL/Complexity/OwnerSynthesisBridge.lean) | 2 |  |
| [KFOL/Definitions/TestDomains.lean](../KFOL/Definitions/TestDomains.lean) | 2 | yes |
| [KFOL/Complexity/FiniteTermMachines.lean](../KFOL/Complexity/FiniteTermMachines.lean) | 1 |  |
| [KFOL/Complexity/OwnerSynthesisMachine.lean](../KFOL/Complexity/OwnerSynthesisMachine.lean) | 1 |  |
| [KFOL/Definitions/Algorithms.lean](../KFOL/Definitions/Algorithms.lean) | 1 | yes |
| [KFOL/Definitions/TwoPlayers.lean](../KFOL/Definitions/TwoPlayers.lean) | 1 | yes |
| [KFOL/Strategic/Adequacy.lean](../KFOL/Strategic/Adequacy.lean) | 1 |  |
| [KFOL/Strategic/Quantified/Basic.lean](../KFOL/Strategic/Quantified/Basic.lean) | 1 |  |

External interfaces are recorded without unfolding them:

- ComplexityLib/Cslib interface: 11 boundary constants.
- GameTheory: 46 boundary constants.
- Lean/Std: 160 boundary constants.
- mathlib: 153 boundary constants.

Review per public theorem:

| Public theorem | Semantic declarations | Project modules |
| --- | ---: | ---: |
| [atomic_functions](../Paper.lean#L218) | 21 | 2 |
| [atomic_repeated_triples](../Paper.lean#L206) | 19 | 2 |
| [binary_atom_preserving_iff](../Paper.lean#L228) | 25 | 5 |
| [canonicalization_collapse](../Paper.lean#L466) | 51 | 6 |
| [choice_union_basis](../Paper.lean#L381) | 40 | 3 |
| [common_source](../Paper.lean#L197) | 25 | 2 |
| [congruence_classification](../Paper.lean#L108) | 11 | 2 |
| [constant_sum_value](../Paper.lean#L531) | 43 | 2 |
| [core_extraction_polynomial](../Paper.lean#L501) | 55 | 6 |
| [core_nonfinite_basis](../Paper.lean#L390) | 31 | 2 |
| [determinacy](../Paper.lean#L222) | 20 | 3 |
| [equational_complexity](../Paper.lean#L409) | 61 | 5 |
| [finite_depth_quantifier_reduction](../Paper.lean#L38) | 63 | 5 |
| [guarded_choice_example](../Paper.lean#L253) | 7 | 3 |
| [guarded_pair_complexity](../Paper.lean#L448) | 34 | 8 |
| [idempotent_elimination](../Paper.lean#L171) | 28 | 3 |
| [infinite_winner_algebra](../Paper.lean#L544) | 51 | 2 |
| [intrinsic_player_views](../Paper.lean#L177) | 29 | 3 |
| [joint_owner_observation_failure](../Paper.lean#L362) | 23 | 5 |
| [minimum_reduct_test_domain](../Paper.lean#L166) | 22 | 3 |
| [neutral_union](../Paper.lean#L51) | 4 | 1 |
| [no_atomic_if_then_else](../Paper.lean#L213) | 18 | 1 |
| [no_boolean_product](../Paper.lean#L63) | 4 | 1 |
| [one_constant_rigidity](../Paper.lean#L235) | 21 | 2 |
| [optimal_test_domain](../Paper.lean#L153) | 19 | 2 |
| [owned_choice_semilattices](../Paper.lean#L56) | 4 | 1 |
| [owner_count_dichotomy](../Paper.lean#L422) | 39 | 7 |
| [owner_definability](../Paper.lean#L247) | 7 | 3 |
| [owner_guard_completeness](../Paper.lean#L316) | 35 | 4 |
| [owner_minimum_generator](../Paper.lean#L334) | 44 | 5 |
| [owner_one_table](../Paper.lean#L327) | 36 | 5 |
| [owner_root_status](../Paper.lean#L310) | 22 | 4 |
| [owner_table_algorithms](../Paper.lean#L492) | 80 | 12 |
| [owner_table_synthesis](../Paper.lean#L344) | 45 | 4 |
| [owner_thirty_six_equation_basis](../Paper.lean#L352) | 40 | 4 |
| [pair_countervaluations](../Paper.lean#L147) | 19 | 2 |
| [player_view_orders](../Paper.lean#L85) | 19 | 3 |
| [player_views](../Paper.lean#L69) | 28 | 4 |
| [policy_family_dichotomy](../Paper.lean#L438) | 42 | 7 |
| [public_backward_induction](../Paper.lean#L22) | 29 | 3 |
| [public_forcing](../Paper.lean#L34) | 31 | 3 |
| [public_mixed_support](../Paper.lean#L521) | 75 | 5 |
| [public_nonidempotence](../Paper.lean#L525) | 42 | 2 |
| [public_realizability](../Paper.lean#L30) | 26 | 3 |
| [public_subdirect_representation](../Paper.lean#L77) | 31 | 3 |
| [raw_pair_dichotomy](../Paper.lean#L415) | 41 | 6 |
| [reciprocal_values](../Paper.lean#L540) | 46 | 2 |
| [reduct_test_domains](../Paper.lean#L161) | 23 | 3 |
| [reset_antimatroids](../Paper.lean#L295) | 28 | 3 |
| [reset_basis](../Paper.lean#L290) | 33 | 4 |
| [reset_circuit_complexity](../Paper.lean#L453) | 52 | 7 |
| [reset_circuit_large_tables](../Paper.lean#L401) | 39 | 3 |
| [reset_definability](../Paper.lean#L242) | 23 | 3 |
| [reset_minimum_generator](../Paper.lean#L282) | 20 | 3 |
| [reset_selection](../Paper.lean#L260) | 22 | 3 |
| [reset_table_recognition_polynomial](../Paper.lean#L483) | 33 | 5 |
| [reset_table_semantic_definition](../Paper.lean#L266) | 26 | 4 |
| [reset_table_synthesis](../Paper.lean#L305) | 27 | 2 |
| [reset_table_synthesis_polynomial](../Paper.lean#L486) | 42 | 5 |
| [reset_tables_semantics](../Paper.lean#L274) | 26 | 4 |
| [role_count_identity_theories](../Paper.lean#L458) | 21 | 4 |
| [round_recursion](../Paper.lean#L513) | 42 | 2 |
| [scalar_contextual_equivalence](../Paper.lean#L552) | 74 | 2 |
| [scalar_diagonal_values](../Paper.lean#L535) | 44 | 2 |
| [semilattice_trace](../Paper.lean#L186) | 26 | 3 |
| [status_cell_provenance](../Paper.lean#L139) | 19 | 1 |
| [strict_two_owner_policy](../Paper.lean#L370) | 17 | 3 |
| [switching_observation](../Paper.lean#L102) | 18 | 1 |
| [symmetric_congruence_chain](../Paper.lean#L119) | 13 | 2 |
| [two_owner_selective](../Paper.lean#L375) | 40 | 7 |
| [two_player_degeneracies](../Paper.lean#L569) | 27 | 6 |
| [two_player_finite_basis](../Paper.lean#L577) | 43 | 3 |
| [two_player_identification](../Paper.lean#L561) | 6 | 2 |
| [two_player_round_contexts](../Paper.lean#L590) | 55 | 2 |
| [two_player_round_support](../Paper.lean#L582) | 49 | 4 |
| [uniform_equality_algorithms](../Paper.lean#L474) | 56 | 7 |
| [uniform_matroid_identification](../Paper.lean#L133) | 3 | 2 |
| [unique_winner_observations](../Paper.lean#L93) | 22 | 2 |

The JSON contains every theorem's complete project slice, exact declaration/type/body edges, external interface types, declaration locations and source fingerprints.

Reproduce with `python3 scripts/export_definition_surface.py --check`.
