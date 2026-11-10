# Paper theorem-type definition surface

80 public theorem types reach 652 project semantic declarations in 35 source files. 23 of those files are under `KFOL/Definitions`. Generated declarations are grouped into 337 written source review units; 7 derived declarations have file-level locations. Theorem proof bodies are excluded.

This is a review index. Definitions still require human review against the manuscript; the separate proof/axiom and import audits remain necessary.

| Source | Reachable declarations | Central definitions |
| --- | ---: | --- |
| [KFOL/Definitions/Rounds.lean](../KFOL/Definitions/Rounds.lean) | 87 | yes |
| [Paper.lean](../Paper.lean) | 80 |  |
| [KFOL/Definitions/Owner.lean](../KFOL/Definitions/Owner.lean) | 73 | yes |
| [KFOL/Definitions/Encoding.lean](../KFOL/Definitions/Encoding.lean) | 48 | yes |
| [KFOL/Definitions/Equational.lean](../KFOL/Definitions/Equational.lean) | 48 | yes |
| [KFOL/Definitions/Reset.lean](../KFOL/Definitions/Reset.lean) | 43 | yes |
| [KFOL/Definitions/Complexity.lean](../KFOL/Definitions/Complexity.lean) | 41 | yes |
| [KFOL/Definitions/Reductions.lean](../KFOL/Definitions/Reductions.lean) | 37 | yes |
| [KFOL/Definitions/Quantified.lean](../KFOL/Definitions/Quantified.lean) | 36 | yes |
| [KFOL/Definitions/Strategic.lean](../KFOL/Definitions/Strategic.lean) | 33 | yes |
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
| [KFOL/Algorithms/CircuitCode.lean](../KFOL/Algorithms/CircuitCode.lean) | 1 |  |
| [KFOL/Complexity/FiniteTermMachines.lean](../KFOL/Complexity/FiniteTermMachines.lean) | 1 |  |
| [KFOL/Complexity/OwnerSynthesisMachine.lean](../KFOL/Complexity/OwnerSynthesisMachine.lean) | 1 |  |
| [KFOL/Definitions/Algorithms.lean](../KFOL/Definitions/Algorithms.lean) | 1 | yes |
| [KFOL/Definitions/TwoPlayers.lean](../KFOL/Definitions/TwoPlayers.lean) | 1 | yes |
| [KFOL/Strategic/Adequacy.lean](../KFOL/Strategic/Adequacy.lean) | 1 |  |

External interfaces are recorded without unfolding them:

- ComplexityLib/Cslib interface: 11 boundary constants.
- GameTheory: 46 boundary constants.
- Lean/Std: 161 boundary constants.
- mathlib: 153 boundary constants.

Review per public theorem:

| Public theorem | Semantic declarations | Project modules |
| --- | ---: | ---: |
| [atomic_functions](../Paper.lean#L223) | 21 | 2 |
| [atomic_repeated_triples](../Paper.lean#L211) | 19 | 2 |
| [binary_atom_preserving_iff](../Paper.lean#L233) | 25 | 5 |
| [canonicalization_collapse](../Paper.lean#L494) | 51 | 6 |
| [choice_union_basis](../Paper.lean#L386) | 40 | 3 |
| [common_source](../Paper.lean#L202) | 25 | 2 |
| [congruence_classification](../Paper.lean#L113) | 11 | 2 |
| [constant_sum_value](../Paper.lean#L559) | 43 | 2 |
| [core_extraction_polynomial](../Paper.lean#L529) | 55 | 6 |
| [core_nonfinite_basis](../Paper.lean#L395) | 31 | 2 |
| [determinacy](../Paper.lean#L227) | 20 | 3 |
| [equational_complexity](../Paper.lean#L437) | 61 | 5 |
| [expanded_nonfinite_basis](../Paper.lean#L406) | 43 | 2 |
| [finite_depth_quantifier_reduction](../Paper.lean#L43) | 60 | 2 |
| [guarded_choice_example](../Paper.lean#L258) | 7 | 3 |
| [guarded_pair_complexity](../Paper.lean#L476) | 34 | 8 |
| [idempotent_elimination](../Paper.lean#L176) | 28 | 3 |
| [infinite_winner_algebra](../Paper.lean#L572) | 51 | 2 |
| [intrinsic_player_views](../Paper.lean#L182) | 29 | 3 |
| [joint_owner_observation_failure](../Paper.lean#L367) | 23 | 5 |
| [minimum_reduct_test_domain](../Paper.lean#L171) | 22 | 3 |
| [neutral_union](../Paper.lean#L56) | 4 | 1 |
| [no_atomic_if_then_else](../Paper.lean#L218) | 18 | 1 |
| [no_boolean_product](../Paper.lean#L68) | 4 | 1 |
| [one_constant_rigidity](../Paper.lean#L240) | 21 | 2 |
| [optimal_test_domain](../Paper.lean#L158) | 19 | 2 |
| [owned_choice_semilattices](../Paper.lean#L61) | 4 | 1 |
| [owner_count_dichotomy](../Paper.lean#L450) | 39 | 7 |
| [owner_definability](../Paper.lean#L252) | 7 | 3 |
| [owner_guard_completeness](../Paper.lean#L321) | 35 | 4 |
| [owner_minimum_generator](../Paper.lean#L339) | 44 | 5 |
| [owner_one_table](../Paper.lean#L332) | 36 | 5 |
| [owner_root_status](../Paper.lean#L315) | 22 | 4 |
| [owner_table_algorithms](../Paper.lean#L520) | 80 | 12 |
| [owner_table_synthesis](../Paper.lean#L349) | 45 | 4 |
| [owner_thirty_six_equation_basis](../Paper.lean#L357) | 40 | 4 |
| [pair_countervaluations](../Paper.lean#L152) | 19 | 2 |
| [player_view_orders](../Paper.lean#L90) | 19 | 3 |
| [player_views](../Paper.lean#L74) | 28 | 4 |
| [policy_family_dichotomy](../Paper.lean#L466) | 42 | 7 |
| [public_backward_induction](../Paper.lean#L22) | 29 | 3 |
| [public_forcing](../Paper.lean#L34) | 31 | 3 |
| [public_mixed_support](../Paper.lean#L549) | 75 | 5 |
| [public_nonidempotence](../Paper.lean#L553) | 42 | 2 |
| [public_realizability](../Paper.lean#L30) | 26 | 3 |
| [public_subdirect_representation](../Paper.lean#L82) | 31 | 3 |
| [quantifier_fold](../Paper.lean#L38) | 51 | 2 |
| [raw_pair_dichotomy](../Paper.lean#L443) | 41 | 6 |
| [reciprocal_values](../Paper.lean#L568) | 46 | 2 |
| [reduct_test_domains](../Paper.lean#L166) | 23 | 3 |
| [reset_antimatroids](../Paper.lean#L300) | 28 | 3 |
| [reset_basis](../Paper.lean#L295) | 33 | 4 |
| [reset_circuit_complexity](../Paper.lean#L481) | 53 | 8 |
| [reset_circuit_large_tables](../Paper.lean#L429) | 39 | 3 |
| [reset_definability](../Paper.lean#L247) | 23 | 3 |
| [reset_minimum_generator](../Paper.lean#L287) | 20 | 3 |
| [reset_selection](../Paper.lean#L265) | 22 | 3 |
| [reset_table_recognition_polynomial](../Paper.lean#L511) | 33 | 5 |
| [reset_table_semantic_definition](../Paper.lean#L271) | 26 | 4 |
| [reset_table_synthesis](../Paper.lean#L310) | 27 | 2 |
| [reset_table_synthesis_polynomial](../Paper.lean#L514) | 42 | 5 |
| [reset_tables_semantics](../Paper.lean#L279) | 26 | 4 |
| [role_count_identity_theories](../Paper.lean#L486) | 21 | 4 |
| [round_recursion](../Paper.lean#L541) | 42 | 2 |
| [scalar_contextual_equivalence](../Paper.lean#L580) | 74 | 2 |
| [scalar_diagonal_values](../Paper.lean#L563) | 44 | 2 |
| [semilattice_trace](../Paper.lean#L191) | 26 | 3 |
| [status_cell_provenance](../Paper.lean#L144) | 19 | 1 |
| [strict_two_owner_policy](../Paper.lean#L375) | 17 | 3 |
| [switching_observation](../Paper.lean#L107) | 18 | 1 |
| [symmetric_congruence_chain](../Paper.lean#L124) | 13 | 2 |
| [two_owner_selective](../Paper.lean#L380) | 40 | 7 |
| [two_player_degeneracies](../Paper.lean#L597) | 27 | 6 |
| [two_player_finite_basis](../Paper.lean#L605) | 43 | 3 |
| [two_player_identification](../Paper.lean#L589) | 6 | 2 |
| [two_player_round_contexts](../Paper.lean#L618) | 55 | 2 |
| [two_player_round_support](../Paper.lean#L610) | 49 | 4 |
| [uniform_equality_algorithms](../Paper.lean#L502) | 56 | 7 |
| [uniform_matroid_identification](../Paper.lean#L138) | 3 | 2 |
| [unique_winner_observations](../Paper.lean#L98) | 22 | 2 |

The JSON contains every theorem's complete project slice, exact declaration/type/body edges, external interface types, declaration locations and source fingerprints.

Reproduce with `python3 scripts/export_definition_surface.py --check`.
