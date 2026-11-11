# Report theorem-type definition surface

73 public theorem types reach 621 project semantic declarations in 36 source files. 25 of those files are under `KFOL/Definitions`. Generated declarations are grouped into 286 written source review units; 18 derived declarations have file-level locations. Theorem proof bodies are excluded.

This is a review index. Definitions still require human review against the manuscript; the separate proof/axiom and import audits remain necessary.

| Source | Reachable declarations | Central definitions |
| --- | ---: | --- |
| [KFOL/Definitions/Rounds.lean](../KFOL/Definitions/Rounds.lean) | 88 | yes |
| [Report.lean](../Report.lean) | 74 |  |
| [KFOL/Definitions/Queries.lean](../KFOL/Definitions/Queries.lean) | 59 | yes |
| [KFOL/Definitions/Strategic.lean](../KFOL/Definitions/Strategic.lean) | 56 | yes |
| [KFOL/Definitions/Owner.lean](../KFOL/Definitions/Owner.lean) | 52 | yes |
| [KFOL/Definitions/Equational.lean](../KFOL/Definitions/Equational.lean) | 46 | yes |
| [KFOL/Definitions/Circuits.lean](../KFOL/Definitions/Circuits.lean) | 44 | yes |
| [KFOL/Definitions/Quantified.lean](../KFOL/Definitions/Quantified.lean) | 36 | yes |
| [KFOL/Definitions/Reset.lean](../KFOL/Definitions/Reset.lean) | 30 | yes |
| [KFOL/Definitions/CoreBasis.lean](../KFOL/Definitions/CoreBasis.lean) | 29 | yes |
| [KFOL/Definitions/CoreNormalForm.lean](../KFOL/Definitions/CoreNormalForm.lean) | 25 | yes |
| [KFOL/Definitions/Public.lean](../KFOL/Definitions/Public.lean) | 19 | yes |
| [KFOL/Definitions/Reductions.lean](../KFOL/Definitions/Reductions.lean) | 16 | yes |
| [KFOL/Definitions/Counting.lean](../KFOL/Definitions/Counting.lean) | 15 | yes |
| [KFOL/Definitions/CoreFunctions.lean](../KFOL/Definitions/CoreFunctions.lean) | 13 | yes |
| [KFOL/Definitions/Envelope.lean](../KFOL/Definitions/Envelope.lean) | 12 | yes |
| [KFOL/Definitions/CoreGraph.lean](../KFOL/Definitions/CoreGraph.lean) | 9 | yes |
| [KFOL/Definitions/CoreInterpolation.lean](../KFOL/Definitions/CoreInterpolation.lean) | 9 | yes |
| [KFOL/Definitions/Views.lean](../KFOL/Definitions/Views.lean) | 9 | yes |
| [KFOL/Definitions/Core.lean](../KFOL/Definitions/Core.lean) | 7 | yes |
| [KFOL/Rounds/SerializationTrace.lean](../KFOL/Rounds/SerializationTrace.lean) | 7 |  |
| [KFOL/Definitions/PaperGames.lean](../KFOL/Definitions/PaperGames.lean) | 6 | yes |
| [KFOL/Definitions/StrategicCounting.lean](../KFOL/Definitions/StrategicCounting.lean) | 6 | yes |
| [KFOL/Rounds/PrefixLaw.lean](../KFOL/Rounds/PrefixLaw.lean) | 6 |  |
| [KFOL/Core/Locality.lean](../KFOL/Core/Locality.lean) | 4 |  |
| [KFOL/Definitions/Relational.lean](../KFOL/Definitions/Relational.lean) | 3 | yes |
| [KFOL/Rounds/DecisionSites.lean](../KFOL/Rounds/DecisionSites.lean) | 3 |  |
| [KFOL/Core/Quotients.lean](../KFOL/Core/Quotients.lean) | 2 |  |
| [KFOL/Definitions/CoreCrown.lean](../KFOL/Definitions/CoreCrown.lean) | 2 | yes |
| [KFOL/Core/AtomicNative.lean](../KFOL/Core/AtomicNative.lean) | 1 |  |
| [KFOL/Core/ModelLaws.lean](../KFOL/Core/ModelLaws.lean) | 1 |  |
| [KFOL/Definitions/PaperAlgebra.lean](../KFOL/Definitions/PaperAlgebra.lean) | 1 | yes |
| [KFOL/Definitions/TwoPlayers.lean](../KFOL/Definitions/TwoPlayers.lean) | 1 | yes |
| [KFOL/Rounds/InformationFibers.lean](../KFOL/Rounds/InformationFibers.lean) | 1 |  |
| [KFOL/Rounds/Scalar/Diagonal.lean](../KFOL/Rounds/Scalar/Diagonal.lean) | 1 |  |
| [KFOL/Strategic/Adequacy.lean](../KFOL/Strategic/Adequacy.lean) | 1 |  |

External interfaces are recorded without unfolding them:

- Batteries: 1 boundary constants.
- GameTheory: 92 boundary constants.
- Lean/Std: 157 boundary constants.
- mathlib: 148 boundary constants.

Review per public theorem:

| Public theorem | Semantic declarations | Project modules |
| --- | ---: | ---: |
| [absorbing_winner_budget](../Report.lean#L54) | 23 | 2 |
| [arbitrary_public_quantifier](../Report.lean#L598) | 21 | 1 |
| [atomic_winner_budget](../Report.lean#L49) | 21 | 2 |
| [boolean_threshold_state_lower_bound](../Report.lean#L473) | 45 | 1 |
| [constant_sum_value](../Report.lean#L735) | 43 | 2 |
| [core_binary_interpolation](../Report.lean#L98) | 24 | 3 |
| [core_colored_graph_guards](../Report.lean#L250) | 52 | 5 |
| [core_colored_graph_representation](../Report.lean#L244) | 30 | 3 |
| [core_cyclic_persistence](../Report.lean#L203) | 23 | 3 |
| [core_five_local_profile_obstruction](../Report.lean#L193) | 24 | 3 |
| [core_four_local_without_minorant](../Report.lean#L187) | 24 | 3 |
| [core_four_valuation_persistence](../Report.lean#L151) | 21 | 2 |
| [core_guard_synthesis](../Report.lean#L90) | 41 | 4 |
| [core_local_interpolation](../Report.lean#L146) | 24 | 3 |
| [core_local_normal_forms](../Report.lean#L115) | 52 | 5 |
| [core_pairwise_obstruction](../Report.lean#L103) | 26 | 3 |
| [core_peeling_interpolation](../Report.lean#L228) | 30 | 3 |
| [core_profile_maximum](../Report.lean#L124) | 22 | 2 |
| [core_profile_nonconvexity](../Report.lean#L136) | 23 | 3 |
| [core_singleton_profiles](../Report.lean#L237) | 11 | 3 |
| [core_source_probe_count](../Report.lean#L84) | 11 | 1 |
| [core_source_reconstruction](../Report.lean#L77) | 42 | 4 |
| [core_ternary_obstruction](../Report.lean#L169) | 31 | 4 |
| [core_three_local_without_minorant](../Report.lean#L181) | 24 | 3 |
| [core_three_valuation_persistence](../Report.lean#L260) | 21 | 2 |
| [core_typed_upper_clone_cover](../Report.lean#L338) | 46 | 6 |
| [core_variable_bound_obstruction](../Report.lean#L309) | 53 | 4 |
| [expanded_variety_envelope](../Report.lean#L705) | 51 | 4 |
| [finite_powerset_relational_representation](../Report.lean#L646) | 2 | 1 |
| [full_no_finite_relation_basis](../Report.lean#L219) | 20 | 2 |
| [full_not_finitely_related](../Report.lean#L211) | 22 | 3 |
| [idempotency_certificates](../Report.lean#L273) | 19 | 1 |
| [intersection_not_definable](../Report.lean#L699) | 18 | 1 |
| [native_nonfinite_basis](../Report.lean#L378) | 36 | 2 |
| [owned_choice_relational_representation](../Report.lean#L684) | 6 | 2 |
| [owned_choice_zero_extension](../Report.lean#L659) | 5 | 2 |
| [owned_choice_zero_representation](../Report.lean#L673) | 7 | 2 |
| [owner_four_variable_obstruction](../Report.lean#L327) | 62 | 2 |
| [pair_game_boolean_full_abstraction](../Report.lean#L452) | 78 | 1 |
| [permutation_envelope_cardinality](../Report.lean#L718) | 1 | 1 |
| [public_choice_small_support](../Report.lean#L517) | 57 | 3 |
| [public_choice_support_sharp](../Report.lean#L526) | 32 | 1 |
| [public_equilibrium_strategic_form](../Report.lean#L363) | 40 | 1 |
| [public_nonidempotence](../Report.lean#L727) | 42 | 2 |
| [public_query_compilation](../Report.lean#L631) | 80 | 3 |
| [public_query_equivalence](../Report.lean#L639) | 74 | 4 |
| [public_sharp_absorbing_budget](../Report.lean#L68) | 57 | 5 |
| [public_sharp_winner_budget](../Report.lean#L59) | 34 | 4 |
| [public_term_interpretation](../Report.lean#L372) | 54 | 3 |
| [reciprocal_values](../Report.lean#L748) | 46 | 2 |
| [reset_circuit_exponential_tables](../Report.lean#L536) | 42 | 3 |
| [reset_circuit_generator](../Report.lean#L588) | 36 | 4 |
| [reset_circuit_reduction](../Report.lean#L577) | 70 | 5 |
| [reset_circuit_tree_succinctness](../Report.lean#L545) | 58 | 5 |
| [reset_family_product](../Report.lean#L303) | 15 | 2 |
| [reset_no_relational_representation](../Report.lean#L692) | 5 | 2 |
| [reset_substitution](../Report.lean#L292) | 24 | 3 |
| [reset_table_size](../Report.lean#L606) | 21 | 2 |
| [round_product_beliefs](../Report.lean#L419) | 45 | 5 |
| [round_profile_consistency](../Report.lean#L406) | 45 | 5 |
| [round_protocol_foundations](../Report.lean#L390) | 28 | 1 |
| [scalar_contextual_equivalence](../Report.lean#L754) | 74 | 2 |
| [scalar_diagonal_security](../Report.lean#L500) | 4 | 2 |
| [scalar_diagonal_values](../Report.lean#L741) | 44 | 2 |
| [scalar_parallel_laws](../Report.lean#L430) | 0 | 0 |
| [scalar_rational_observation_order](../Report.lean#L485) | 64 | 1 |
| [scalar_rational_values](../Report.lean#L440) | 63 | 1 |
| [serial_order_independence](../Report.lean#L572) | 39 | 2 |
| [two_player_forcing_coordinates](../Report.lean#L612) | 6 | 2 |
| [well_founded_quantifier_fold](../Report.lean#L563) | 60 | 2 |
| [winner_accounting](../Report.lean#L33) | 25 | 2 |
| [winner_budget_eq_iff](../Report.lean#L44) | 23 | 2 |
| [winner_leaf_mass](../Report.lean#L39) | 18 | 2 |

The JSON contains every theorem's complete project slice, exact declaration/type/body edges, external interface types, declaration locations and source fingerprints.

Reproduce with `python3 scripts/export_definition_surface.py --check --entrypoint Report`.
