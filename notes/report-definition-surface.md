# Report theorem-type definition surface

73 public theorem types reach 645 project semantic declarations in 35 source files. 24 of those files are under `KFOL/Definitions`. Generated declarations are grouped into 293 written source review units; 22 derived declarations have file-level locations. Theorem proof bodies are excluded.

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
| [KFOL/Definitions/CoreFunctions.lean](../KFOL/Definitions/CoreFunctions.lean) | 36 | yes |
| [KFOL/Definitions/Quantified.lean](../KFOL/Definitions/Quantified.lean) | 36 | yes |
| [KFOL/Definitions/Reset.lean](../KFOL/Definitions/Reset.lean) | 30 | yes |
| [KFOL/Definitions/CoreBasis.lean](../KFOL/Definitions/CoreBasis.lean) | 29 | yes |
| [KFOL/Definitions/CoreNormalForm.lean](../KFOL/Definitions/CoreNormalForm.lean) | 28 | yes |
| [KFOL/Definitions/Public.lean](../KFOL/Definitions/Public.lean) | 19 | yes |
| [KFOL/Definitions/Reductions.lean](../KFOL/Definitions/Reductions.lean) | 16 | yes |
| [KFOL/Definitions/Counting.lean](../KFOL/Definitions/Counting.lean) | 15 | yes |
| [KFOL/Definitions/Envelope.lean](../KFOL/Definitions/Envelope.lean) | 12 | yes |
| [KFOL/Definitions/CoreGraph.lean](../KFOL/Definitions/CoreGraph.lean) | 9 | yes |
| [KFOL/Definitions/FiniteHorn.lean](../KFOL/Definitions/FiniteHorn.lean) | 9 | yes |
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
- Lean/Std: 158 boundary constants.
- mathlib: 157 boundary constants.

Review per public theorem:

| Public theorem | Semantic declarations | Project modules |
| --- | ---: | ---: |
| [absorbing_winner_budget](../Report.lean#L48) | 23 | 2 |
| [arbitrary_public_quantifier](../Report.lean#L600) | 21 | 1 |
| [atomic_winner_budget](../Report.lean#L43) | 21 | 2 |
| [boolean_threshold_state_lower_bound](../Report.lean#L475) | 45 | 1 |
| [constant_sum_value](../Report.lean#L737) | 43 | 2 |
| [core_binary_interpolation](../Report.lean#L121) | 24 | 3 |
| [core_colored_graph_guards](../Report.lean#L217) | 52 | 5 |
| [core_colored_graph_representation](../Report.lean#L211) | 30 | 3 |
| [core_cut_maximum](../Report.lean#L247) | 52 | 4 |
| [core_cut_recognition](../Report.lean#L269) | 54 | 4 |
| [core_cut_round_bound](../Report.lean#L259) | 31 | 3 |
| [core_cut_synthesis](../Report.lean#L240) | 53 | 4 |
| [core_four_valuation_persistence](../Report.lean#L174) | 21 | 2 |
| [core_guard_compatibility](../Report.lean#L92) | 84 | 6 |
| [core_guard_synthesis](../Report.lean#L84) | 41 | 4 |
| [core_local_interpolation](../Report.lean#L169) | 24 | 3 |
| [core_local_normal_forms](../Report.lean#L138) | 52 | 5 |
| [core_pairwise_obstruction](../Report.lean#L126) | 26 | 3 |
| [core_profile_maximum](../Report.lean#L147) | 22 | 2 |
| [core_profile_nonconvexity](../Report.lean#L159) | 23 | 3 |
| [core_singleton_profiles](../Report.lean#L204) | 11 | 3 |
| [core_source_interior](../Report.lean#L100) | 57 | 5 |
| [core_source_interior_realization](../Report.lean#L108) | 76 | 6 |
| [core_source_probe_count](../Report.lean#L78) | 11 | 1 |
| [core_source_reconstruction](../Report.lean#L71) | 42 | 4 |
| [core_ternary_obstruction](../Report.lean#L192) | 31 | 4 |
| [core_three_valuation_persistence](../Report.lean#L227) | 21 | 2 |
| [core_typed_upper_clone_cover](../Report.lean#L340) | 46 | 6 |
| [core_variable_bound_obstruction](../Report.lean#L311) | 53 | 4 |
| [expanded_variety_envelope](../Report.lean#L707) | 51 | 4 |
| [finite_powerset_relational_representation](../Report.lean#L648) | 2 | 1 |
| [idempotency_certificates](../Report.lean#L275) | 19 | 1 |
| [intersection_not_definable](../Report.lean#L701) | 18 | 1 |
| [native_nonfinite_basis](../Report.lean#L380) | 36 | 2 |
| [owned_choice_relational_representation](../Report.lean#L686) | 6 | 2 |
| [owned_choice_zero_extension](../Report.lean#L661) | 5 | 2 |
| [owned_choice_zero_representation](../Report.lean#L675) | 7 | 2 |
| [owner_four_variable_obstruction](../Report.lean#L329) | 62 | 2 |
| [pair_game_boolean_full_abstraction](../Report.lean#L454) | 78 | 1 |
| [permutation_envelope_cardinality](../Report.lean#L720) | 1 | 1 |
| [public_choice_small_support](../Report.lean#L519) | 57 | 3 |
| [public_choice_support_sharp](../Report.lean#L528) | 32 | 1 |
| [public_equilibrium_strategic_form](../Report.lean#L365) | 40 | 1 |
| [public_nonidempotence](../Report.lean#L729) | 42 | 2 |
| [public_query_compilation](../Report.lean#L633) | 80 | 3 |
| [public_query_equivalence](../Report.lean#L641) | 74 | 4 |
| [public_sharp_absorbing_budget](../Report.lean#L62) | 57 | 5 |
| [public_sharp_winner_budget](../Report.lean#L53) | 34 | 4 |
| [public_term_interpretation](../Report.lean#L374) | 54 | 3 |
| [reciprocal_values](../Report.lean#L750) | 46 | 2 |
| [reset_circuit_exponential_tables](../Report.lean#L538) | 42 | 3 |
| [reset_circuit_generator](../Report.lean#L590) | 36 | 4 |
| [reset_circuit_reduction](../Report.lean#L579) | 70 | 5 |
| [reset_circuit_tree_succinctness](../Report.lean#L547) | 58 | 5 |
| [reset_family_product](../Report.lean#L305) | 15 | 2 |
| [reset_no_relational_representation](../Report.lean#L694) | 5 | 2 |
| [reset_substitution](../Report.lean#L294) | 24 | 3 |
| [reset_table_size](../Report.lean#L608) | 21 | 2 |
| [round_product_beliefs](../Report.lean#L421) | 45 | 5 |
| [round_profile_consistency](../Report.lean#L408) | 45 | 5 |
| [round_protocol_foundations](../Report.lean#L392) | 28 | 1 |
| [scalar_contextual_equivalence](../Report.lean#L756) | 74 | 2 |
| [scalar_diagonal_security](../Report.lean#L502) | 4 | 2 |
| [scalar_diagonal_values](../Report.lean#L743) | 44 | 2 |
| [scalar_parallel_laws](../Report.lean#L432) | 0 | 0 |
| [scalar_rational_observation_order](../Report.lean#L487) | 64 | 1 |
| [scalar_rational_values](../Report.lean#L442) | 63 | 1 |
| [serial_order_independence](../Report.lean#L574) | 39 | 2 |
| [two_player_forcing_coordinates](../Report.lean#L614) | 6 | 2 |
| [well_founded_quantifier_fold](../Report.lean#L565) | 60 | 2 |
| [winner_accounting](../Report.lean#L27) | 25 | 2 |
| [winner_budget_eq_iff](../Report.lean#L38) | 23 | 2 |
| [winner_leaf_mass](../Report.lean#L33) | 18 | 2 |

The JSON contains every theorem's complete project slice, exact declaration/type/body edges, external interface types, declaration locations and source fingerprints.

Reproduce with `python3 scripts/export_definition_surface.py --check --entrypoint Report`.
