# Report theorem-type definition surface

96 public theorem types reach 725 project semantic declarations in 43 source files. 32 of those files are under `KFOL/Definitions`. Generated declarations are grouped into 340 written source review units; 22 derived declarations have file-level locations. Theorem proof bodies are excluded.

This is a review index. Definitions still require human review against the manuscript; the separate proof/axiom and import audits remain necessary.

| Source | Reachable declarations | Central definitions |
| --- | ---: | --- |
| [Report.lean](../Report.lean) | 97 |  |
| [KFOL/Definitions/Rounds.lean](../KFOL/Definitions/Rounds.lean) | 88 | yes |
| [KFOL/Definitions/Queries.lean](../KFOL/Definitions/Queries.lean) | 59 | yes |
| [KFOL/Definitions/Strategic.lean](../KFOL/Definitions/Strategic.lean) | 56 | yes |
| [KFOL/Definitions/Owner.lean](../KFOL/Definitions/Owner.lean) | 52 | yes |
| [KFOL/Definitions/Bichain.lean](../KFOL/Definitions/Bichain.lean) | 50 | yes |
| [KFOL/Definitions/Equational.lean](../KFOL/Definitions/Equational.lean) | 46 | yes |
| [KFOL/Definitions/Circuits.lean](../KFOL/Definitions/Circuits.lean) | 44 | yes |
| [KFOL/Definitions/Quantified.lean](../KFOL/Definitions/Quantified.lean) | 36 | yes |
| [KFOL/Definitions/CoreNormalForm.lean](../KFOL/Definitions/CoreNormalForm.lean) | 30 | yes |
| [KFOL/Definitions/Reset.lean](../KFOL/Definitions/Reset.lean) | 30 | yes |
| [KFOL/Definitions/CoreBasis.lean](../KFOL/Definitions/CoreBasis.lean) | 29 | yes |
| [KFOL/Definitions/Public.lean](../KFOL/Definitions/Public.lean) | 19 | yes |
| [KFOL/Definitions/Reductions.lean](../KFOL/Definitions/Reductions.lean) | 16 | yes |
| [KFOL/Definitions/Counting.lean](../KFOL/Definitions/Counting.lean) | 15 | yes |
| [KFOL/Definitions/Views.lean](../KFOL/Definitions/Views.lean) | 15 | yes |
| [KFOL/Definitions/CoreFunctions.lean](../KFOL/Definitions/CoreFunctions.lean) | 13 | yes |
| [KFOL/Definitions/Envelope.lean](../KFOL/Definitions/Envelope.lean) | 12 | yes |
| [KFOL/Definitions/CoreHypergraphs.lean](../KFOL/Definitions/CoreHypergraphs.lean) | 10 | yes |
| [KFOL/Definitions/ProfileRelations.lean](../KFOL/Definitions/ProfileRelations.lean) | 10 | yes |
| [KFOL/Definitions/CoreCertificates.lean](../KFOL/Definitions/CoreCertificates.lean) | 9 | yes |
| [KFOL/Definitions/CoreGraph.lean](../KFOL/Definitions/CoreGraph.lean) | 9 | yes |
| [KFOL/Definitions/CoreInterpolation.lean](../KFOL/Definitions/CoreInterpolation.lean) | 9 | yes |
| [KFOL/Definitions/Core.lean](../KFOL/Definitions/Core.lean) | 7 | yes |
| [KFOL/Rounds/SerializationTrace.lean](../KFOL/Rounds/SerializationTrace.lean) | 7 |  |
| [KFOL/Definitions/PaperGames.lean](../KFOL/Definitions/PaperGames.lean) | 6 | yes |
| [KFOL/Definitions/ProfileBounds.lean](../KFOL/Definitions/ProfileBounds.lean) | 6 | yes |
| [KFOL/Definitions/StrategicCounting.lean](../KFOL/Definitions/StrategicCounting.lean) | 6 | yes |
| [KFOL/Rounds/PrefixLaw.lean](../KFOL/Rounds/PrefixLaw.lean) | 6 |  |
| [KFOL/Core/Locality.lean](../KFOL/Core/Locality.lean) | 4 |  |
| [KFOL/Definitions/AtomicObserver.lean](../KFOL/Definitions/AtomicObserver.lean) | 4 | yes |
| [KFOL/Definitions/CoreAmalgamation.lean](../KFOL/Definitions/CoreAmalgamation.lean) | 4 | yes |
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
- Lean/Std: 161 boundary constants.
- mathlib: 154 boundary constants.

Review per public theorem:

| Public theorem | Semantic declarations | Project modules |
| --- | ---: | ---: |
| [absorbing_winner_budget](../Report.lean#L68) | 23 | 2 |
| [arbitrary_public_quantifier](../Report.lean#L843) | 21 | 1 |
| [atomic_winner_budget](../Report.lean#L63) | 21 | 2 |
| [bichain_projection_fiber](../Report.lean#L232) | 44 | 1 |
| [bichain_projection_fiber_unique](../Report.lean#L239) | 39 | 1 |
| [boolean_threshold_state_lower_bound](../Report.lean#L718) | 45 | 1 |
| [constant_sum_value](../Report.lean#L980) | 43 | 2 |
| [core_atomic_observer](../Report.lean#L246) | 25 | 3 |
| [core_binary_interpolation](../Report.lean#L112) | 24 | 3 |
| [core_bounded_profile_pair](../Report.lean#L388) | 17 | 4 |
| [core_bounded_profiles](../Report.lean#L409) | 19 | 4 |
| [core_bounded_rainbow_query](../Report.lean#L398) | 20 | 4 |
| [core_closed_hypergraph_basis](../Report.lean#L310) | 23 | 3 |
| [core_colored_graph_guards](../Report.lean#L495) | 52 | 5 |
| [core_colored_graph_representation](../Report.lean#L489) | 30 | 3 |
| [core_cyclic_persistence](../Report.lean#L266) | 23 | 3 |
| [core_exact_profile_point](../Report.lean#L437) | 21 | 4 |
| [core_exponential_locality](../Report.lean#L291) | 22 | 3 |
| [core_five_local_profile_obstruction](../Report.lean#L207) | 24 | 3 |
| [core_four_local_without_minorant](../Report.lean#L201) | 24 | 3 |
| [core_four_valuation_persistence](../Report.lean#L165) | 21 | 2 |
| [core_guard_synthesis](../Report.lean#L104) | 41 | 4 |
| [core_hypergraph_guards](../Report.lean#L331) | 74 | 6 |
| [core_hypergraph_operations](../Report.lean#L320) | 40 | 4 |
| [core_local_interpolation](../Report.lean#L160) | 24 | 3 |
| [core_local_normal_forms](../Report.lean#L129) | 52 | 5 |
| [core_negative_budget_obstructions](../Report.lean#L479) | 21 | 2 |
| [core_observer_amalgamation](../Report.lean#L254) | 30 | 4 |
| [core_omission_independence](../Report.lean#L471) | 21 | 2 |
| [core_output_is_input_union](../Report.lean#L465) | 21 | 2 |
| [core_pairwise_obstruction](../Report.lean#L117) | 26 | 3 |
| [core_peeling_interpolation](../Report.lean#L301) | 30 | 3 |
| [core_pointwise_profile_obstruction](../Report.lean#L448) | 29 | 4 |
| [core_profile_bound_coupling](../Report.lean#L425) | 18 | 4 |
| [core_profile_maximum](../Report.lean#L138) | 22 | 2 |
| [core_profile_nonconvexity](../Report.lean#L150) | 23 | 3 |
| [core_profile_relations](../Report.lean#L346) | 10 | 1 |
| [core_single_bound_profiles](../Report.lean#L362) | 16 | 3 |
| [core_single_bound_small_witness](../Report.lean#L375) | 17 | 3 |
| [core_singleton_profiles](../Report.lean#L355) | 11 | 3 |
| [core_source_probe_count](../Report.lean#L98) | 11 | 1 |
| [core_source_reconstruction](../Report.lean#L91) | 42 | 4 |
| [core_ternary_obstruction](../Report.lean#L183) | 31 | 4 |
| [core_three_local_without_minorant](../Report.lean#L195) | 24 | 3 |
| [core_three_valuation_persistence](../Report.lean#L505) | 21 | 2 |
| [core_typed_upper_clone_cover](../Report.lean#L583) | 46 | 6 |
| [core_unbounded_profile_condition](../Report.lean#L419) | 7 | 3 |
| [core_variable_bound_obstruction](../Report.lean#L554) | 53 | 4 |
| [core_whole_input_provenance](../Report.lean#L458) | 21 | 2 |
| [expanded_variety_envelope](../Report.lean#L950) | 51 | 4 |
| [finite_powerset_relational_representation](../Report.lean#L891) | 2 | 1 |
| [full_no_finite_relation_basis](../Report.lean#L282) | 20 | 2 |
| [full_not_finitely_related](../Report.lean#L274) | 22 | 3 |
| [idempotency_certificates](../Report.lean#L518) | 19 | 1 |
| [intersection_not_definable](../Report.lean#L944) | 18 | 1 |
| [native_nonfinite_basis](../Report.lean#L623) | 36 | 2 |
| [observer_bichain](../Report.lean#L217) | 38 | 2 |
| [owned_choice_relational_representation](../Report.lean#L929) | 6 | 2 |
| [owned_choice_zero_extension](../Report.lean#L904) | 5 | 2 |
| [owned_choice_zero_representation](../Report.lean#L918) | 7 | 2 |
| [owner_four_variable_obstruction](../Report.lean#L572) | 62 | 2 |
| [pair_game_boolean_full_abstraction](../Report.lean#L697) | 78 | 1 |
| [permutation_envelope_cardinality](../Report.lean#L963) | 1 | 1 |
| [public_choice_small_support](../Report.lean#L762) | 57 | 3 |
| [public_choice_support_sharp](../Report.lean#L771) | 32 | 1 |
| [public_equilibrium_strategic_form](../Report.lean#L608) | 40 | 1 |
| [public_nonidempotence](../Report.lean#L972) | 42 | 2 |
| [public_query_compilation](../Report.lean#L876) | 80 | 3 |
| [public_query_equivalence](../Report.lean#L884) | 74 | 4 |
| [public_sharp_absorbing_budget](../Report.lean#L82) | 57 | 5 |
| [public_sharp_winner_budget](../Report.lean#L73) | 34 | 4 |
| [public_term_interpretation](../Report.lean#L617) | 54 | 3 |
| [reciprocal_values](../Report.lean#L993) | 46 | 2 |
| [reset_circuit_exponential_tables](../Report.lean#L781) | 42 | 3 |
| [reset_circuit_generator](../Report.lean#L833) | 36 | 4 |
| [reset_circuit_reduction](../Report.lean#L822) | 70 | 5 |
| [reset_circuit_tree_succinctness](../Report.lean#L790) | 58 | 5 |
| [reset_family_product](../Report.lean#L548) | 15 | 2 |
| [reset_no_relational_representation](../Report.lean#L937) | 5 | 2 |
| [reset_substitution](../Report.lean#L537) | 24 | 3 |
| [reset_table_size](../Report.lean#L851) | 21 | 2 |
| [round_product_beliefs](../Report.lean#L664) | 45 | 5 |
| [round_profile_consistency](../Report.lean#L651) | 45 | 5 |
| [round_protocol_foundations](../Report.lean#L635) | 28 | 1 |
| [scalar_contextual_equivalence](../Report.lean#L999) | 74 | 2 |
| [scalar_diagonal_security](../Report.lean#L745) | 4 | 2 |
| [scalar_diagonal_values](../Report.lean#L986) | 44 | 2 |
| [scalar_parallel_laws](../Report.lean#L675) | 0 | 0 |
| [scalar_rational_observation_order](../Report.lean#L730) | 64 | 1 |
| [scalar_rational_values](../Report.lean#L685) | 63 | 1 |
| [serial_order_independence](../Report.lean#L817) | 39 | 2 |
| [two_player_forcing_coordinates](../Report.lean#L857) | 6 | 2 |
| [well_founded_quantifier_fold](../Report.lean#L808) | 60 | 2 |
| [winner_accounting](../Report.lean#L47) | 25 | 2 |
| [winner_budget_eq_iff](../Report.lean#L58) | 23 | 2 |
| [winner_leaf_mass](../Report.lean#L53) | 18 | 2 |

The JSON contains every theorem's complete project slice, exact declaration/type/body edges, external interface types, declaration locations and source fingerprints.

Reproduce with `python3 scripts/export_definition_surface.py --check --entrypoint Report`.
