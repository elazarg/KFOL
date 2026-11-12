# Report theorem-type definition surface

105 public theorem types reach 730 project semantic declarations in 43 source files. 32 of those files are under `KFOL/Definitions`. Generated declarations are grouped into 344 written source review units; 22 derived declarations have file-level locations. Theorem proof bodies are excluded.

This is a review index. Definitions still require human review against the manuscript; the separate proof/axiom and import audits remain necessary.

| Source | Reachable declarations | Central definitions |
| --- | ---: | --- |
| [Report.lean](../Report.lean) | 106 |  |
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
| [KFOL/Definitions/Core.lean](../KFOL/Definitions/Core.lean) | 9 | yes |
| [KFOL/Definitions/CoreCertificates.lean](../KFOL/Definitions/CoreCertificates.lean) | 9 | yes |
| [KFOL/Definitions/CoreGraph.lean](../KFOL/Definitions/CoreGraph.lean) | 9 | yes |
| [KFOL/Definitions/CoreInterpolation.lean](../KFOL/Definitions/CoreInterpolation.lean) | 9 | yes |
| [KFOL/Rounds/SerializationTrace.lean](../KFOL/Rounds/SerializationTrace.lean) | 7 |  |
| [KFOL/Definitions/PaperGames.lean](../KFOL/Definitions/PaperGames.lean) | 6 | yes |
| [KFOL/Definitions/ProfileBounds.lean](../KFOL/Definitions/ProfileBounds.lean) | 6 | yes |
| [KFOL/Definitions/StrategicCounting.lean](../KFOL/Definitions/StrategicCounting.lean) | 6 | yes |
| [KFOL/Rounds/PrefixLaw.lean](../KFOL/Rounds/PrefixLaw.lean) | 6 |  |
| [KFOL/Definitions/CoreCrown.lean](../KFOL/Definitions/CoreCrown.lean) | 5 | yes |
| [KFOL/Core/Locality.lean](../KFOL/Core/Locality.lean) | 4 |  |
| [KFOL/Definitions/AtomicObserver.lean](../KFOL/Definitions/AtomicObserver.lean) | 4 | yes |
| [KFOL/Definitions/CoreAmalgamation.lean](../KFOL/Definitions/CoreAmalgamation.lean) | 4 | yes |
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
- Lean/Std: 163 boundary constants.
- mathlib: 155 boundary constants.

Review per public theorem:

| Public theorem | Semantic declarations | Project modules |
| --- | ---: | ---: |
| [absorbing_winner_budget](../Report.lean#L70) | 23 | 2 |
| [arbitrary_public_quantifier](../Report.lean#L930) | 21 | 1 |
| [atomic_winner_budget](../Report.lean#L65) | 21 | 2 |
| [bichain_projection_fiber](../Report.lean#L234) | 44 | 1 |
| [bichain_projection_fiber_unique](../Report.lean#L241) | 39 | 1 |
| [boolean_threshold_state_lower_bound](../Report.lean#L805) | 45 | 1 |
| [constant_sum_value](../Report.lean#L1067) | 43 | 2 |
| [core_atomic_observer](../Report.lean#L248) | 25 | 3 |
| [core_binary_interpolation](../Report.lean#L114) | 24 | 3 |
| [core_bounded_profile_pair](../Report.lean#L409) | 17 | 4 |
| [core_bounded_profiles](../Report.lean#L430) | 19 | 4 |
| [core_bounded_rainbow_query](../Report.lean#L419) | 20 | 4 |
| [core_closed_hypergraph_basis](../Report.lean#L331) | 23 | 3 |
| [core_colored_graph_guards](../Report.lean#L582) | 52 | 5 |
| [core_colored_graph_representation](../Report.lean#L576) | 30 | 3 |
| [core_crown_ambiguous_family](../Report.lean#L302) | 7 | 2 |
| [core_crown_neutral_sections](../Report.lean#L293) | 14 | 3 |
| [core_cyclic_persistence](../Report.lean#L268) | 23 | 3 |
| [core_exact_profile_point](../Report.lean#L458) | 21 | 4 |
| [core_exponential_locality](../Report.lean#L312) | 22 | 3 |
| [core_five_local_profile_obstruction](../Report.lean#L209) | 24 | 3 |
| [core_four_local_without_minorant](../Report.lean#L203) | 24 | 3 |
| [core_four_valuation_persistence](../Report.lean#L167) | 21 | 2 |
| [core_guard_synthesis](../Report.lean#L106) | 41 | 4 |
| [core_hypergraph_guards](../Report.lean#L352) | 74 | 6 |
| [core_hypergraph_operations](../Report.lean#L341) | 40 | 4 |
| [core_local_interpolation](../Report.lean#L162) | 24 | 3 |
| [core_local_normal_forms](../Report.lean#L131) | 52 | 5 |
| [core_negative_budget_obstructions](../Report.lean#L566) | 21 | 2 |
| [core_neutral_elimination](../Report.lean#L479) | 29 | 3 |
| [core_nonempty_neutral_elimination](../Report.lean#L490) | 31 | 3 |
| [core_observer_amalgamation](../Report.lean#L256) | 30 | 4 |
| [core_omission_independence](../Report.lean#L558) | 21 | 2 |
| [core_output_is_input_union](../Report.lean#L552) | 21 | 2 |
| [core_pairwise_obstruction](../Report.lean#L119) | 26 | 3 |
| [core_peeling_interpolation](../Report.lean#L322) | 30 | 3 |
| [core_pointwise_profile_obstruction](../Report.lean#L469) | 29 | 4 |
| [core_profile_bound_coupling](../Report.lean#L446) | 18 | 4 |
| [core_profile_maximum](../Report.lean#L140) | 22 | 2 |
| [core_profile_nonconvexity](../Report.lean#L152) | 23 | 3 |
| [core_profile_relations](../Report.lean#L367) | 10 | 1 |
| [core_projection_profile_fiber](../Report.lean#L499) | 23 | 3 |
| [core_projection_profile_fiber_union](../Report.lean#L533) | 18 | 1 |
| [core_projection_profile_fiber_unique](../Report.lean#L512) | 5 | 2 |
| [core_projection_profile_lift](../Report.lean#L525) | 23 | 3 |
| [core_projection_profile_nontrivial](../Report.lean#L519) | 5 | 2 |
| [core_single_bound_profiles](../Report.lean#L383) | 16 | 3 |
| [core_single_bound_small_witness](../Report.lean#L396) | 17 | 3 |
| [core_singleton_profiles](../Report.lean#L376) | 11 | 3 |
| [core_source_probe_count](../Report.lean#L100) | 11 | 1 |
| [core_source_reconstruction](../Report.lean#L93) | 42 | 4 |
| [core_ternary_obstruction](../Report.lean#L185) | 31 | 4 |
| [core_three_local_without_minorant](../Report.lean#L197) | 24 | 3 |
| [core_three_valuation_persistence](../Report.lean#L592) | 21 | 2 |
| [core_typed_upper_clone_cover](../Report.lean#L670) | 46 | 6 |
| [core_unbounded_profile_condition](../Report.lean#L440) | 7 | 3 |
| [core_variable_bound_obstruction](../Report.lean#L641) | 53 | 4 |
| [core_whole_input_provenance](../Report.lean#L545) | 21 | 2 |
| [expanded_variety_envelope](../Report.lean#L1037) | 51 | 4 |
| [finite_powerset_relational_representation](../Report.lean#L978) | 2 | 1 |
| [full_no_finite_relation_basis](../Report.lean#L284) | 20 | 2 |
| [full_not_finitely_related](../Report.lean#L276) | 22 | 3 |
| [idempotency_certificates](../Report.lean#L605) | 19 | 1 |
| [intersection_not_definable](../Report.lean#L1031) | 18 | 1 |
| [native_nonfinite_basis](../Report.lean#L710) | 36 | 2 |
| [observer_bichain](../Report.lean#L219) | 38 | 2 |
| [owned_choice_relational_representation](../Report.lean#L1016) | 6 | 2 |
| [owned_choice_zero_extension](../Report.lean#L991) | 5 | 2 |
| [owned_choice_zero_representation](../Report.lean#L1005) | 7 | 2 |
| [owner_four_variable_obstruction](../Report.lean#L659) | 62 | 2 |
| [pair_game_boolean_full_abstraction](../Report.lean#L784) | 78 | 1 |
| [permutation_envelope_cardinality](../Report.lean#L1050) | 1 | 1 |
| [public_choice_small_support](../Report.lean#L849) | 57 | 3 |
| [public_choice_support_sharp](../Report.lean#L858) | 32 | 1 |
| [public_equilibrium_strategic_form](../Report.lean#L695) | 40 | 1 |
| [public_nonidempotence](../Report.lean#L1059) | 42 | 2 |
| [public_query_compilation](../Report.lean#L963) | 80 | 3 |
| [public_query_equivalence](../Report.lean#L971) | 74 | 4 |
| [public_sharp_absorbing_budget](../Report.lean#L84) | 57 | 5 |
| [public_sharp_winner_budget](../Report.lean#L75) | 34 | 4 |
| [public_term_interpretation](../Report.lean#L704) | 54 | 3 |
| [reciprocal_values](../Report.lean#L1080) | 46 | 2 |
| [reset_circuit_exponential_tables](../Report.lean#L868) | 42 | 3 |
| [reset_circuit_generator](../Report.lean#L920) | 36 | 4 |
| [reset_circuit_reduction](../Report.lean#L909) | 70 | 5 |
| [reset_circuit_tree_succinctness](../Report.lean#L877) | 58 | 5 |
| [reset_family_product](../Report.lean#L635) | 15 | 2 |
| [reset_no_relational_representation](../Report.lean#L1024) | 5 | 2 |
| [reset_substitution](../Report.lean#L624) | 24 | 3 |
| [reset_table_size](../Report.lean#L938) | 21 | 2 |
| [round_product_beliefs](../Report.lean#L751) | 45 | 5 |
| [round_profile_consistency](../Report.lean#L738) | 45 | 5 |
| [round_protocol_foundations](../Report.lean#L722) | 28 | 1 |
| [scalar_contextual_equivalence](../Report.lean#L1086) | 74 | 2 |
| [scalar_diagonal_security](../Report.lean#L832) | 4 | 2 |
| [scalar_diagonal_values](../Report.lean#L1073) | 44 | 2 |
| [scalar_parallel_laws](../Report.lean#L762) | 0 | 0 |
| [scalar_rational_observation_order](../Report.lean#L817) | 64 | 1 |
| [scalar_rational_values](../Report.lean#L772) | 63 | 1 |
| [serial_order_independence](../Report.lean#L904) | 39 | 2 |
| [two_player_forcing_coordinates](../Report.lean#L944) | 6 | 2 |
| [well_founded_quantifier_fold](../Report.lean#L895) | 60 | 2 |
| [winner_accounting](../Report.lean#L49) | 25 | 2 |
| [winner_budget_eq_iff](../Report.lean#L60) | 23 | 2 |
| [winner_leaf_mass](../Report.lean#L55) | 18 | 2 |

The JSON contains every theorem's complete project slice, exact declaration/type/body edges, external interface types, declaration locations and source fingerprints.

Reproduce with `python3 scripts/export_definition_surface.py --check --entrypoint Report`.
