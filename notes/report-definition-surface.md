# Report theorem-type definition surface

45 public theorem types reach 535 project semantic declarations in 29 source files. 18 of those files are under `KFOL/Definitions`. Generated declarations are grouped into 229 written source review units; 17 derived declarations have file-level locations. Theorem proof bodies are excluded.

This is a review index. Definitions still require human review against the manuscript; the separate proof/axiom and import audits remain necessary.

| Source | Reachable declarations | Central definitions |
| --- | ---: | --- |
| [KFOL/Definitions/Rounds.lean](../KFOL/Definitions/Rounds.lean) | 88 | yes |
| [KFOL/Definitions/Queries.lean](../KFOL/Definitions/Queries.lean) | 59 | yes |
| [KFOL/Definitions/Strategic.lean](../KFOL/Definitions/Strategic.lean) | 56 | yes |
| [KFOL/Definitions/Owner.lean](../KFOL/Definitions/Owner.lean) | 52 | yes |
| [KFOL/Definitions/Equational.lean](../KFOL/Definitions/Equational.lean) | 46 | yes |
| [Report.lean](../Report.lean) | 46 |  |
| [KFOL/Definitions/Circuits.lean](../KFOL/Definitions/Circuits.lean) | 44 | yes |
| [KFOL/Definitions/Quantified.lean](../KFOL/Definitions/Quantified.lean) | 36 | yes |
| [KFOL/Definitions/Reset.lean](../KFOL/Definitions/Reset.lean) | 30 | yes |
| [KFOL/Definitions/CoreBasis.lean](../KFOL/Definitions/CoreBasis.lean) | 29 | yes |
| [KFOL/Definitions/Public.lean](../KFOL/Definitions/Public.lean) | 19 | yes |
| [KFOL/Definitions/Reductions.lean](../KFOL/Definitions/Reductions.lean) | 16 | yes |
| [KFOL/Definitions/Envelope.lean](../KFOL/Definitions/Envelope.lean) | 12 | yes |
| [KFOL/Definitions/Core.lean](../KFOL/Definitions/Core.lean) | 7 | yes |
| [KFOL/Rounds/SerializationTrace.lean](../KFOL/Rounds/SerializationTrace.lean) | 7 |  |
| [KFOL/Definitions/PaperGames.lean](../KFOL/Definitions/PaperGames.lean) | 6 | yes |
| [KFOL/Rounds/PrefixLaw.lean](../KFOL/Rounds/PrefixLaw.lean) | 6 |  |
| [KFOL/Core/Locality.lean](../KFOL/Core/Locality.lean) | 4 |  |
| [KFOL/Definitions/Relational.lean](../KFOL/Definitions/Relational.lean) | 3 | yes |
| [KFOL/Rounds/DecisionSites.lean](../KFOL/Rounds/DecisionSites.lean) | 3 |  |
| [KFOL/Core/Quotients.lean](../KFOL/Core/Quotients.lean) | 2 |  |
| [KFOL/Definitions/CoreFunctions.lean](../KFOL/Definitions/CoreFunctions.lean) | 2 | yes |
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
- Lean/Std: 148 boundary constants.
- mathlib: 122 boundary constants.

Review per public theorem:

| Public theorem | Semantic declarations | Project modules |
| --- | ---: | ---: |
| [arbitrary_public_quantifier](../Report.lean#L356) | 21 | 1 |
| [boolean_threshold_state_lower_bound](../Report.lean#L231) | 45 | 1 |
| [constant_sum_value](../Report.lean#L493) | 43 | 2 |
| [core_singleton_profiles](../Report.lean#L24) | 11 | 3 |
| [core_typed_upper_clone_cover](../Report.lean#L96) | 46 | 6 |
| [core_variable_bound_obstruction](../Report.lean#L67) | 53 | 4 |
| [expanded_variety_envelope](../Report.lean#L463) | 51 | 4 |
| [finite_powerset_relational_representation](../Report.lean#L404) | 2 | 1 |
| [idempotency_certificates](../Report.lean#L31) | 19 | 1 |
| [intersection_not_definable](../Report.lean#L457) | 18 | 1 |
| [native_nonfinite_basis](../Report.lean#L136) | 36 | 2 |
| [owned_choice_relational_representation](../Report.lean#L442) | 6 | 2 |
| [owned_choice_zero_extension](../Report.lean#L417) | 5 | 2 |
| [owned_choice_zero_representation](../Report.lean#L431) | 7 | 2 |
| [owner_four_variable_obstruction](../Report.lean#L85) | 62 | 2 |
| [pair_game_boolean_full_abstraction](../Report.lean#L210) | 78 | 1 |
| [permutation_envelope_cardinality](../Report.lean#L476) | 1 | 1 |
| [public_choice_small_support](../Report.lean#L275) | 57 | 3 |
| [public_choice_support_sharp](../Report.lean#L284) | 32 | 1 |
| [public_equilibrium_strategic_form](../Report.lean#L121) | 40 | 1 |
| [public_nonidempotence](../Report.lean#L485) | 42 | 2 |
| [public_query_compilation](../Report.lean#L389) | 80 | 3 |
| [public_query_equivalence](../Report.lean#L397) | 74 | 4 |
| [public_term_interpretation](../Report.lean#L130) | 54 | 3 |
| [reciprocal_values](../Report.lean#L506) | 46 | 2 |
| [reset_circuit_exponential_tables](../Report.lean#L294) | 42 | 3 |
| [reset_circuit_generator](../Report.lean#L346) | 36 | 4 |
| [reset_circuit_reduction](../Report.lean#L335) | 70 | 5 |
| [reset_circuit_tree_succinctness](../Report.lean#L303) | 58 | 5 |
| [reset_family_product](../Report.lean#L61) | 15 | 2 |
| [reset_no_relational_representation](../Report.lean#L450) | 5 | 2 |
| [reset_substitution](../Report.lean#L50) | 24 | 3 |
| [reset_table_size](../Report.lean#L364) | 21 | 2 |
| [round_product_beliefs](../Report.lean#L177) | 45 | 5 |
| [round_profile_consistency](../Report.lean#L164) | 45 | 5 |
| [round_protocol_foundations](../Report.lean#L148) | 28 | 1 |
| [scalar_contextual_equivalence](../Report.lean#L512) | 74 | 2 |
| [scalar_diagonal_security](../Report.lean#L258) | 4 | 2 |
| [scalar_diagonal_values](../Report.lean#L499) | 44 | 2 |
| [scalar_parallel_laws](../Report.lean#L188) | 0 | 0 |
| [scalar_rational_observation_order](../Report.lean#L243) | 64 | 1 |
| [scalar_rational_values](../Report.lean#L198) | 63 | 1 |
| [serial_order_independence](../Report.lean#L330) | 39 | 2 |
| [two_player_forcing_coordinates](../Report.lean#L370) | 6 | 2 |
| [well_founded_quantifier_fold](../Report.lean#L321) | 60 | 2 |

The JSON contains every theorem's complete project slice, exact declaration/type/body edges, external interface types, declaration locations and source fingerprints.

Reproduce with `python3 scripts/export_definition_surface.py --check --entrypoint Report`.
