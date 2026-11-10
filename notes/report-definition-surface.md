# Report theorem-type definition surface

33 public theorem types reach 440 project semantic declarations in 25 source files. 14 of those files are under `KFOL/Definitions`. Generated declarations are grouped into 193 written source review units; 15 derived declarations have file-level locations. Theorem proof bodies are excluded.

This is a review index. Definitions still require human review against the manuscript; the separate proof/axiom and import audits remain necessary.

| Source | Reachable declarations | Central definitions |
| --- | ---: | --- |
| [KFOL/Definitions/Rounds.lean](../KFOL/Definitions/Rounds.lean) | 86 | yes |
| [KFOL/Definitions/Queries.lean](../KFOL/Definitions/Queries.lean) | 59 | yes |
| [KFOL/Definitions/Strategic.lean](../KFOL/Definitions/Strategic.lean) | 56 | yes |
| [KFOL/Definitions/Circuits.lean](../KFOL/Definitions/Circuits.lean) | 44 | yes |
| [KFOL/Definitions/Quantified.lean](../KFOL/Definitions/Quantified.lean) | 36 | yes |
| [Report.lean](../Report.lean) | 34 |  |
| [KFOL/Definitions/Reset.lean](../KFOL/Definitions/Reset.lean) | 30 | yes |
| [KFOL/Definitions/Equational.lean](../KFOL/Definitions/Equational.lean) | 29 | yes |
| [KFOL/Definitions/CoreBasis.lean](../KFOL/Definitions/CoreBasis.lean) | 26 | yes |
| [KFOL/Definitions/Public.lean](../KFOL/Definitions/Public.lean) | 19 | yes |
| [KFOL/Definitions/Reductions.lean](../KFOL/Definitions/Reductions.lean) | 16 | yes |
| [KFOL/Definitions/Core.lean](../KFOL/Definitions/Core.lean) | 7 | yes |
| [KFOL/Rounds/SerializationTrace.lean](../KFOL/Rounds/SerializationTrace.lean) | 7 |  |
| [KFOL/Rounds/PrefixLaw.lean](../KFOL/Rounds/PrefixLaw.lean) | 6 |  |
| [KFOL/Core/Locality.lean](../KFOL/Core/Locality.lean) | 4 |  |
| [KFOL/Rounds/DecisionSites.lean](../KFOL/Rounds/DecisionSites.lean) | 3 |  |
| [KFOL/Core/Quotients.lean](../KFOL/Core/Quotients.lean) | 2 |  |
| [KFOL/Definitions/PaperGames.lean](../KFOL/Definitions/PaperGames.lean) | 2 | yes |
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
- Lean/Std: 141 boundary constants.
- mathlib: 113 boundary constants.

Review per public theorem:

| Public theorem | Semantic declarations | Project modules |
| --- | ---: | ---: |
| [arbitrary_public_quantifier](../Report.lean#L337) | 21 | 1 |
| [boolean_threshold_state_lower_bound](../Report.lean#L212) | 45 | 1 |
| [core_typed_upper_clone_cover](../Report.lean#L77) | 46 | 6 |
| [core_variable_bound_obstruction](../Report.lean#L59) | 53 | 4 |
| [idempotency_certificates](../Report.lean#L23) | 19 | 1 |
| [intersection_not_definable](../Report.lean#L400) | 18 | 1 |
| [native_nonfinite_basis](../Report.lean#L117) | 36 | 2 |
| [owned_choice_relational_representation](../Report.lean#L385) | 6 | 2 |
| [pair_game_boolean_full_abstraction](../Report.lean#L191) | 78 | 1 |
| [public_choice_small_support](../Report.lean#L256) | 57 | 3 |
| [public_choice_support_sharp](../Report.lean#L265) | 32 | 1 |
| [public_equilibrium_strategic_form](../Report.lean#L102) | 40 | 1 |
| [public_query_compilation](../Report.lean#L370) | 80 | 3 |
| [public_query_equivalence](../Report.lean#L378) | 74 | 4 |
| [public_term_interpretation](../Report.lean#L111) | 54 | 3 |
| [reset_circuit_exponential_tables](../Report.lean#L275) | 42 | 3 |
| [reset_circuit_generator](../Report.lean#L327) | 36 | 4 |
| [reset_circuit_reduction](../Report.lean#L316) | 70 | 5 |
| [reset_circuit_tree_succinctness](../Report.lean#L284) | 58 | 5 |
| [reset_family_product](../Report.lean#L53) | 15 | 2 |
| [reset_no_relational_representation](../Report.lean#L393) | 5 | 2 |
| [reset_substitution](../Report.lean#L42) | 24 | 3 |
| [reset_table_size](../Report.lean#L345) | 21 | 2 |
| [round_product_beliefs](../Report.lean#L158) | 45 | 5 |
| [round_profile_consistency](../Report.lean#L145) | 45 | 5 |
| [round_protocol_foundations](../Report.lean#L129) | 28 | 1 |
| [scalar_diagonal_security](../Report.lean#L239) | 4 | 2 |
| [scalar_parallel_laws](../Report.lean#L169) | 0 | 0 |
| [scalar_rational_observation_order](../Report.lean#L224) | 64 | 1 |
| [scalar_rational_values](../Report.lean#L179) | 63 | 1 |
| [serial_order_independence](../Report.lean#L311) | 39 | 2 |
| [two_player_forcing_coordinates](../Report.lean#L351) | 6 | 2 |
| [well_founded_quantifier_fold](../Report.lean#L302) | 60 | 2 |

The JSON contains every theorem's complete project slice, exact declaration/type/body edges, external interface types, declaration locations and source fingerprints.

Reproduce with `python3 scripts/export_definition_surface.py --check --entrypoint Report`.
