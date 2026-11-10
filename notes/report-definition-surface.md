# Report theorem-type definition surface

38 public theorem types reach 472 project semantic declarations in 27 source files. 16 of those files are under `KFOL/Definitions`. Generated declarations are grouped into 204 written source review units; 15 derived declarations have file-level locations. Theorem proof bodies are excluded.

This is a review index. Definitions still require human review against the manuscript; the separate proof/axiom and import audits remain necessary.

| Source | Reachable declarations | Central definitions |
| --- | ---: | --- |
| [KFOL/Definitions/Rounds.lean](../KFOL/Definitions/Rounds.lean) | 86 | yes |
| [KFOL/Definitions/Queries.lean](../KFOL/Definitions/Queries.lean) | 59 | yes |
| [KFOL/Definitions/Strategic.lean](../KFOL/Definitions/Strategic.lean) | 56 | yes |
| [KFOL/Definitions/Equational.lean](../KFOL/Definitions/Equational.lean) | 46 | yes |
| [KFOL/Definitions/Circuits.lean](../KFOL/Definitions/Circuits.lean) | 44 | yes |
| [Report.lean](../Report.lean) | 39 |  |
| [KFOL/Definitions/Quantified.lean](../KFOL/Definitions/Quantified.lean) | 36 | yes |
| [KFOL/Definitions/Reset.lean](../KFOL/Definitions/Reset.lean) | 30 | yes |
| [KFOL/Definitions/CoreBasis.lean](../KFOL/Definitions/CoreBasis.lean) | 26 | yes |
| [KFOL/Definitions/Public.lean](../KFOL/Definitions/Public.lean) | 19 | yes |
| [KFOL/Definitions/Reductions.lean](../KFOL/Definitions/Reductions.lean) | 16 | yes |
| [KFOL/Definitions/Envelope.lean](../KFOL/Definitions/Envelope.lean) | 12 | yes |
| [KFOL/Definitions/Core.lean](../KFOL/Definitions/Core.lean) | 7 | yes |
| [KFOL/Rounds/SerializationTrace.lean](../KFOL/Rounds/SerializationTrace.lean) | 7 |  |
| [KFOL/Rounds/PrefixLaw.lean](../KFOL/Rounds/PrefixLaw.lean) | 6 |  |
| [KFOL/Core/Locality.lean](../KFOL/Core/Locality.lean) | 4 |  |
| [KFOL/Definitions/Relational.lean](../KFOL/Definitions/Relational.lean) | 3 | yes |
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
- Lean/Std: 145 boundary constants.
- mathlib: 119 boundary constants.

Review per public theorem:

| Public theorem | Semantic declarations | Project modules |
| --- | ---: | ---: |
| [arbitrary_public_quantifier](../Report.lean#L338) | 21 | 1 |
| [boolean_threshold_state_lower_bound](../Report.lean#L213) | 45 | 1 |
| [core_typed_upper_clone_cover](../Report.lean#L78) | 46 | 6 |
| [core_variable_bound_obstruction](../Report.lean#L60) | 53 | 4 |
| [expanded_variety_envelope](../Report.lean#L445) | 51 | 4 |
| [finite_powerset_relational_representation](../Report.lean#L386) | 2 | 1 |
| [idempotency_certificates](../Report.lean#L24) | 19 | 1 |
| [intersection_not_definable](../Report.lean#L439) | 18 | 1 |
| [native_nonfinite_basis](../Report.lean#L118) | 36 | 2 |
| [owned_choice_relational_representation](../Report.lean#L424) | 6 | 2 |
| [owned_choice_zero_extension](../Report.lean#L399) | 5 | 2 |
| [owned_choice_zero_representation](../Report.lean#L413) | 7 | 2 |
| [pair_game_boolean_full_abstraction](../Report.lean#L192) | 78 | 1 |
| [permutation_envelope_cardinality](../Report.lean#L458) | 1 | 1 |
| [public_choice_small_support](../Report.lean#L257) | 57 | 3 |
| [public_choice_support_sharp](../Report.lean#L266) | 32 | 1 |
| [public_equilibrium_strategic_form](../Report.lean#L103) | 40 | 1 |
| [public_query_compilation](../Report.lean#L371) | 80 | 3 |
| [public_query_equivalence](../Report.lean#L379) | 74 | 4 |
| [public_term_interpretation](../Report.lean#L112) | 54 | 3 |
| [reset_circuit_exponential_tables](../Report.lean#L276) | 42 | 3 |
| [reset_circuit_generator](../Report.lean#L328) | 36 | 4 |
| [reset_circuit_reduction](../Report.lean#L317) | 70 | 5 |
| [reset_circuit_tree_succinctness](../Report.lean#L285) | 58 | 5 |
| [reset_family_product](../Report.lean#L54) | 15 | 2 |
| [reset_no_relational_representation](../Report.lean#L432) | 5 | 2 |
| [reset_substitution](../Report.lean#L43) | 24 | 3 |
| [reset_table_size](../Report.lean#L346) | 21 | 2 |
| [round_product_beliefs](../Report.lean#L159) | 45 | 5 |
| [round_profile_consistency](../Report.lean#L146) | 45 | 5 |
| [round_protocol_foundations](../Report.lean#L130) | 28 | 1 |
| [scalar_diagonal_security](../Report.lean#L240) | 4 | 2 |
| [scalar_parallel_laws](../Report.lean#L170) | 0 | 0 |
| [scalar_rational_observation_order](../Report.lean#L225) | 64 | 1 |
| [scalar_rational_values](../Report.lean#L180) | 63 | 1 |
| [serial_order_independence](../Report.lean#L312) | 39 | 2 |
| [two_player_forcing_coordinates](../Report.lean#L352) | 6 | 2 |
| [well_founded_quantifier_fold](../Report.lean#L303) | 60 | 2 |

The JSON contains every theorem's complete project slice, exact declaration/type/body edges, external interface types, declaration locations and source fingerprints.

Reproduce with `python3 scripts/export_definition_surface.py --check --entrypoint Report`.
