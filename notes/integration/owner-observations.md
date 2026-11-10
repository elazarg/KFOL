# Native relative-owner observation frontend

The independently defined owner language in `Definitions/Reductions.lean`
existentially encodes original full owner-signature equations, requires every
H owner to lie in the selected finite family, and universally quantifies an
explicit relation on actual winner-set values. The relation is equality,
one chosen membership implication, or one chosen membership equivalence.
Malformed words and unselected owners are rejected by the actual checker.

`Definitions/Owner.lean` defines `Term.compileObservation observer` on the
same source tree. An H owned by the observer becomes `z.reset (y.reset x)`;
every other H is relabeled to Unit. Each source child appears exactly once.
`Owner/ObservationCompilation` proves the root and raw guard list are
preserved exactly after transporting Unit H to the non-observer role.
Completeness of these guards still uses the independent owner-family bound;
exact guard equality alone does not certify arbitrary multi-owner semantics.

`Complexity/OwnerObservationCompiler` proves a linear original-byte output
bound and actual native polynomial compilation, then transports the complete
one-owner guard annotation machine. `OwnerLanguage` adds a finite Boolean
owner-occurrence fold, the whole-word decoding wrapper, its native P bound,
and a generic coNP upper for every fixed relation on the finite winner algebra.
`OwnerObservationFrontend` proves the full positive branches:

- full equality when the selected owner family has cardinality at most one;
- observer implication when at most one selected owner differs from it;
- observer equivalence under that same relative-owner condition.

`Paper.owner_count_polynomial_branches` repeats their complete original-word
statements. `OwnerHardnessTransport` relabels each native H node once to two actual selected owners, preserving all child occurrences and actual evaluation. `OwnerCountCompleteness` transports the pinned machine-level 3SAT reductions for equality, membership implication and equivalence. Together with the fixed-algebra verifier, these give both hard branches for every selected finite owner family. `Paper.owner_count_dichotomy` repeats the full six-branch statement. The theorem asserts P membership in the small cases and coNP-completeness in the large cases without assuming that those classes differ.

`Owner/JointObservation` proves an explicit four-variable equation agrees at
two owners for every valuation, yet fails at a displayed third-role valuation.
`Paper.joint_owner_observation_failure` repeats the existential equation,
owner-occurrence restrictions, universal two-owner agreement and failed actual
equality. The two tests together do not decide full equality.

Validation: `lake build KFOL.Complexity.OwnerObservationFrontend` passed
2083 jobs; `lake build Paper` passed4465 jobs after consolidating duplicate
withOwner constructor lemmas into `Owner/GuardEncoding`. Regression examples
cover both owners' easy observations, zero/one-owner equality, exact raw guard
compilation and the actual third-role countervaluation. All public declarations
have their standard-axiom guards in Paper.


The hard original-word endpoint uses the same complete full owner-signature
codec as the easy branch; legality is a checked source predicate rather than
an informal promise. Source H syntax has only two ternary operations, with no
primitive reset. Native constructor/fold machines implement the relabeling;
a proved linear byte bound charges source owner headers. All universal
correctness clauses are proved before class transport, including the direction
of the third-role implication. Strict regression examples test both distinct
selected owners and larger families containing the observer.
