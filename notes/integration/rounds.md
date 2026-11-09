# General finite-menu round foundations

Independent protocol semantics remain in `Definitions/Rounds.lean`. The
initial Boolean gate remains available. The general `Rounds.Game` syntax has
winner leaves and simultaneous-round nodes with an actual nonempty finite
menu `Fin (sizes i + 1)` for each role. Continuations are indexed by complete
joint tuples. Equal continuation trees at different occurrences retain distinct
public prefixes; no strategy sharing or public randomization is inserted.

`Game.Position` is the intrinsic prefix carrier. `current`, `depth`, `path`
and legal `append` specify its meaning. The observed canonical ExecutionProtocol
uses natural-number action labels with exactly the current bounded menus.
Every nonterminal role supplies an action, including forced one-action menus.
The entire completed tuple is publicly disclosed; private signals are unit.
`toFOSG` and `serialized` use the accepted library execution/information models
and explicit-order serializer. No equilibrium or equilibrium recursion is defined
by these wrappers. Refuted mixed open-game composition is not used.

## Complete compiled scope

- `Rounds/Tree` proves finite intrinsic prefixes, exact path/append behavior,
  unique legal histories, perfect recall, finite complete source histories,
  a uniform certified bound and termination.
- `Reachability` proves every intrinsic prefix is actually reachable under legal
  play and every source history is an information-set-closed subgame root.
  There is no reach-probability premise. Public prefixes and actual histories
  are equivalent.
- `SerializationFinite` proves finite source menus, stored partial commitments,
  serialized states and actual histories; the accepted serializer supplies
  unique traces. The resulting serial bound covers every off-path history.
- `SerializationRecall` is generic for FOSGs with source perfect recall.
  It proves the exact serial own-play record, including a current commitment
  after its slot, and transfers recall at genuine decision sites. Inactive
  intermediate observations may forget current commitments; full target perfect
  recall is not asserted.
- `SerializationTrace` constructs actual target traces for every literal source
  history and every legal partial commitment at a nonterminal public boundary.
- `InformationFibers` identifies an actual serial decision fiber with precisely
  the earlier legal current commitments, with its public source history fixed.
  This is an equivalence of complete histories, not an outcome-law projection.
- `SequentialExistence` supplies total legal fallback policies and applies the
  existing independent GameTheory finite sequential-equilibrium theorem to this
  actual implementation, for arbitrary utilities.
- `PrefixLaw` constructs the ordered independent probability product of the
  scheduled local laws on the actual stored prefixes. Appending a commitment is
  a proved pair equivalence; exact masses multiply. These products preserve
  pointwise convergence. This is a probability-law construction, not a new
  solution predicate.

Root `Paper.round_protocol_foundations` repeats finite histories, reachability,
proper public subgames, both recall premises, certified source/serial bounds,
and canonical sequential-equilibrium existence. It does not claim the complete
round proposition.

## Remaining required scope

The prefix probability product still needs its exact Bayes/reach-factor bridge,
including cancellation at fully mixed approximations to unreachable public
histories. Limit consistency and sequential rationality must connect serial SE
to observed mixed SPE. The full mixed-SPE recurrence, common winner-value set,
public support conservativity, concrete scalar games, rational synthesis,
no finite compositional winner algebra and scalar full abstraction remain.
Existing scalar arithmetic certificates alone do not discharge these claims.

## Validation

Each module builds strictly against the pinned 4.35.0 dependencies.
`tests/RoundTrees.lean` exercises changing asymmetric menus (2×1 followed by
1×3), distinct copies of equal continuations, rejected unavailable labels,
actual off-path prefixes, finite canonical histories, recall, arbitrary-utility
SE existence and exact decision fibers. The principal existence/recall/fiber
results print only the standard three axioms. The root integration audit covers
all authored declarations and the separate pure algebra boundary.
