# Canonical observed mixed-SPE round recursion

The actual canonical runner's root/child winner-law decomposition is complete.
The equilibrium recursion is still in progress. In particular, the compiled
production slice through `Observed/RootLaw.lean` does not by itself establish
`observedValues_round` or the sequential/observed equivalence.

## Independent semantic boundary

The approved narrow append to `Definitions/Rounds.lean` defines `Game.stageForm`
using actual menu indices `Fin (sizes i+1)` and continuation winner PMFs.
`Game.roundOperator` selects one value at every actual joint tuple, then takes
canonical independent mixed Nash winner laws. Its utility is the indicator
`fun winner i => winnerPayoff id i winner` with the original payoff argument
order respected. Neither this operator nor the independently defined
`observedValues` contains a recursive equilibrium predicate.

## Compiled production through the run-law milestone

- `Observed/Policies.lean`: actual root Choice equivalence to Fin menu indices;
  identity-on-option child Choice equivalences; a genuine playerwise
  `BehavioralPolicy ≃ root PMF × all child policies`. Equal continuation syntax
  at different actual tuples retains independent policy occurrences. Child
  menu equivalences are explicit because Lean does not definitionally identify
  the two stuck `LegalOption` matchers; no action value is changed.
- `Observed/History.lean`: actual child occurrence embeddings between canonical
  complete histories, exact depth/length increment and certified child horizon
  `bound-1`, including every off-path child history.
- `Observed/Kernel.lean`: a public-position kernel that samples independent
  canonical information-local laws and appends the actual tuple. The generic
  GameTheory state-kernel theorem proves exact equality with the canonical
  history runner pushed through its state projection.
- `Observed/Transport.lean`: the one-step kernel and every iterated position law
  commute with each actual child embedding. `child_run_winner` proves exact
  canonical winner-PMF transport at every fuel and every child history.
- `Observed/RootLaw.lean`: `runBehavioral_round_winner` proves the actual canonical
  winner law at fuel `n+1` equals the independent product of actual root menu
  marginals, bound to the actual child canonical winner laws at fuel `n`.

The production live build through RootLaw passes3190 jobs. Strict
`tests/ObservedRun.lean` repeats the complete root-law statement and checks
repeated equal-child policy carriers and a one-round deterministic leaf law.
Temporary `/tmp/kfol-observed-audit.lean` imports all authored declarations of
these modules plus the shared independent round definitions, including private
helpers, and checks standard-three axioms: all160 declarations pass.

## Equilibrium continuation

Staged, compiled proof slices additionally establish canonical Nash/SPE iff
actual winner-coordinate inequalities (bounded indicator integrability is
proved), whole-profile update transport, SPE in every off-path child by lifting
one-child whole-policy deviations, root-stage Nash by root-only deviations,
and the observed-value inclusion in the round operator. A concrete canonical
leaf SPE establishes the leaf equation. These remain staged during the root
checkpoint freeze; they must not be counted as a completed two-sided round
recursion. The reverse direction will combine child optimality, monotonicity of
PMF mixtures and local stage Nash to bound every whole-policy deviation.

Root owns the separate serial product-Bayes/sequential-equilibrium bridge.
