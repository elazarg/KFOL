# Canonical observed mixed-SPE round recursion

The complete canonical observed mixed-SPE leaf/round recursion and existence
are now proved and compiled in production. The sequential/observed equivalence
is a separate root-owned bridge; it is not claimed by this package alone.

## Independent semantic boundary

The approved narrow append to `Definitions/Rounds.lean` defines `Game.stageForm`
using actual menu indices `Fin (sizes i+1)` and continuation winner PMFs.
`Game.roundOperator` selects one value at every actual joint tuple, then takes
canonical independent mixed Nash winner laws. Its utility is the indicator
`fun winner i => winnerPayoff id i winner` with the original payoff argument
order respected. Neither this operator nor the independently defined
`observedValues` contains a recursive equilibrium predicate.

## Canonical run-law foundation

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

The production live build through RootLaw passes 3190 jobs. Strict
`tests/ObservedRun.lean` repeats the complete root-law statement and checks
repeated equal-child policy carriers and a one-round deterministic leaf law.
Temporary `/tmp/kfol-observed-audit.lean` imports all authored declarations of
these modules plus the shared independent round definitions, including private
helpers, and checks standard-three axioms: all 160 declarations pass.

## Complete equilibrium recursion

- `Profiles.lean` proves whole-profile root/child construction and preservation
  of unilateral policy replacement through both projections.
- `Optimality.lean` proves canonical Nash and observed SPE are exactly the
  inequalities of actual winner-PMF coordinates, including all indicator
  integrability proofs. Every actual public history is a proper subgame.
- `Children.lean` lifts a deviation in one child occurrence to a whole parent
  policy, deriving canonical SPE in every child, including zero-reach children.
- `StageNecessity.lean` lifts arbitrary root-law replacements with all child
  policies fixed, deriving canonical mixed Nash of the actual finite stage
  and the forward observed-value inclusion.
- `Bounds.lean` proves certified-fuel independence of actual canonical laws
  and monotonicity of a winner coordinate under arbitrary PMF mixtures.
- `Sufficiency.lean` proves the reverse whole-policy implication. An arbitrary
  deviation is no better in each actual child by child SPE, hence no better
  in its mixture by PMF monotonicity, and no better at the root by stage Nash.
  Future public histories are handled through actual child transport.
- `Leaf.lean` constructs a concrete canonical terminal profile and proves
  `observedValues_leaf = {PMF.pure r}`, including the valid zero-fuel witness.
- `Recursion.lean` proves the complete set equality `observedValues_round`
  and the fully expanded selected-continuation `observedValues_round_iff`.
  Arbitrary child certificates are normalized to the parent's certified
  `bound-1` before assembling its actual canonical policies.
- `Existence.lean` proves every actual finite stochastic stage has canonical
  mixed Nash (reusing the library theorem with indicator integrability proved),
  then proves `observedValues_nonempty` by induction through the exact recursion.

The public umbrella is `KFOL/Rounds/Observed.lean`. All statements require at
most `[Fintype Role] [DecidableEq Role]`; there is no K≥3 assumption. The exact
recursion quantifies over every actual joint Fin-menu tuple, with an actual
canonical child SPE witness for each, even when syntax repeats or its root
probability is zero. No recursive equilibrium predicate, outside-result
hypothesis, certificate assumption or separate unconnected value evaluator
is introduced.

Live build through Existence: 3820 jobs, success. Strict
`tests/ObservedRecursion.lean` repeats the complete leaf/round proposition,
checks the one-player value set and nonempty values with repeated equal-child
syntax, and prints standard-three axiom dependencies. The expanded temporary
`/tmp/kfol-observed-audit.lean` imports every authored source with `import all`
and checks all 200 declarations' transitive axioms: standard-three-only audit
passes.

Root owns the serial product-Bayes/sequential-equilibrium equivalence. The
separate SerialRun workstream supplies actual finite-prefix and product-belief
terminal-deviation run bridges for that argument.
