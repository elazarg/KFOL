# Canonical scalar diagonal and reciprocal games

The actual two-bit diagonal constructor and linear reciprocal games now have
complete canonical sequential-equilibrium winner-distribution theorems.
The exact main-paper threshold formula and its finite-summary/contextual-index
obstruction are also proved in production.

The approved independent append in `Definitions/Rounds.lean` adds exactly the
actual finite menus, diagonal/public-choice constructors, reciprocal games,
threshold games and possible-winner observation. Threshold indexing is exactly
`Fₘ[Gₙ] = publicChoice a (reciprocal a b (n+1)) (reciprocal a c (m+1))`, so the
corresponding denominators are `n+2` and `m+2`.

## Compiled proof modules

- `Scalar/Distribution.lean`: actual two-winner PMF mixtures, exact coordinates,
  and reconstruction from one real coordinate plus proved pair support.
- `Scalar/Binary.lean`: actual independent finite-menu profiles marginalized
  onto the two designated active bits; complete four-point PMF expansion.
- `Scalar/Diagonal.lean`: actual canonical mixed play equals the independent
  two-bit law bound to the diagonal continuation table. Its exact row payoff,
  complementary column payoff and absence of third-role mass are proved.
- `Scalar/Nash.lean`: the four actual pure unilateral deviations force the
  parallel-sum value in every canonical mixed Nash equilibrium. Both-zero and
  either single-zero entry are covered; no independent Nash definition or
  minimax hypothesis is introduced.
- `Scalar/Arithmetic.lean`: complete nonnegative parallel-sum arithmetic,
  including all zero cases, associativity, commutativity, monotonicity,
  absorption, min/max distribution and the reciprocal induction step.
- `Scalar/Values.lean`: every canonical stage Nash has the complete singleton
  parallel-sum distribution; the actual canonical `roundOperator` has exactly
  that singleton; the actual diagonal game's independently defined observed
  SPE values have that singleton when its continuations do.
- `Scalar/Reciprocal.lean`: the already proved canonical SE/SPE bridge gives
  `sequentialValues_diagonal`; induction on the actual finite game syntax
  proves observed and sequential reciprocal singleton laws for every `n`,
  including `n=0`, with exact row and column mass formulas.

The scalar is `parallel x y = x*y/(x+y)`; field division makes the both-zero
case zero, and its valid probability bounds are proved. Distinctness is needed
only for the designated two roles. The semantic theorems require
`[Fintype Role] [DecidableEq Role]`, with no three-role assumption or positive
reach condition. Extra inactive roles are marginalized through the actual
product law, not silently removed from the game.

The production build through Reciprocal passes 3849 jobs. Strict
`tests/ScalarDiagonal.lean` repeats the complete actual serial-game proposition,
checks the zero matrix, reciprocal zero case, matching-pennies half law, and
next reciprocal coordinate. All-source transitive axiom audit of all seven
modules, including private helpers, checks all 83 declarations and permits
only `propext`, `Classical.choice` and `Quot.sound`.

## Threshold and infinite observation index

`Scalar/Threshold.lean` derives forced singleton outcomes under strict owner
preference and exact possible-winner support union at indifference, directly
from the independently proved canonical public-choice value equation.
`Scalar/Support.lean` proves every actual `Gₙ = Lₙ₊₁` has possible winners
exactly `{a,b}`. `Scalar/Infinite.lean` proves the complete actual SE formula
for `Fₘ[Gₙ]`: `{a,b}` for `n<m`, `{a,b,c}` for `n=m`, and `{a,c}` for `n>m`.
It also proves third-role possibility is exactly `m≤n`.

`Scalar/Contexts.lean` proves actual canonical SE value equality is a
congruence for every finite round context, with independent repeated holes.
It constructs the literal threshold context and proves two impossibility
statements for arbitrary universe-polymorphic finite carriers:

- `no_finite_winner_algebra` assumes only congruence under the paper's actual
  public-choice threshold contexts and adequacy for third-role possible SE
  victory, and derives a contradiction.
- `no_finite_contextual_summary` states the same obstruction directly in terms
  of adequacy under every actual round context.

Their proofs make the actual reciprocal-game encoding injective by the proved
canonical SE threshold observations and then contradict finiteness. There is
no arithmetic-probe adequacy assumption detached from games. The three roles
are pairwise distinct only where the third-role observation needs that fact.

Production build through Contexts passes 3856 jobs. Strict
`tests/ScalarThreshold.lean` repeats the complete main formula and the
contextual finite-carrier obstruction, and exercises all three comparison
branches on the actual three-role canonical serial game semantics.

## Rational generation and full abstraction

The approved `ScalarTerm` syntax and its actual game compiler are in the
independent definition file. It includes leaves, diagonal, role exchange and
public maximum/minimum; its definition contains no equilibrium evaluator.
`Scalar/Rational.lean` proves every term's rational `rate` is in `[0,1]` and
proves the complete canonical serial-SE singleton distribution of its actual
compiled game by induction through the established semantic recursion.
`Scalar/Extrema.lean` supplies the exact maximum/minimum scalar semantics,
including tie boundaries and independent continuation occurrences.

`Scalar/Synthesis.lean` proves exact denominator-decreasing synthesis for
unreduced fractions and for every rational in `[0,1]`. Its `UnaryGenerated`
witness certifies only leaves, complement and the one-occurrence step were
used. Both full syntax and this smaller constructor set have exactly the
rational unit interval as their range. `exists_rational_game` connects that
synthesis to actual finite-menu games and their actual canonical SE laws.

`Scalar/FullAbstraction.lean` synthesizes the strict rational midpoint between
unequal rates as a closed rival on the third role, then constructs an actual
public round context separating the two components. It proves rate equality
iff the third role's possible SE victory agrees in every actual round context,
and equivalently iff the complete possible-winner sets agree. General contexts
may contain repeated holes; their instantiated occurrences retain independent
policies through the established all-round value-set congruence.

`Scalar/Fragment.lean` proves literal `UsesOnly` symmetry and constructor
closure, every reciprocal and compiled scalar term's two-role restriction,
and explicit Boolean-menu restrictions for reciprocal, threshold and all
compiled scalar games. These are syntactic properties, with no equilibrium
predicate assumed in their definitions.

Production build through FullAbstraction passes 3860 jobs. Strict
`tests/ScalarRational.lean` repeats the complete single-observer contextual
full-abstraction proposition, checks unreduced rational synthesis against the
actual canonical SE value set, complementary/public-extrema rates, actual
endpoint separation, and the finite-menu fragment restrictions with additional
inactive roles.

The final all-source transitive axiom audit imports all 16 Scalar modules and
checks all 230 authored declarations, including private helpers and fragment
properties: every declaration uses only `propext`, `Classical.choice`, and
`Quot.sound`. All three strict scalar regression files pass.
