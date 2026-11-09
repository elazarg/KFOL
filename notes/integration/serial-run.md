# Canonical serialized prefix and deviation run bridges

All three assigned serial-run targets are proved against the actual canonical
GameTheory history runners. Import `KFOL.Rounds.SerialRun.Terminal`; no shared
semantic definition has been changed by this package.

## Statements and assumptions

`SerialRun.run_prefix` in `Prefix.lean` proves that, for every game, explicit
order, serialized behavioral profile, nonterminal actual public history `h`,
and `n ≤ order.slots`, the actual serialized `runBehavioralFrom profile n`
from `boundaryHistory h` is exactly `Serialization.prefixLaw ... h n` mapped
through `Serialization.historyAtPrefix ... h ht n`. This is equality of PMFs
on complete canonical histories, including `n = 0` and `n = order.slots`, with
no positive-reach assumption. It requires only `[Finite Role] [DecidableEq Role]`.

`SerialRun.prefixLaw_update_before` in `Deviation.lean` proves that replacing
player `who`'s entire serialized policy leaves the actual prefix law unchanged
for every `n ≤ (order.player.symm who).val`. It needs `[DecidableEq Role]`;
there is no reach condition or restriction on the replacement policy.

`SerialRun.productBelief_terminal_deviation` in `Terminal.lean` proves that
the baseline `game.productBelief order profile h ht who`, bound to the actual
canonical serialized terminal runner under `Profile.update profile who
alternative`, and then mapped through `eraseHistory`, equals the actual
canonical source terminal law under the projected replacement profile.
The terminal certificates are the genuine
`game.serial_well_founded_histories order` and `game.well_founded_histories`.
It holds at every nonterminal actual public history, including zero-reach
histories, for `[Fintype Role] [DecidableEq Role]`. The winner-law corollary
`productBelief_terminal_winner_deviation` maps the same actual distributions
through `game.serialWinner order` and `game.winner`. The baseline corollary
`productBelief_terminal_baseline` specializes to self replacement.

## Proof organization

- `Choice.lean` identifies the unique active serialized player's actual local
  behavioral sample with `Serialization.currentLaw`, preserving the underlying
  optional action value. Other players' choices are forced.
- `Step.lean` transports the actual one-step history runner through its state
  projection and proves the exact prefix-advance law.
- `Prefix.lean` inducts over the real finite run. Tree-shaped actual histories
  make their state projection injective, so equality of state laws gives
  equality of complete-history PMFs.
- `Deviation.lean` uses the schedule bijection to show that every earlier slot
  belongs to a different player, and then inducts through the product prefix law.
- `Terminal.lean` identifies the baseline belief pushforward with the changed
  profile's actual pre-slot run, applies the canonical terminal splitting law,
  and then reuses the independently proved all-boundary terminal erasure bridge.

No equilibrium predicate, alternative runner, conditional outside theorem or
unproved certificate is introduced. The final sequential-rationality versus
observed-SPE comparison and value-set equality remain root-owned.

## Validation

The production build of `KFOL.Rounds.SerialRun.Terminal` completes successfully
(3813 jobs). Strict `tests/ObservedSerialRun.lean` repeats the complete prefix
and terminal-deviation propositions and checks the one-player zero-prefix
case; it passes. The temporary all-source transitive axiom audit imports all
five modules, including private helpers: all 38 declarations pass. It permits only `propext`,
`Classical.choice`, and `Quot.sound`.
