module

import KFOL.Rounds.Observed.RootLaw
noncomputable section

namespace KFOL.ObservedRunRegression

open Rounds Rounds.Game Rounds.Game.Observed GameTheory.Protocol GameTheory.Math.Probability

universe u

/-- Complete canonical first-round law, with actual menus, all continuations
and independent local root laws written out. -/
theorem canonical_round_winner {Role : Type u} [Fintype Role]
    (sizes : Role → ℕ) (next : ((i : Role) → Fin (sizes i+1)) → Game Role)
    (profile : (i : Role) → (Game.round sizes next).information.BehavioralPolicy i)
    (fuel : Nat) :
    ((Game.round sizes next).information.runBehavioralFrom profile (fuel+1)
      (Game.round sizes next).execution.initHistory).map (Game.round sizes next).winner =
    (independentProduct (fun i => rootLaw sizes next i (profile i))).bind fun a =>
      ((next a).information.runBehavioralFrom
        (fun i => restrictChild sizes next i (profile i) a) fuel
        (next a).execution.initHistory).map (next a).winner :=
  runBehavioral_round_winner sizes next profile fuel

/-- Equal child syntax does not identify different child occurrences in the
canonical policy space: every actual tuple retains its own whole policy. -/
example {Role : Type u} (sizes : Role → ℕ) (child : Game Role) (who : Role) :
    (Game.round sizes (fun _ => child)).information.BehavioralPolicy who ≃
      (PMF (Fin (sizes who+1)) ×
        (((i : Role) → Fin (sizes i+1)) → child.information.BehavioralPolicy who)) :=
  policyEquiv sizes (fun _ => child) who

example (r : Fin 3) (sizes : Fin 3 → ℕ)
    (profile : (i : Fin 3) → (Game.round sizes (fun _ => .leaf r)).information.BehavioralPolicy i) :
    ((Game.round sizes (fun _ => .leaf r)).information.runBehavioralFrom profile 1
      (Game.round sizes (fun _ => .leaf r)).execution.initHistory).map
        (Game.round sizes (fun _ => .leaf r)).winner = PMF.pure r := by
  rw [runBehavioral_round_winner]
  have he : (fun a : (i : Fin 3) → Fin (sizes i+1) =>
      ((Game.leaf r).information.runBehavioralFrom
        (fun i => restrictChild sizes (fun _ => .leaf r) i (profile i) a) 0
        (Game.leaf r).execution.initHistory).map (Game.leaf r).winner) = fun _ => PMF.pure r := by
    funext a
    change (PMF.pure (Game.leaf r).execution.initHistory).map (Game.leaf r).winner = PMF.pure r
    rw [PMF.pure_map]
    rfl
  rw [he,PMF.bind_const]

end KFOL.ObservedRunRegression

#print axioms KFOL.Rounds.Game.Observed.policyEquiv
#print axioms KFOL.Rounds.Game.Observed.runBehavioral_map_state
#print axioms KFOL.Rounds.Game.Observed.child_run_winner
#print axioms KFOL.Rounds.Game.Observed.runBehavioral_round_winner
