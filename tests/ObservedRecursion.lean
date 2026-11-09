module

import KFOL.Rounds.Observed.Existence

namespace KFOL.ObservedRecursionRegression

open Rounds Rounds.Game Rounds.Game.Observed GameTheory GameTheory.Protocol GameTheory.Math.Probability

universe u

/-- Complete actual observed-SPE leaf and round equations, with the latter
fully exposing selection at every tuple and canonical mixed Nash. -/
theorem observed_recursion {Role : Type u} [Fintype Role] [DecidableEq Role]
    (sizes : Role → ℕ) (next : ((i : Role) → Fin (sizes i+1)) → Game Role)
    (value : PMF Role) :
    (∀ r : Role, (Game.leaf r).observedValues = {PMF.pure r}) ∧
    (value ∈ (Game.round sizes next).observedValues ↔
      ∃ p : ((i : Role) → Fin (sizes i+1)) → PMF Role,
        (∀ a, p a ∈ (next a).observedValues) ∧
        ∃ root : Profile (stageForm sizes p).sig.mixed,
          IsNash (stageForm sizes p).mixed
            (euPreference (fun winner i => winnerPayoff id i winner)) root ∧
          value = (stageForm sizes p).mixed.play root) :=
  ⟨observedValues_leaf,observedValues_round_iff sizes next value⟩

example (game : Game (Fin 1)) : game.observedValues = {PMF.pure 0} := by
  ext p
  constructor
  · intro _
    exact Set.mem_singleton_iff.mpr (eq_pure_of_subsingleton p 0)
  · intro hp
    obtain ⟨q,hq⟩ := observedValues_nonempty game
    have hqp : q = p := (eq_pure_of_subsingleton q 0).trans (Set.mem_singleton_iff.mp hp).symm
    exact hqp ▸ hq

example (sizes : Fin 3 → ℕ) (child : Game (Fin 3)) :
    (Game.round sizes (fun _ => child)).observedValues.Nonempty :=
  observedValues_nonempty _

end KFOL.ObservedRecursionRegression

#print axioms KFOL.Rounds.Game.Observed.observedValues_leaf
#print axioms KFOL.Rounds.Game.Observed.observedValues_round
#print axioms KFOL.Rounds.Game.Observed.observedValues_nonempty
