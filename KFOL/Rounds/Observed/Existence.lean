module

public import KFOL.Rounds.Observed.Recursion
public import GameTheory.Analysis.Nash

/-! # Observed mixed SPE exist by finite-stage Nash and exact recursion -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game.Observed

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

universe u

variable {Role : Type u} [Fintype Role] [DecidableEq Role]

/-- The actual finite stochastic stage has a canonical independent mixed Nash
equilibrium. Indicator-payoff integrability is proved, rather than assumed. -/
theorem stage_exists_nash (sizes : Role → ℕ)
    (p : ((i : Role) → Fin (sizes i+1)) → PMF Role) :
    ∃ root : Profile (stageForm sizes p).sig.mixed,
      IsNash (stageForm sizes p).mixed
        (euPreference (fun winner i => winnerPayoff id i winner)) root := by
  let : ∀ i, Fintype ((stageForm sizes p).sig.Strategy i) :=
    fun i => inferInstanceAs (Fintype (Fin (sizes i+1)))
  let : ∀ i, Nonempty ((stageForm sizes p).sig.Strategy i) :=
    fun i => ⟨(0 : Fin (sizes i+1))⟩
  exact exists_isNash_mixed (F := stageForm sizes p)
    (fun winner i => winnerPayoff id i winner)
    (fun who profile => payoffIntegrable_of_bounded _ _ (winnerPayoff_abs_le_one id who))

/-- Every finite observed round tree has an actual canonical behavioral SPE
winner law. The proof uses the exact proved round equation and the library's
finite-game mixed-Nash existence, not a recursive equilibrium definition. -/
theorem observedValues_nonempty (game : Game Role) : game.observedValues.Nonempty := by
  induction game with
  | leaf r => rw [observedValues_leaf]; exact Set.singleton_nonempty _
  | round sizes next ih =>
    choose p hp using ih
    obtain ⟨root,nash⟩ := stage_exists_nash sizes p
    rw [observedValues_round]
    exact ⟨(stageForm sizes p).mixed.play root,p,hp,root,nash,rfl⟩

end KFOL.Rounds.Game.Observed
