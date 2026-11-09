module

public import KFOL.Rounds.SequentialExistence
public import GameTheory.Math.Probability.Bounds

/-! # Actual sequential-equilibrium winner distributions -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game
open GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Languages.Bridges.FOSGToEFG
universe u
variable {Role : Type u}

/-- Indicator utility is bounded and integrable under every outcome law. -/
theorem winnerPayoff_abs_le_one {Outcome : Type u} (label : Outcome → Role)
    (i : Role) (outcome : Outcome) : |winnerPayoff label i outcome| ≤ 1 := by
  classical
  simp only [winnerPayoff]
  split <;> norm_num

/-- A role's expected utility is exactly its coordinate in the actual winner
distribution. No separately defined numeric evaluator enters this equality. -/
theorem expect_winnerPayoff {Outcome : Type u} (law : PMF Outcome)
    (label : Outcome → Role) (i : Role) :
    expect law (winnerPayoff label i) = ((law.map label) i).toReal := by
  classical
  rw [show winnerPayoff label i = (fun x => if x ∈ {x | label x = i} then (1 : ℝ) else 0) from rfl,
    expect_indicator]
  change (law.toOuterMeasure (label ⁻¹' {i})).toReal = _
  rw [← PMF.toOuterMeasure_map_apply,PMF.toOuterMeasure_apply_singleton]

/-- The readout agrees with the actual winner label at every leaf continuation. -/
theorem winner_at_leaf (game : Game Role) (h : game.execution.History) (r : Role)
    (hh : h.state.current = .leaf r) : game.winner h = r := by
  simp only [winner,hh,defaultWinner]

/-- The paper's independently defined sequential value set is nonempty. -/
theorem sequentialValues_nonempty [Fintype Role] [DecidableEq Role] (game : Game Role)
    (order : ExplicitOrder Role) : (game.sequentialValues order).Nonempty := by
  obtain ⟨assessment,hse⟩ := game.serial_exists_sequential_equilibrium order
    (winnerPayoff (game.serialWinner order))
  exact ⟨_,game.serial_well_founded_histories order,
    (game.serial_decision_recall order).decisionInformationAntichain,assessment,hse,rfl⟩

theorem winner_leaf (r : Role) (h : (Game.leaf r).execution.History) :
    (Game.leaf r).winner h = r := by
  have he : h.state = .root := by cases h.state; rfl
  simp only [winner,he,Position.current,defaultWinner]

theorem serialWinner_leaf [DecidableEq Role] (r : Role) (order : ExplicitOrder Role)
    (h : ((Game.leaf r).serialized order).execution.History) :
    (Game.leaf r).serialWinner order h = r :=
  winner_leaf r _

/-- The leaf equation holds for the canonical serial SE values, not merely for
an arithmetic evaluator. -/
theorem sequentialValues_leaf [Fintype Role] [DecidableEq Role] (r : Role)
    (order : ExplicitOrder Role) : (Game.leaf r).sequentialValues order = {PMF.pure r} := by
  have hall : ∀ value ∈ (Game.leaf r).sequentialValues order, value = PMF.pure r := by
    intro value hval
    obtain ⟨certificate,antichain,assessment,_hse,rfl⟩ := hval
    have hlabel : (Game.leaf r).serialWinner order =
        Function.const ((Game.leaf r).serialized order).execution.History r :=
      funext (serialWinner_leaf r order)
    rw [hlabel,PMF.map_const]
  ext value
  constructor
  · exact fun hv => Set.mem_singleton_iff.mpr (hall value hv)
  · intro hv
    obtain ⟨w,hw⟩ := (Game.leaf r).sequentialValues_nonempty order
    have he := hall w hw
    simpa only [Set.mem_singleton_iff.mp hv,he] using hw

end KFOL.Rounds.Game
