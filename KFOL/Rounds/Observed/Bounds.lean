module

public import KFOL.Rounds.Observed.Kernel

/-! # Certified-fuel independence and monotonicity of winner mixtures -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game.Observed

open GameTheory.Protocol GameTheory.Math.Probability

universe u v

variable {Role : Type u} [Fintype Role]

/-- Extra certified evaluation fuel does not change the canonical history law. -/
theorem runBehavioral_eq_of_bound (game : Game Role) {bound : Nat}
    (bounded : game.execution.BoundedHorizon bound)
    (profile : (i : Role) → game.information.BehavioralPolicy i)
    (h : game.execution.History) (fuel : Nat) (enough : bound ≤ fuel) :
    game.information.runBehavioralFrom profile fuel h =
      game.information.runBehavioralFrom profile bound h :=
  game.execution.runRandomizedFor_eq_of_bound bounded
    (game.information.randomizedChooser profile) h fuel enough

/-- Any two globally certified fuels give the same actual continuation law. -/
theorem runBehavioral_bounds_eq (game : Game Role) {first second : Nat}
    (firstBound : game.execution.BoundedHorizon first)
    (secondBound : game.execution.BoundedHorizon second)
    (profile : (i : Role) → game.information.BehavioralPolicy i)
    (h : game.execution.History) :
    game.information.runBehavioralFrom profile first h =
      game.information.runBehavioralFrom profile second h := by
  exact (runBehavioral_eq_of_bound game firstBound profile h (max first second) (Nat.le_max_left _ _)).symm.trans
    (runBehavioral_eq_of_bound game secondBound profile h (max first second) (Nat.le_max_right _ _))

omit [Fintype Role] in
/-- A mixture preserves a pointwise inequality in any one winner coordinate.
No integrability or strictly positive branch mass is required. -/
theorem bind_winner_coordinate_mono {Index : Type v} (law : PMF Index)
    (p q : Index → PMF Role) (who : Role)
    (h : ∀ a, ((p a) who).toReal ≤ ((q a) who).toReal) :
    ((law.bind p) who).toReal ≤ ((law.bind q) who).toReal := by
  apply (ENNReal.toReal_le_toReal (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mpr
  simp only [PMF.bind_apply]
  apply ENNReal.tsum_le_tsum
  intro a
  exact mul_le_mul_right ((ENNReal.toReal_le_toReal
    (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp (h a)) _

end KFOL.Rounds.Game.Observed
