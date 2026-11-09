module

public import KFOL.Rounds.Scalar.Binary
public import KFOL.Rounds.Observed.Existence

/-! # The actual diagonal stage has the parallel-sum winner distribution -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game.Scalar

open GameTheory GameTheory.Math.Probability

universe u
variable {Role : Type u}

/-- The two actual bit masses have complementary real coordinates. -/
theorem bit_false_toReal (law : PMF Bool) :
    (law false).toReal = 1-(law true).toReal := by
  have hm : law true + law false = 1 := by
    simpa only [tsum_fintype,Fintype.sum_bool] using law.tsum_coe
  have hr := congrArg ENNReal.toReal hm
  rw [ENNReal.toReal_add (law.apply_ne_top true) (law.apply_ne_top false)] at hr
  norm_num at hr
  linarith

/-- The exact actual winner coordinate is the familiar bilinear diagonal
payoff, after marginalizing every other role from the canonical product law. -/
theorem bitKernel_coordinate (a b : Role) (hab : a ≠ b) (x y : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (laws : Fin 2 → PMF Bool) :
    (((independentProduct laws).bind (bitKernel b
      (distribution a b x hx0 hx1) (distribution a b y hy0 hy1))) a).toReal =
      x * (laws 0 true).toReal * (laws 1 true).toReal +
      y * (1-(laws 0 true).toReal) * (1-(laws 1 true).toReal) := by
  rw [bitKernel_bind_apply]
  simp only [PMF.pure_apply,ite_eq_right hab,mul_zero,add_zero]
  rw [ENNReal.toReal_add]
  · simp only [ENNReal.toReal_mul,distribution_a a b hab,bit_false_toReal]
    ring
  · exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ((laws 0).apply_ne_top true) ((laws 1).apply_ne_top true))
      ((distribution a b x hx0 hx1).apply_ne_top a)
  · exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ((laws 0).apply_ne_top false) ((laws 1).apply_ne_top false))
      ((distribution a b y hy0 hy1).apply_ne_top a)

/-- No third role gains mass in this actual two-winner diagonal stage. -/
theorem bitKernel_other (a b who : Role) (ha : who ≠ a) (hb : who ≠ b)
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (laws : Fin 2 → PMF Bool) :
    ((independentProduct laws).bind (bitKernel b
      (distribution a b x hx0 hx1) (distribution a b y hy0 hy1))) who = 0 := by
  rw [bitKernel_bind_apply]
  simp [distribution_other a b who ha hb,PMF.pure_apply,hb]

section Stage
variable [DecidableEq Role] [Fintype Role]

/-- The actual continuation-law table of the two-bit diagonal constructor. -/
def diagonalTable (a b : Role) (left right : PMF Role)
    (actions : (i : Role) → Fin (binarySizes a b i+1)) : PMF Role :=
  if (actions a).val = 0 then
    if (actions b).val = 0 then left else PMF.pure b
  else if (actions b).val = 0 then PMF.pure b else right

/-- The actual menu-zero marginal of one player's canonical mixed strategy. -/
def zeroProbability {sizes : Role → ℕ}
    (profile : (i : Role) → PMF (Fin (sizes i+1))) (who : Role) : ℝ :=
  ((profile who).map zeroBit true).toReal

/-- Canonical mixed play of the actual finite-menu diagonal stage is exactly
its two independent actual bit marginals bound to the diagonal table. -/
theorem diagonal_stage_play (a b : Role) (hab : a ≠ b) (left right : PMF Role)
    (profile : (i : Role) → PMF (Fin (binarySizes a b i+1))) :
    (stageForm (binarySizes a b) (diagonalTable a b left right)).mixed.play profile =
      (independentProduct (fun j => (profile (twoRoles a b hab j)).map zeroBit)).bind
        (bitKernel b left right) := by
  change (independentProduct profile).bind (diagonalTable a b left right) = _
  rw [← independentProduct_twoBits a b hab,PMF.bind_map]
  congr 1
  funext actions
  by_cases ha : (actions a).val = 0 <;> by_cases hb : (actions b).val = 0 <;>
    simp [diagonalTable,bitKernel,twoBits,twoRoles,zeroBit,ha,hb]

/-- The actual diagonal stage payoff is the bilinear scalar matrix expression. -/
theorem diagonal_stage_coordinate (a b : Role) (hab : a ≠ b) (x y : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (profile : (i : Role) → PMF (Fin (binarySizes a b i+1))) :
    ((stageForm (binarySizes a b) (diagonalTable a b
      (distribution a b x hx0 hx1) (distribution a b y hy0 hy1))).mixed.play profile a).toReal =
      x * zeroProbability profile a * zeroProbability profile b +
      y * (1-zeroProbability profile a) * (1-zeroProbability profile b) := by
  calc
    _ = (((independentProduct (fun j => (profile (twoRoles a b hab j)).map zeroBit)).bind
        (bitKernel b (distribution a b x hx0 hx1) (distribution a b y hy0 hy1))) a).toReal :=
      congrArg (fun law : PMF Role => (law a).toReal)
        (diagonal_stage_play a b hab _ _ profile)
    _ = _ := by
      simpa only [zeroProbability,twoRoles_zero,twoRoles_one] using
        bitKernel_coordinate a b hab x y hx0 hx1 hy0 hy1
          (fun j => (profile (twoRoles a b hab j)).map zeroBit)

/-- All actual mixed profiles of a scalar diagonal stage remain supported on
its designated pair. This conclusion does not assume equilibrium. -/
theorem diagonal_stage_other (a b who : Role) (hab : a ≠ b) (ha : who ≠ a) (hb : who ≠ b)
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (profile : (i : Role) → PMF (Fin (binarySizes a b i+1))) :
    (stageForm (binarySizes a b) (diagonalTable a b
      (distribution a b x hx0 hx1) (distribution a b y hy0 hy1))).mixed.play profile who = 0 := by
  rw [diagonal_stage_play a b hab]
  exact bitKernel_other a b who ha hb x y hx0 hx1 hy0 hy1 _

/-- The column role's actual winner probability complements the row role's. -/
theorem diagonal_stage_complement (a b : Role) (hab : a ≠ b) (x y : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (profile : (i : Role) → PMF (Fin (binarySizes a b i+1))) :
    ((stageForm (binarySizes a b) (diagonalTable a b
      (distribution a b x hx0 hx1) (distribution a b y hy0 hy1))).mixed.play profile b).toReal =
      1 - ((stageForm (binarySizes a b) (diagonalTable a b
        (distribution a b x hx0 hx1) (distribution a b y hy0 hy1))).mixed.play profile a).toReal := by
  let law : PMF Role :=
    (stageForm (binarySizes a b) (diagonalTable a b
      (distribution a b x hx0 hx1) (distribution a b y hy0 hy1))).mixed.play profile
  change (law b).toReal = 1-(law a).toReal
  have hm : law a + law b = 1 := pair_mass_add a b hab law
    (fun who ha hb => diagonal_stage_other a b who hab ha hb x y hx0 hx1 hy0 hy1 profile)
  have hr := congrArg ENNReal.toReal hm
  rw [ENNReal.toReal_add (law.apply_ne_top a) (law.apply_ne_top b)] at hr
  norm_num at hr
  linarith

/-- The second actual menu index of a designated Boolean role. -/
def oneAction (a b who : Role) (hwho : who = a ∨ who = b) : Fin (binarySizes a b who+1) :=
  ⟨1,by simp [binarySizes,hwho]⟩

omit [Fintype Role] in
/-- Pure menu-zero replacement makes its actual zero marginal one. -/
theorem zeroProbability_update_zero (a b who : Role)
    (profile : (i : Role) → PMF (Fin (binarySizes a b i+1))) :
    zeroProbability (Profile.update
      (sig := {Strategy := fun i => PMF (Fin (binarySizes a b i+1)),Outcome := Role})
      profile who (PMF.pure 0)) who = 1 := by
  simp [zeroProbability,Profile.update_same,PMF.pure_map,zeroBit]

omit [Fintype Role] in
/-- Pure menu-one replacement makes its actual zero marginal zero. -/
theorem zeroProbability_update_one (a b who : Role) (hwho : who = a ∨ who = b)
    (profile : (i : Role) → PMF (Fin (binarySizes a b i+1))) :
    zeroProbability (Profile.update
      (sig := {Strategy := fun i => PMF (Fin (binarySizes a b i+1)),Outcome := Role})
      profile who (PMF.pure (oneAction a b who hwho))) who = 0 := by
  simp [zeroProbability,Profile.update_same,PMF.pure_map,zeroBit,oneAction]

omit [Fintype Role] in
/-- A unilateral replacement preserves every other player's bit marginal. -/
theorem zeroProbability_update_other (a b who other : Role) (hne : other ≠ who)
    (profile : (i : Role) → PMF (Fin (binarySizes a b i+1)))
    (alternative : PMF (Fin (binarySizes a b who+1))) :
    zeroProbability (Profile.update
      (sig := {Strategy := fun i => PMF (Fin (binarySizes a b i+1)),Outcome := Role})
      profile who alternative) other = zeroProbability profile other := by
  simp only [zeroProbability,Profile.update_of_ne _ _ hne]

end Stage

end KFOL.Rounds.Game.Scalar
