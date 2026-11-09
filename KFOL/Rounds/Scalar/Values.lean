module

public import KFOL.Rounds.Scalar.Nash
public import KFOL.Rounds.Scalar.Arithmetic

/-! # Canonical diagonal round values are singleton parallel-sum laws -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game.Scalar

open GameTheory GameTheory.Math.Probability

universe u
variable {Role : Type u} [DecidableEq Role] [Fintype Role]

/-- Every actual Nash outcome of the scalar diagonal stage is its complete
parallel-sum distribution, not merely an unconnected scalar certificate. -/
theorem diagonal_nash_distribution (a b : Role) (hab : a ≠ b) (x y : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (profile : (i : Role) → PMF (Fin (binarySizes a b i+1)))
    (nash : IsNash (stageForm (binarySizes a b) (diagonalTable a b
      (distribution a b x hx0 hx1) (distribution a b y hy0 hy1))).mixed
      (euPreference (fun winner i => winnerPayoff id i winner)) profile) :
    (stageForm (binarySizes a b) (diagonalTable a b
      (distribution a b x hx0 hx1) (distribution a b y hy0 hy1))).mixed.play profile =
      distribution a b (parallel x y) (parallel_nonneg x y hx0 hy0)
        (parallel_le_one x y hx0 hx1 hy0) := by
  let law : PMF Role :=
    (stageForm (binarySizes a b) (diagonalTable a b
      (distribution a b x hx0 hx1) (distribution a b y hy0 hy1))).mixed.play profile
  have he : law = distribution a b (law a).toReal ENNReal.toReal_nonneg
      (pmf_toReal_apply_le_one law a) :=
    eq_distribution a b hab law
      (fun who ha hb => diagonal_stage_other a b who hab ha hb x y hx0 hx1 hy0 hy1 profile)
  have hv : (law a).toReal = parallel x y :=
    diagonal_nash_value a b hab x y hx0 hx1 hy0 hy1 profile nash
  change law = _
  rw [he]
  simp only [hv]

/-- The canonical round operator applied to the four actual diagonal
continuation laws has exactly the parallel-sum winner distribution.
The formula covers `x=y=0` as well as either single-zero boundary. -/
theorem diagonal_roundOperator (a b : Role) (hab : a ≠ b) (x y : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    roundOperator (binarySizes a b)
      (fun actions => {(diagonalTable a b (distribution a b x hx0 hx1)
        (distribution a b y hy0 hy1) actions)}) =
      {distribution a b (parallel x y) (parallel_nonneg x y hx0 hy0)
        (parallel_le_one x y hx0 hx1 hy0)} := by
  let table := diagonalTable a b (distribution a b x hx0 hx1) (distribution a b y hy0 hy1)
  have unique {law : PMF Role}
      (hlaw : law ∈ roundOperator (binarySizes a b) (fun actions => {table actions})) :
      law = distribution a b (parallel x y) (parallel_nonneg x y hx0 hy0)
        (parallel_le_one x y hx0 hx1 hy0) := by
    obtain ⟨p,hp,profile,nash,rfl⟩ := hlaw
    have he : p = table := funext fun actions => hp actions
    subst p
    exact diagonal_nash_distribution a b hab x y hx0 hx1 hy0 hy1 profile nash
  apply Set.Subset.antisymm
  · intro law hlaw
    exact unique hlaw
  · intro law hlaw
    obtain rfl := hlaw
    obtain ⟨profile,nash⟩ := Observed.stage_exists_nash (binarySizes a b) table
    have hmem : (stageForm (binarySizes a b) table).mixed.play profile ∈
        roundOperator (binarySizes a b) (fun actions => {table actions}) :=
      ⟨table,(fun _ => rfl),profile,nash,rfl⟩
    rw [unique hmem] at hmem
    exact hmem

/-- The actual diagonal game constructor combines independently certified
canonical continuation values into the singleton parallel-sum distribution. -/
theorem observedValues_diagonal (a b : Role) (hab : a ≠ b) (left right : Game Role)
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hleft : left.observedValues = {distribution a b x hx0 hx1})
    (hright : right.observedValues = {distribution a b y hy0 hy1}) :
    (diagonal a b left right).observedValues =
      {distribution a b (parallel x y) (parallel_nonneg x y hx0 hy0)
        (parallel_le_one x y hx0 hx1 hy0)} := by
  unfold diagonal
  rw [Observed.observedValues_round]
  have he : (fun actions : (i : Role) → Fin (binarySizes a b i+1) =>
      (if (actions a).val = 0 then
        if (actions b).val = 0 then left else .leaf b
      else if (actions b).val = 0 then .leaf b else right).observedValues) =
      fun actions => {(diagonalTable a b (distribution a b x hx0 hx1)
        (distribution a b y hy0 hy1) actions)} := by
    funext actions
    by_cases ha : (actions a).val = 0 <;> by_cases hb : (actions b).val = 0 <;>
      simp [ha,hb,diagonalTable,hleft,hright,Observed.observedValues_leaf]
  rw [he]
  exact diagonal_roundOperator a b hab x y hx0 hx1 hy0 hy1

end KFOL.Rounds.Game.Scalar
