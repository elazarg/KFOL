module

public import KFOL.Rounds.Scalar.Distribution
public import GameTheory.Math.Probability.Product
public import Mathlib.Logic.Equiv.Fin.Basic

/-! # Exact two-coordinate laws of actual independent finite menu profiles -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game.Scalar

open GameTheory GameTheory.Math.Probability

universe u
variable {Role : Type u}

/-- The two designated active roles as an actual injective coordinate map. -/
def twoRoles (a b : Role) (hab : a ≠ b) : Fin 2 ↪ Role where
  toFun j := if j = 0 then a else b
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

@[simp] theorem twoRoles_zero (a b : Role) (hab : a ≠ b) : twoRoles a b hab 0 = a := rfl
@[simp] theorem twoRoles_one (a b : Role) (hab : a ≠ b) : twoRoles a b hab 1 = b := rfl

/-- The bit is true exactly for menu index zero. This definition applies to
actual menus of any size and never introduces a fictitious action. -/
def zeroBit {n : ℕ} (action : Fin (n+1)) : Bool := decide (action.val = 0)

/-- The two actual bits sampled by the designated roles. -/
def twoBits (a b : Role) (hab : a ≠ b) {sizes : Role → ℕ}
    (actions : (i : Role) → Fin (sizes i+1)) : Fin 2 → Bool :=
  fun j => zeroBit (actions (twoRoles a b hab j))

/-- Projection onto the two designated bits preserves their independent law;
all additional roles, including inactive roles, disappear by actual marginalization. -/
theorem independentProduct_twoBits [Fintype Role] (a b : Role) (hab : a ≠ b)
    (sizes : Role → ℕ) (profile : (i : Role) → PMF (Fin (sizes i+1))) :
    (independentProduct profile).map (twoBits a b hab) =
      independentProduct (fun j => (profile (twoRoles a b hab j)).map zeroBit) := by
  calc
    _ = ((independentProduct profile).map (fun actions j => actions (twoRoles a b hab j))).map
        (fun actions j => zeroBit (actions j)) := by
      rw [PMF.map_comp]
      rfl
    _ = _ := by
      rw [independentProduct_map_embedding,independentProduct_map]

/-- The two-bit diagonal continuation table on actual winner laws. -/
def bitKernel (b : Role) (left right : PMF Role) (bits : Fin 2 → Bool) : PMF Role :=
  if bits 0 then if bits 1 then left else PMF.pure b
  else if bits 1 then PMF.pure b else right

/-- Exhaustive expansion of the actual four-point independent bit law. -/
theorem bitKernel_bind_apply (b who : Role) (left right : PMF Role)
    (laws : Fin 2 → PMF Bool) :
    ((independentProduct laws).bind (bitKernel b left right)) who =
      laws 0 true * laws 1 true * left who +
      laws 0 false * laws 1 false * right who +
      (laws 0 true * laws 1 false + laws 0 false * laws 1 true) * (PMF.pure b who) := by
  rw [PMF.bind_apply,← (finTwoArrowEquiv Bool).symm.tsum_eq]
  simp only [tsum_fintype,Fintype.sum_prod_type,Fintype.sum_bool,independentProduct_apply,
    Fin.prod_univ_two,finTwoArrowEquiv_symm_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    bitKernel,Bool.false_eq_true,ite_false,ite_true]
  ring

end KFOL.Rounds.Game.Scalar
