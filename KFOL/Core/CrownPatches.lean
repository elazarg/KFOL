module

public import KFOL.Core.CrownBasePatch
public import KFOL.Core.CrownRotation
public import Mathlib.Tactic.NormNum

/-! # Every one-edge deletion of the cyclic obstruction is a core term -/

@[expose] public section
namespace KFOL.Core.Crown

theorem rotate_ne_self (n : ℕ) (i : Fin (n+3)) : finRotate (n+3) i ≠ i := by
  intro he
  have hv := congrArg Fin.val he
  rw [coe_finRotate] at hv
  split_ifs at hv with hi
  · have hval := congrArg Fin.val hi
    simp only [Fin.val_last] at hval
    omega
  · omega

theorem rotate_twice_ne_self (n : ℕ) (i : Fin (n+3)) :
    finRotate (n+3) (finRotate (n+3) i) ≠ i := by
  intro he
  have hsum : i + ((1 : Fin (n+3)) + 1) = i + 0 := by
    simpa only [finRotate_apply, add_assoc, add_zero] using he
  have htwo := add_left_cancel hsum
  have hv := congrArg Fin.val htwo
  norm_num [Fin.val_add, Fin.val_natCast, Nat.mod_eq_of_lt (by omega : 2 < n+3)] at hv

/-- Rotations carry the base patch to every missing edge of the same cycle. -/
theorem exists_patch {Role : Type*} [Fintype Role]
    (three : Fin 3 ↪ Role) (n : ℕ) (h : Fin (n+3)) :
    ∃ t : Term Role (Fin (n+3)), t.IsCore ∧ ∀ v,
      t.eval v = operation (three 1) (three 2) (finRotate (n+3)) {i | i ≠ h} v := by
  classical
  obtain ⟨base, hbase, hvalue⟩ := exists_base_patch three n
  let e := finCycle (h - Fin.last (n+2))
  have he (i : Fin (n+3)) : e (finRotate (n+3) i) = finRotate (n+3) (e i) := by
    simp only [e, finCycle_apply, finRotate_apply]
    simp only [add_assoc, add_left_comm, add_comm]
  have hlast : e (Fin.last (n+2)) = h := by
    simp only [e, finCycle_apply]
    exact add_sub_cancel _ _
  simpa only [hlast] using
    core_patch_relabel (three 1) (three 2) (finRotate (n+3)) e he
      (Fin.last (n+2)) base hbase hvalue

end KFOL.Core.Crown
