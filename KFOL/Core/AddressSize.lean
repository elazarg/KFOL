module

public import KFOL.Core.AddressedRails
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.Ring

/-! # Size of a table on binary address rails -/

@[expose] public section
namespace KFOL.Core.AddressSize

open AddressedRails

/-- Two spare bit positions guarantee a nontrivial bit set even for one label. -/
def width (n : ℕ) : ℕ := (n + 1).log2 + 2

theorem width_ge_two (n : ℕ) : 2 ≤ width n := by simp [width]
instance (n : ℕ) : Nontrivial (Fin (width n)) :=
  Fin.nontrivial_iff_two_le.mpr (width_ge_two n)

theorem fits (n : ℕ) : n < 2 ^ width n := by
  have h : (n+1).log2 < width n := by simp [width]
  exact Nat.lt_trans (Nat.lt_succ_self n) ((Nat.log2_lt (Nat.succ_ne_zero n)).mp h)

theorem power_bound (n : ℕ) : 2 ^ width n ≤ 4 * (n+1) := by
  have h : 2 ^ (n+1).log2 ≤ n+1 := (Nat.le_log2 (Nat.succ_ne_zero n)).mp (Nat.le_refl _)
  rw [width, pow_add]
  omega

/-- A label number and a track coloring compute the address digits directly. -/
def book {Label Track : Type*} {n : ℕ} (ids : Label ↪ Fin n) (color : Label → Track) :
    Book Label Track (Fin (width n)) where
  track := color
  digit f i := (ids f).val.testBit i.val
  unique f h _ bits := by
    apply ids.injective
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < width n
    · exact bits ⟨i, hi⟩
    · have bound := Nat.le_of_not_gt hi
      have lim : n < 2 ^ i := (fits n).trans_le (Nat.pow_le_pow_right (by decide) bound)
      rw [Nat.testBit_lt_two_pow ((ids f).isLt.trans lim), Nat.testBit_lt_two_pow ((ids h).isLt.trans lim)]

/-- Count all nonempty-menu tuples, including the extra selector. At fixed
owner and track counts the right hand side is polynomial in label count. -/
theorem table_length_bound (k q n : ℕ) :
    (2^k - 1) ^ (1 + 2*q*width n) ≤ 2^k * (4*(n+1)) ^ (2*q*k) := by
  calc
    _ ≤ (2^k) ^ (1 + 2*q*width n) := Nat.pow_le_pow_left (Nat.sub_le _ _) _
    _ = 2^k * (2 ^ width n) ^ (2*q*k) := by
      rw [pow_add, pow_one, ← pow_mul, ← pow_mul]
      congr 2
      ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (power_bound _) _)

end KFOL.Core.AddressSize
