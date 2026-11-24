module

public import KFOL.Core.AddressSize
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
public import Mathlib.Data.Fintype.Pi

/-! # Enumerating the full table on logarithmic address rails

For fixed owner and track counts the number of tuples is polynomial in the
unary bound on the number of labels. Their indices increase from zero.
Input zero is the least significant base-`2^k-1` digit. Digit zero names
menu mask one, so the zero mask is skipped. Each menu is emitted as an
increasing list of its role indices.
-/

@[expose] public section
namespace KFOL.AddressTableOutput

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open KFOL.Core.AddressSize

def arity (q n : ℕ) := 1 + 2*q*width n

def count (k q n : ℕ) := (2^k - 1) ^ arity q n

/-- Polynomial unary clock for the exact size, including the selector. -/
def bound (k q n : ℕ) := 2^k * (4 * (n+1)) ^ (2*q*k)

theorem count_le_bound (k q n : ℕ) : count k q n ≤ bound k q n :=
  table_length_bound k q n

def digit (base index position : ℕ) := index / base^position % base

def mask (k index position : ℕ) := digit (2^k-1) index position + 1

def menu (k index position : ℕ) : List ℕ :=
  (List.range k).filter (fun r => (mask k index position).testBit r)

def tuple (k coordinates index : ℕ) : List (List ℕ) :=
  (List.range coordinates).map (menu k index)

/-- A menu appears exactly at its specified coordinate in this ordering. -/
theorem tuple_get (k d i j : ℕ) (hj : j < d) :
    (tuple k d i)[j]'(by simpa [tuple] using hj) = menu k i j := by
  simp [tuple]

theorem tuple_getD (k d i j : ℕ) (hj : j < d) :
    (tuple k d i).getD j [] = menu k i j := by
  have len : j < (tuple k d i).length := by simpa [tuple] using hj
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem len,Option.getD_some,tuple_get k d i j hj]

theorem menu_mem (k i j r : ℕ) :
    r ∈ menu k i j ↔ r < k ∧ (mask k i j).testBit r = true := by
  simp [menu]

/-- Division by the base drops the least significant digit. -/
theorem digit_div (b i j : ℕ) : digit b (i/b) j = digit b i (j+1) := by
  simp only [digit, Nat.div_div_eq_div_mul, pow_succ']

theorem digit_ext {b d i n : ℕ} (base : 0 < b) (hi : i < b^d) (hn : n < b^d)
    (agree : ∀ j < d, digit b i j = digit b n j) : i = n := by
  induction d generalizing i n with
  | zero => simp only [pow_zero, Nat.lt_one_iff] at hi hn; exact hi.trans hn.symm
  | succ d ih =>
    have low : i % b = n % b := by simpa [digit] using agree 0 (by omega)
    have quot : i/b = n/b := by
      apply ih
      · apply (Nat.div_lt_iff_lt_mul base).mpr
        simpa [pow_succ] using hi
      · apply (Nat.div_lt_iff_lt_mul base).mpr
        simpa [pow_succ] using hn
      · intro j hj
        simpa only [digit_div] using agree (j+1) (by omega)
    calc i = i % b + b * (i / b) := (Nat.mod_add_div _ _).symm
         _ = n % b + b * (n / b) := by rw [low, quot]
         _ = n := Nat.mod_add_div _ _

/-- Every tuple of base-b digits is emitted at exactly one index below b^d. -/
theorem digits_bijective (b d : ℕ) (base : 0 < b) :
    Function.Bijective (fun (i : Fin (b^d)) (j : Fin d) =>
      (⟨digit b i j, Nat.mod_lt _ base⟩ : Fin b)) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_, by simp⟩
  intro i n same
  apply Fin.ext
  exact digit_ext base i.isLt n.isLt (fun j hj => congrArg Fin.val (congrFun same ⟨j,hj⟩))

/-- Positive k-bit masks enumerate all and only the nonempty flag vectors.
The label represented by digit m has binary mask m+1. -/
theorem positive_mask_unique (k : ℕ) (flags : Fin k → Bool) (present : ∃ r, flags r = true) :
    ∃! m : Fin (2^k-1), ∀ r : Fin k, (m.val+1).testBit r.val = flags r := by
  let bits (r : Fin k) : Fin 2 := ⟨(flags r).toNat, by cases flags r <;> decide⟩
  obtain ⟨u, same⟩ := (digits_bijective 2 k (by decide)).surjective bits
  have repr (r : Fin k) : u.val.testBit r.val = flags r := by
    have h : digit 2 u.val r.val = (flags r).toNat := congrArg Fin.val (congrFun same r)
    rw [Nat.testBit_eq_decide_div_mod_eq]
    change decide (digit 2 u.val r.val = 1) = flags r
    rw [h]
    cases flags r <;> rfl
  have pos : 0 < u.val := by
    obtain ⟨r, yes⟩ := present
    by_contra! zero
    have e := repr r
    simp [Nat.eq_zero_of_le_zero zero, yes] at e
  let m : Fin (2^k-1) := ⟨u.val-1, by have := u.isLt; omega⟩
  have recover : m.val+1 = u.val := by dsimp [m]; omega
  refine ⟨m, fun r => recover ▸ repr r, ?_⟩
  intro v hv
  apply Fin.ext
  suffices eq : v.val+1 = u.val by omega
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < k
  · exact (hv ⟨j,hj⟩).trans (repr ⟨j,hj⟩).symm
  · have large := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt hj)
    have bound : v.val+1 < 2^k := by have := v.isLt; omega
    rw [Nat.testBit_lt_two_pow (bound.trans_le large), Nat.testBit_lt_two_pow (u.isLt.trans_le large)]

/-- An arbitrary tuple of nonempty menus has exactly one index in the output.
Together with `tuple_get` and `menu_mem`, this specifies the actual role lists. -/
theorem tuple_index_unique (k d : ℕ) (hk : 0 < k) (flags : Fin d → Fin k → Bool)
    (present : ∀ j, ∃ r, flags j r = true) :
    ∃! i : Fin ((2^k-1)^d), ∀ j r, (mask k i.val j.val).testBit r.val = flags j r := by
  classical
  have base : 0 < 2^k-1 := by
    have h : 2^1 ≤ 2^k := Nat.pow_le_pow_right (by decide) hk
    omega
  let digits (j : Fin d) := (positive_mask_unique k (flags j) (present j)).exists.choose
  have good (j : Fin d) := (positive_mask_unique k (flags j) (present j)).exists.choose_spec
  let index := fun (i : Fin ((2^k-1)^d)) (j : Fin d) =>
    (⟨digit (2^k-1) i j, Nat.mod_lt _ base⟩ : Fin (2^k-1))
  have bij : Function.Bijective index := digits_bijective _ _ base
  obtain ⟨i, eq⟩ := bij.surjective digits
  refine ⟨i, ?_, ?_⟩
  · intro j r
    change ((index i j).val+1).testBit r.val = _
    rw [eq]
    exact good j r
  · intro v hv
    apply bij.injective
    rw [eq]
    funext j
    exact (positive_mask_unique k (flags j) (present j)).unique
      (fun r => hv j r) (good j)

variable {X A : Type} {input : X ↪ List Bool} {output : A ↪ List Bool}

theorem arity_poly (q : ℕ) {n : X → ℕ} (hn : ComputableInPolyTime n input encUnary) :
    ComputableInPolyTime (fun x => arity q (n x)) input encUnary := by
  have plus : ComputableInPolyTime (fun x => n x + 1) input encUnary := by fun_prop
  have log : ComputableInPolyTime (fun x => Nat.log 2 (n x+1)) input encUnary :=
    (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.unary_log_two).comp plus
  simp only [arity, width, Nat.log2_eq_log_two]
  fun_prop

theorem count_poly (k q : ℕ) {n : X → ℕ} (hn : ComputableInPolyTime n input encUnary) :
    ComputableInPolyTime (fun x => count k q (n x)) input encUnary := by
  have binary : ComputableInPolyTime (fun x => count k q (n x)) input encNat :=
    binary_pow' (const (2^k-1)) (arity_poly q hn)
  have unary : ComputableInPolyTime (fun x => bound k q (n x)) input encUnary := by
    unfold bound
    have power := (unary_pow (2*q*k)).comp (show ComputableInPolyTime (fun x => 4*(n x+1)) input encUnary by
      fun_prop)
    fun_prop
  simpa only [Nat.min_eq_right (count_le_bound k q _)] using binary_min_unary' unary binary

theorem mask_poly (k : ℕ) {i j : X → ℕ}
    (hi : ComputableInPolyTime i input encUnary) (hj : ComputableInPolyTime j input encUnary) :
    ComputableInPolyTime (fun x => mask k (i x) (j x)) input encNat := by
  apply ComputableInPolyTime.of_tidy
  apply ComputableTidilyInPolyTime.binary_add'
  · apply ComputableTidilyInPolyTime.binary_mod'
    · apply ComputableTidilyInPolyTime.binary_div'
      · exact ComputableTidilyInPolyTime.unary_to_binary.comp hi.tidy
      · exact ComputableTidilyInPolyTime.binary_pow' (.const _) hj.tidy
    · exact .const _
  · exact .const _

theorem menu_poly (k : ℕ) {i j : X → ℕ}
    (hi : ComputableInPolyTime i input encUnary) (hj : ComputableInPolyTime j input encUnary) :
    ComputableInPolyTime (fun x => menu k (i x) (j x)) input (encList encUnary) := by
  apply filterWithInput (const (List.range k))
  apply ComputableInPolyTime.of_tidy
  apply ComputableTidilyInPolyTime.binary_testBit
  · exact ((mask_poly k hi hj).comp (fst input encUnary)).tidy
  · exact (snd input encUnary).tidy

theorem tuple_poly (k : ℕ) {d i : X → ℕ}
    (hd : ComputableInPolyTime d input encUnary) (hi : ComputableInPolyTime i input encUnary) :
    ComputableInPolyTime (fun x => tuple k (d x) (i x)) input (encList (encList encUnary)) := by
  apply mapWithInput (ComputableInPolyTime.range.comp hd)
  exact menu_poly k (hi.comp (fst input encUnary)) (snd input encUnary)

/-- Supply a point evaluator on a source instance and its concrete list of
menus. The table program returns the list of its outputs in tuple-index order. -/
def table (k q : ℕ) (n : X → ℕ) (eval : X → List (List ℕ) → A) (x : X) : List A :=
  (List.range (count k q (n x))).map fun i => eval x (tuple k (arity q (n x)) i)

theorem table_length (k q : ℕ) (n : X → ℕ) (eval : X → List (List ℕ) → A) (x : X) :
    (table k q n eval x).length = count k q (n x) := by simp [table]

theorem table_get (k q : ℕ) (n : X → ℕ) (eval : X → List (List ℕ) → A) (x : X) (i : ℕ)
    (hi : i < count k q (n x)) :
    (table k q n eval x)[i]'(by rwa [table_length]) = eval x (tuple k (arity q (n x)) i) := by
  simp [table]

theorem table_poly (k q : ℕ) {n : X → ℕ} {eval : X → List (List ℕ) → A}
    (hn : ComputableInPolyTime n input encUnary)
    (heval : ComputableInPolyTime (fun p : X × List (List ℕ) => eval p.1 p.2)
      (encPair input (encList (encList encUnary))) output) :
    ComputableInPolyTime (table k q n eval) input (encList output) := by
  apply mapWithInput (ComputableInPolyTime.range.comp (count_poly k q hn))
  exact heval.comp ((fst input encUnary).prod (tuple_poly k
    ((arity_poly q hn).comp (fst input encUnary)) (snd input encUnary)))

/-- The same tuple format with role identifiers encoded in binary. -/
theorem table_binary_poly (k q : ℕ) {n : X → ℕ} {eval : X → List (List ℕ) → A}
    (hn : ComputableInPolyTime n input encUnary)
    (heval : ComputableInPolyTime (fun p : X × List (List ℕ) => eval p.1 p.2)
      (encPair input (encList (encList encNat))) output) :
    ComputableInPolyTime (table k q n eval) input (encList output) := by
  have convertRole : ComputableInPolyTime (fun i : ℕ => i) encUnary encNat :=
    .of_tidy ComputableTidilyInPolyTime.unary_to_binary
  have convertMenu : ComputableInPolyTime (fun v : List ℕ => v) (encList encUnary) (encList encNat) := by
    rw [show (fun v : List ℕ => v) = List.map (fun i : ℕ => i) by
      funext v; exact (List.map_id' v).symm]
    exact ComputableInPolyTime.map convertRole
  have convertTuple : ComputableInPolyTime (fun v : List (List ℕ) => v)
      (encList (encList encUnary)) (encList (encList encNat)) := by
    rw [show (fun v : List (List ℕ) => v) = List.map (fun m : List ℕ => m) by
      funext v; exact (List.map_id' v).symm]
    exact ComputableInPolyTime.map convertMenu
  apply table_poly k q hn
  exact heval.comp ((fst _ _).prod (convertTuple.comp (snd _ _)))

end KFOL.AddressTableOutput
