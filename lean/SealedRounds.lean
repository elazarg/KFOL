/-
Algebraic certificates for completely revealed commit--reveal rounds.

The ordered-field statements concern a two-player diagonal stage and all
mixed deviations. Rational generation and threshold separation are generic.
The SE correspondence, public-boundary pasting, and semialgebraic closure
are written proofs in the paper; this module does not formalize beliefs.
-/
import Std

set_option autoImplicit false
namespace MinimalChoice.SealedRounds

open Lean.Grind Std

section Diagonal
variable {F : Type} [Field F] [LE F] [LT F] [IsLinearOrder F]
    [LawfulOrderLT F] [OrderedRing F]

/-- Probability of the row player's win for a diagonal continuation table.
The row player maximizes this; the column player minimizes it. -/
def payoff (x y row column : F) : F :=
  x * row * column + y * (1 - row) * (1 - column)

def Nash (x y row column : F) : Prop :=
  (0 ≤ row ∧ row ≤ 1) ∧ (0 ≤ column ∧ column ≤ 1) ∧
  (∀ deviation : F, 0 ≤ deviation → deviation ≤ 1 →
    payoff x y deviation column ≤ payoff x y row column) ∧
  (∀ deviation : F, 0 ≤ deviation → deviation ≤ 1 →
    payoff x y row column ≤ payoff x y row deviation)

/-- The two pure opponent actions have the same value against this mix. -/
def Balanced (x y probability value : F) : Prop :=
  x * probability = value ∧ y * (1 - probability) = value

theorem balanced_left (x y probability value opponent : F)
    (h : Balanced x y probability value) :
    payoff x y probability opponent = value := by
  rcases h with ⟨h₀, h₁⟩
  unfold payoff
  grind

theorem balanced_right (x y probability value opponent : F)
    (h : Balanced x y probability value) :
    payoff x y opponent probability = value := by
  rcases h with ⟨h₀, h₁⟩
  unfold payoff
  grind

theorem balanced_nash (x y probability value : F)
    (h : Balanced x y probability value) (hp₀ : 0 ≤ probability)
    (hp₁ : probability ≤ 1) : Nash x y probability probability := by
  refine ⟨⟨hp₀, hp₁⟩, ⟨hp₀, hp₁⟩, ?_, ?_⟩
  · intro deviation _ _
    rw [balanced_right x y probability value deviation h,
      balanced_left x y probability value probability h]
    exact Std.le_refl _
  · intro deviation _ _
    rw [balanced_left x y probability value deviation h,
      balanced_left x y probability value probability h]
    exact Std.le_refl _

/-- Security on both sides forces the same payoff in every Nash equilibrium. -/
theorem nash_value (x y probability value row column : F)
    (h : Balanced x y probability value) (hp₀ : 0 ≤ probability)
    (hp₁ : probability ≤ 1) (hn : Nash x y row column) :
    payoff x y row column = value := by
  have hrow := hn.2.2.1 probability hp₀ hp₁
  have hcolumn := hn.2.2.2 probability hp₀ hp₁
  rw [balanced_left x y probability value column h] at hrow
  rw [balanced_right x y probability value row h] at hcolumn
  exact IsPartialOrder.le_antisymm _ _ hcolumn hrow

theorem parallel_balanced (x y : F) (hxy : x + y ≠ 0) :
    Balanced x y (y / (x + y)) (x * y / (x + y)) := by
  have hinv := Field.mul_inv_cancel hxy
  unfold Balanced
  simp only [Field.div_eq_mul_inv]
  constructor <;> grind

theorem parallel_probability_valid (x y : F) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : 0 < x + y) :
    0 ≤ y / (x + y) ∧ y / (x + y) ≤ 1 := by
  have hn : x + y ≠ 0 := by grind
  have hinv := Field.mul_inv_cancel hn
  have hmul : y / (x + y) * (x + y) = y := by
    simp only [Field.div_eq_mul_inv]
    grind
  constructor
  · apply Classical.byContradiction
    intro h
    have hp : y / (x + y) < 0 := by grind
    have hh := OrderedRing.mul_lt_mul_of_pos_right hp hxy
    grind
  · apply Classical.byContradiction
    intro h
    have hp : 1 < y / (x + y) := by grind
    have hh := OrderedRing.mul_lt_mul_of_pos_right hp hxy
    grind

theorem diagonal_nash_exists (x y : F) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : 0 < x + y) :
    Nash x y (y / (x + y)) (y / (x + y)) := by
  have hn : x + y ≠ 0 := by grind
  have hp := parallel_probability_valid x y hx hy hxy
  exact balanced_nash x y _ _ (parallel_balanced x y hn) hp.1 hp.2

theorem diagonal_nash_value (x y row column : F) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : 0 < x + y) (hn : Nash x y row column) :
    payoff x y row column = x * y / (x + y) := by
  have hs : x + y ≠ 0 := by grind
  have hp := parallel_probability_valid x y hx hy hxy
  exact nash_value x y _ _ row column (parallel_balanced x y hs) hp.1 hp.2 hn

end Diagonal

/-- U is implemented by the diagonal stage with right continuation one. -/
inductive RateTerm where
  | zero
  | one
  | step : RateTerm → RateTerm
  | complement : RateTerm → RateTerm
  deriving Repr, DecidableEq

def RateTerm.fraction : RateTerm → Nat × Nat
  | .zero => (0, 1)
  | .one => (1, 1)
  | .step t => let (p, q) := t.fraction; (p, p + q)
  | .complement t => let (p, q) := t.fraction; (q - p, q)

theorem fraction_valid (t : RateTerm) :
    0 < t.fraction.2 ∧ t.fraction.1 ≤ t.fraction.2 := by
  induction t with
  | zero => decide
  | one => decide
  | step t ih => simp only [RateTerm.fraction]; omega
  | complement t ih => simp only [RateTerm.fraction]; omega

/-- Every fraction in [0,1] is generated by complement and U.
Cross multiplication avoids any assumption that fractions are reduced. -/
theorem every_rational (p q : Nat) (hq : 0 < q) (hpq : p ≤ q) :
    ∃ t : RateTerm, t.fraction.1 * q = p * t.fraction.2 := by
  induction q using Nat.strongRecOn generalizing p with
  | ind q ih =>
    by_cases hp : p = 0
    · subst p
      exact ⟨.zero, by simp [RateTerm.fraction]⟩
    by_cases heq : p = q
    · subst p
      exact ⟨.one, by simp [RateTerm.fraction]⟩
    have hpos : 0 < p := by omega
    have hlt : p < q := by omega
    by_cases hsmall : p ≤ q - p
    · obtain ⟨t, ht⟩ := ih (q - p) (by omega) p (by omega) hsmall
      refine ⟨.step t, ?_⟩
      simp only [RateTerm.fraction]
      calc
        t.fraction.1 * q = t.fraction.1 * ((q - p) + p) := by
          rw [Nat.sub_add_cancel hpq]
        _ = t.fraction.1 * (q - p) + t.fraction.1 * p := Nat.mul_add ..
        _ = p * t.fraction.2 + p * t.fraction.1 := by
          rw [ht, Nat.mul_comm t.fraction.1 p]
        _ = p * (t.fraction.1 + t.fraction.2) := by
          rw [Nat.mul_add]
          omega
    · obtain ⟨t, ht⟩ := ih p hlt (q - p) hpos (by omega)
      refine ⟨.complement (.step t), ?_⟩
      simp only [RateTerm.fraction, Nat.add_sub_cancel_left]
      calc
        t.fraction.2 * q = t.fraction.2 * ((q - p) + p) := by
          rw [Nat.sub_add_cancel hpq]
        _ = t.fraction.2 * (q - p) + t.fraction.2 * p := Nat.mul_add ..
        _ = p * t.fraction.1 + p * t.fraction.2 := by
          rw [Nat.mul_comm t.fraction.2 (q - p), ← ht,
            Nat.mul_comm t.fraction.1 p, Nat.mul_comm t.fraction.2 p]
        _ = p * (t.fraction.1 + t.fraction.2) := (Nat.mul_add ..).symm

def reciprocalTerm : Nat → RateTerm
  | 0 => .one
  | n + 1 => .step (reciprocalTerm n)

theorem reciprocal_fraction (n : Nat) :
    (reciprocalTerm n).fraction = (1, n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [reciprocalTerm, RateTerm.fraction, ih, Nat.add_comm]

/-- The probe observes whether the rival denominator is no larger.
The stage-payoff interpretation is proved in the paper. -/
def probe (index threshold : Nat) : Prop := threshold ≤ index

theorem probes_separate (n m : Nat)
    (h : ∀ threshold, probe n threshold ↔ probe m threshold) : n = m := by
  have hnm := (h n).mp (show probe n n from Nat.le_refl n)
  have hmn := (h m).mpr (show probe m m from Nat.le_refl m)
  exact Nat.le_antisymm hnm hmn

/-- No finite carrier can retain all these winner-possibility probes. -/
theorem no_finite_summary (k : Nat) (encode : Nat → Fin k)
    (observe : Fin k → Nat → Prop)
    (adequate : ∀ n threshold, observe (encode n) threshold ↔ probe n threshold) :
    False := by
  have hinj : Function.Injective encode := by
    intro n m he
    apply probes_separate n m
    intro threshold
    rw [← adequate n threshold, ← adequate m threshold, he]
  have hn : ((List.range (k + 1)).map encode).Nodup :=
    List.Pairwise.map encode (fun i j hij he => hij (hinj he)) (List.nodup_range ..)
  have hsub : (List.range (k + 1)).map encode ⊆ List.finRange k := by
    intro i _
    exact List.mem_finRange i
  have hlen := hn.length_le_of_subset hsub
  simp only [List.length_map, List.length_range, List.length_finRange] at hlen
  omega

end MinimalChoice.SealedRounds
