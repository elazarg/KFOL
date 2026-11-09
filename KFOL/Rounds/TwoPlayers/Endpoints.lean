module

public import KFOL.Rounds.TwoPlayers.Values
public import Mathlib.Logic.Equiv.Fin.Basic

/-! # Pure equilibrium endpoints are exactly all-winning rows or columns -/
@[expose] public section
noncomputable section
namespace KFOL.Rounds.Game.TwoPlayers
open GameTheory GameTheory.Math.Probability

/-- The actual pair of menu choices, without a padded or duplicated action. -/
def matrixAction (sizes : Fin 2 → Nat) (row : Fin (sizes 0+1)) (col : Fin (sizes 1+1)) :
    (i : Fin 2) → Fin (sizes i+1) :=
  (piFinTwoEquiv (fun i => Fin (sizes i+1))).symm (row,col)

@[simp] theorem matrixAction_zero (sizes : Fin 2 → Nat) (row : Fin (sizes 0+1)) (col : Fin (sizes 1+1)) :
    matrixAction sizes row col 0 = row := rfl
@[simp] theorem matrixAction_one (sizes : Fin 2 → Nat) (row : Fin (sizes 0+1)) (col : Fin (sizes 1+1)) :
    matrixAction sizes row col 1 = col := rfl
@[simp] theorem matrixAction_coords (sizes : Fin 2 → Nat) (actions : (i : Fin 2) → Fin (sizes i+1)) :
    matrixAction sizes (actions 0) (actions 1) = actions :=
  (piFinTwoEquiv (fun i => Fin (sizes i+1))).symm_apply_apply actions

private theorem mass_zero {α : Type*} (law : PMF α) (i : α) (h : (law i).toReal ≤ 0) : law i = 0 :=
  (ENNReal.toReal_eq_toReal_iff' (law.apply_ne_top i) (by simp)).mp
    (by simpa using le_antisymm h ENNReal.toReal_nonneg)

private theorem mass_one {α : Type*} (law : PMF α) (i : α) (h : 1 ≤ (law i).toReal) : law = PMF.pure i := by
  have he : law i = 1 := (ENNReal.toReal_eq_toReal_iff' (law.apply_ne_top i) (by simp)).mp
    (by simpa using le_antisymm (pmf_toReal_apply_le_one law i) h)
  exact pmf_eq_pure_of_support_subset_singleton law i ((law.apply_eq_one_iff i).mp he).subset

private theorem finTwo_support (law : PMF (Fin 2)) :
    ∀ who, who ≠ 0 → who ≠ 1 → law who = 0 := by
  intro who h0 h1
  fin_cases who <;> contradiction

private theorem pure_of_opponent_zero (law : PMF (Fin 2)) (who : Fin 2)
    (zero : law who.rev = 0) : law = PMF.pure who := by
  apply pmf_eq_pure_of_support_subset_singleton law who
  intro i hi
  fin_cases who <;> fin_cases i <;> simp_all [PMF.mem_support_iff]

private theorem winning_deviation_forces (sizes : Fin 2 → Nat)
    (p : ((i : Fin 2) → Fin (sizes i+1)) → PMF (Fin 2))
    (profile : (i : Fin 2) → PMF (Fin (sizes i+1)))
    (nash : IsNash (stageForm sizes p).mixed
      (euPreference (fun winner i => winnerPayoff id i winner)) profile)
    (who : Fin 2) (alternative : PMF (Fin (sizes who+1)))
    (wins : (independentProduct (Profile.update
      (sig := {Strategy := fun i => PMF (Fin (sizes i+1)),Outcome := Fin 2})
      profile who alternative)).bind p = PMF.pure who) :
    (independentProduct profile).bind p = PMF.pure who := by
  apply mass_one
  have h := (Observed.stage_nash_iff sizes p profile).mp nash who alternative
  simpa only [wins,PMF.pure_apply_self,ENNReal.toReal_one] using h

/-- At the upper endpoint, a supported equilibrium row wins against every
pure column. Conversely one such row forces the upper endpoint in every Nash
equilibrium. The proof uses actual support and arbitrary whole menu-law deviations. -/
theorem nash_pure_zero_iff (sizes : Fin 2 → Nat)
    (p : ((i : Fin 2) → Fin (sizes i+1)) → PMF (Fin 2))
    (profile : (i : Fin 2) → PMF (Fin (sizes i+1)))
    (nash : IsNash (stageForm sizes p).mixed
      (euPreference (fun winner i => winnerPayoff id i winner)) profile) :
    (independentProduct profile).bind p = PMF.pure 0 ↔
      ∃ row, ∀ col, p (matrixAction sizes row col) = PMF.pure 0 := by
  constructor
  · intro wins
    obtain ⟨row,hrow⟩ := (profile 0).support_nonempty
    refine ⟨row,fun col => ?_⟩
    let changed := Profile.update
      (sig := {Strategy := fun i => PMF (Fin (sizes i+1)),Outcome := Fin 2})
      profile 1 (PMF.pure col)
    have hdev := (Observed.stage_nash_iff sizes p profile).mp nash 1 (PMF.pure col)
    have hz : ((independentProduct changed).bind p) 1 = 0 := by
      apply mass_zero
      simpa only [wins,PMF.pure_apply,show (1 : Fin 2) ≠ 0 by decide,ite_false,ENNReal.toReal_zero] using hdev
    have htuple : matrixAction sizes row col ∈ (independentProduct changed).support := by
      rw [independentProduct_support_iff]
      intro i
      fin_cases i
      · simpa [changed] using hrow
      · simp [changed]
    apply pure_of_opponent_zero _ 0
    change p (matrixAction sizes row col) 1 = 0
    by_contra hn
    have hm : 1 ∈ ((independentProduct changed).bind p).support :=
      (PMF.mem_support_bind_iff ..).mpr ⟨matrixAction sizes row col,htuple,hn⟩
    exact hm hz
  · rintro ⟨row,hrow⟩
    apply winning_deviation_forces sizes p profile nash 0 (PMF.pure row)
    apply pmf_eq_pure_of_support_subset_singleton
    intro who hw
    obtain ⟨actions,ha,hp⟩ := (PMF.mem_support_bind_iff ..).mp hw
    have hzero := (independentProduct_support_iff _ actions).mp ha 0
    have he : actions 0 = row := by simpa using hzero
    have heq : p actions = PMF.pure 0 := by
      rw [← matrixAction_coords sizes actions,he]
      exact hrow (actions 1)
    simpa only [heq,PMF.mem_support_pure_iff,Set.mem_singleton_iff] using hp

/-- The lower endpoint is forced exactly by an all-winning column. -/
theorem nash_pure_one_iff (sizes : Fin 2 → Nat)
    (p : ((i : Fin 2) → Fin (sizes i+1)) → PMF (Fin 2))
    (profile : (i : Fin 2) → PMF (Fin (sizes i+1)))
    (nash : IsNash (stageForm sizes p).mixed
      (euPreference (fun winner i => winnerPayoff id i winner)) profile) :
    (independentProduct profile).bind p = PMF.pure 1 ↔
      ∃ col, ∀ row, p (matrixAction sizes row col) = PMF.pure 1 := by
  constructor
  · intro wins
    obtain ⟨col,hcol⟩ := (profile 1).support_nonempty
    refine ⟨col,fun row => ?_⟩
    let changed := Profile.update
      (sig := {Strategy := fun i => PMF (Fin (sizes i+1)),Outcome := Fin 2})
      profile 0 (PMF.pure row)
    have hdev := (Observed.stage_nash_iff sizes p profile).mp nash 0 (PMF.pure row)
    have hz : ((independentProduct changed).bind p) 0 = 0 := by
      apply mass_zero
      simpa only [wins,PMF.pure_apply,show (0 : Fin 2) ≠ 1 by decide,ite_false,ENNReal.toReal_zero] using hdev
    have htuple : matrixAction sizes row col ∈ (independentProduct changed).support := by
      rw [independentProduct_support_iff]
      intro i
      fin_cases i
      · simp [changed]
      · simpa [changed] using hcol
    apply pure_of_opponent_zero _ 1
    change p (matrixAction sizes row col) 0 = 0
    by_contra hn
    have hm : 0 ∈ ((independentProduct changed).bind p).support :=
      (PMF.mem_support_bind_iff ..).mpr ⟨matrixAction sizes row col,htuple,hn⟩
    exact hm hz
  · rintro ⟨col,hcol⟩
    apply winning_deviation_forces sizes p profile nash 1 (PMF.pure col)
    apply pmf_eq_pure_of_support_subset_singleton
    intro who hw
    obtain ⟨actions,ha,hp⟩ := (PMF.mem_support_bind_iff ..).mp hw
    have hone := (independentProduct_support_iff _ actions).mp ha 1
    have he : actions 1 = col := by simpa using hone
    have heq : p actions = PMF.pure 1 := by
      rw [← matrixAction_coords sizes actions,he]
      exact hcol (actions 0)
    simpa only [heq,PMF.mem_support_pure_iff,Set.mem_singleton_iff] using hp

end KFOL.Rounds.Game.TwoPlayers
