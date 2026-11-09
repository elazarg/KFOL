module

public import KFOL.Congruences.UniformMatroid

/-! The complete uniform-matroid clause and boundary regressions. -/

@[expose] public section

namespace KFOLTest.CongruencesUniformMatroid

open KFOL

universe u

theorem uniform_matroid_identification {Role : Type u} [Finite Role] [Nonempty Role]
    (m : ℕ) (hm : m < Nat.card Role) :
    ∃ M : Matroid Role,
      M.E = Set.univ ∧
      (∀ I : Set Role, M.Indep I ↔ I.ncard ≤ m+1) ∧
      M.eRank = (m+1 : ℕ) ∧
      ∀ A : WinnerSet Role, (WinnerSet.threshold m A).val = M.closure A.val :=
  WinnerSet.uniform_matroid_identification m hm

example : (uniformMatroid (Role := Fin 4) 3).eRank = (3 : ℕ∞) := by
  exact uniformMatroid_eRank (by rw [Nat.card_fin]; decide)

example (S : Set (Fin 4)) (hS : S.ncard = 2) : (uniformMatroid 3).closure S = S := by
  change (uniformMatroid (2+1)).closure S = S
  rw [uniformMatroid_closure,ite_eq_left (by omega)]

example (S : Set (Fin 4)) (hS : S.ncard = 3) : (uniformMatroid 3).closure S = Set.univ := by
  change (uniformMatroid (2+1)).closure S = Set.univ
  rw [uniformMatroid_closure,ite_eq_right (by omega)]

example : (uniformMatroid (Role := Fin 3) 1).closure ∅ = ∅ := by
  change (uniformMatroid (0+1)).closure ∅ = ∅
  rw [uniformMatroid_closure]
  simp

/-- info: 'KFOLTest.CongruencesUniformMatroid.uniform_matroid_identification' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOLTest.CongruencesUniformMatroid.uniform_matroid_identification

end KFOLTest.CongruencesUniformMatroid
