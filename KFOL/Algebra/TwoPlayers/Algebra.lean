module

public import KFOL.Definitions.TwoPlayers
public import KFOL.Algebra.Idempotent
public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.FinCases

/-! # The two-player winner-set algebra is the strong-Kleene chain -/

@[expose] public section

namespace KFOL.TwoPlayers

open Classical

universe u

variable {Role : Type u}

/-- The two named roles exhaust the type. -/
theorem role_cases (e : Fin 2 ≃ Role) (r : Role) : r = e 0 ∨ r = e 1 := by
  have h : e.symm r = 0 ∨ e.symm r = 1 := by omega
  exact h.elim (fun h => Or.inl ((e.apply_symm_apply r).symm.trans (congrArg e h)))
    (fun h => Or.inr ((e.apply_symm_apply r).symm.trans (congrArg e h)))

theorem ambiguous_middle (e : Fin 2 ≃ Role) : (value e 1).Ambiguous := by
  apply WinnerSet.ambiguous_of_two_mem _ (e 0) (e 1) (e.injective.ne (by decide))
  · simp [value]
  · simp [value]

/-- The three values exhaust all nonempty winner sets, without enumerating a
sample of sets or assuming a certificate. -/
theorem value_surjective (e : Fin 2 ≃ Role) : Function.Surjective (value e) := by
  intro A
  by_cases h0 : e 0 ∈ A.val
  · by_cases h1 : e 1 ∈ A.val
    · refine ⟨1,?_⟩
      apply Subtype.ext
      ext r
      constructor
      · intro _
        exact (role_cases e r).elim (fun h => h ▸ h0) (fun h => h ▸ h1)
      · intro _
        rcases role_cases e r with rfl | rfl <;> simp [value]
    · refine ⟨2,?_⟩
      symm
      apply WinnerSet.eq_singleton_of_subset A (e 0)
      intro r hr
      exact (role_cases e r).elim id (fun he => False.elim (h1 (he ▸ hr)))
  · have hsub : A.val ⊆ {e 1} := by
      intro r hr
      exact (role_cases e r).elim (fun he => False.elim (h0 (he ▸ hr))) id
    exact ⟨0,(WinnerSet.eq_singleton_of_subset A (e 1) hsub).symm⟩

@[simp] theorem rank_value (e : Fin 2 ≃ Role) (i : Fin 3) : rank e (value e i) = i := by
  classical
  have hne : e 0 ≠ e 1 := e.injective.ne (by decide)
  have hm0 : value e 1 ≠ WinnerSet.singleton (e 0) := ambiguous_middle e _
  have hm1 : value e 1 ≠ WinnerSet.singleton (e 1) := ambiguous_middle e _
  fin_cases i <;> simp_all [rank,value,WinnerSet.singleton_inj]

@[simp] theorem value_rank (e : Fin 2 ≃ Role) (A : WinnerSet Role) : value e (rank e A) = A := by
  obtain ⟨i,rfl⟩ := value_surjective e A
  rw [rank_value]

/-- An actual bijection with the usual three-element truth chain. -/
noncomputable def equiv (e : Fin 2 ≃ Role) : WinnerSet Role ≃ Fin 3 where
  toFun := rank e
  invFun := value e
  left_inv := value_rank e
  right_inv := rank_value e

/-- The top player's owned choice is maximum on the truth chain. -/
theorem choice_top (e : Fin 2 ≃ Role) (i j : Fin 3) :
    WinnerSet.choice (e 0) (value e i) (value e j) = value e (max i j) := by
  classical
  have hne : e 0 ≠ e 1 := e.injective.ne (by decide)
  have hm : value e 1 ≠ WinnerSet.singleton (e 0) := ambiguous_middle e _
  fin_cases i <;> fin_cases j
  all_goals dsimp only [max,LE.le,Fin.le_def]
  all_goals simp_all [value,WinnerSet.choice,WinnerSet.singleton_inj]
  all_goals apply Subtype.ext
  all_goals ext r
  all_goals simp [WinnerSet.union,Set.union_comm]

/-- The bottom player's owned choice is minimum on the truth chain. -/
theorem choice_bottom (e : Fin 2 ≃ Role) (i j : Fin 3) :
    WinnerSet.choice (e 1) (value e i) (value e j) = value e (min i j) := by
  classical
  have hne : e 0 ≠ e 1 := e.injective.ne (by decide)
  have hm : value e 1 ≠ WinnerSet.singleton (e 1) := ambiguous_middle e _
  fin_cases i <;> fin_cases j
  all_goals dsimp only [min,LE.le,Fin.le_def]
  all_goals simp_all [value,WinnerSet.choice,WinnerSet.singleton_inj]
  all_goals apply Subtype.ext
  all_goals ext r
  all_goals simp [WinnerSet.union,Set.union_comm]

/-- Exchanging the two roles reverses the truth chain and fixes ambiguity. -/
theorem rename_swap (e : Fin 2 ≃ Role) (i : Fin 3) :
    WinnerSet.rename (Equiv.swap (e 0) (e 1)) (value e i) = value e i.rev := by
  classical
  fin_cases i
  all_goals simp [value,WinnerSet.rename_singleton,WinnerSet.rename_union]
  exact WinnerSet.union_comm _ _

/-- Complete strong-Kleene identification of every public operation. -/
theorem strong_kleene_identification (e : Fin 2 ≃ Role) :
    ∃ q : WinnerSet Role ≃ Fin 3,
      (∀ i, q (value e i) = i) ∧
      (∀ A B, q (WinnerSet.choice (e 0) A B) = max (q A) (q B)) ∧
      (∀ A B, q (WinnerSet.choice (e 1) A B) = min (q A) (q B)) ∧
      (∀ A, q (WinnerSet.rename (Equiv.swap (e 0) (e 1)) A) = (q A).rev) := by
  refine ⟨equiv e,rank_value e,?_,?_,?_⟩
  · intro A B
    obtain ⟨i,rfl⟩ := value_surjective e A
    obtain ⟨j,rfl⟩ := value_surjective e B
    simp only [choice_top,equiv,Equiv.coe_fn_mk,rank_value]
  · intro A B
    obtain ⟨i,rfl⟩ := value_surjective e A
    obtain ⟨j,rfl⟩ := value_surjective e B
    simp only [choice_bottom,equiv,Equiv.coe_fn_mk,rank_value]
  · intro A
    obtain ⟨i,rfl⟩ := value_surjective e A
    simp only [rename_swap,equiv,Equiv.coe_fn_mk,rank_value]

end KFOL.TwoPlayers
