module

public import KFOL.Algebra.TwoPlayers.CoreFailure

/-! # The two-player algebra's two Boolean forcing coordinates -/

@[expose] public section

namespace KFOL.TwoPlayers

universe u

open Classical

variable {Role : Type u}

@[simp] theorem forcingCoordinates_value (e : Fin 2 ≃ Role) (i : Fin 3) :
    forcingCoordinates e (value e i) = (decide (i = 2),decide (i = 0)) := by
  have hne : e 0 ≠ e 1 := e.injective.ne (by decide)
  have hm0 : value e 1 ≠ WinnerSet.singleton (e 0) := ambiguous_middle e _
  have hm1 : value e 1 ≠ WinnerSet.singleton (e 1) := ambiguous_middle e _
  fin_cases i <;> simp_all [forcingCoordinates,value,WinnerSet.singleton_inj]

/-- The two singleton tests jointly determine every two-player value. -/
theorem forcingCoordinates_injective (e : Fin 2 ≃ Role) :
    Function.Injective (forcingCoordinates e) := by
  intro A B he
  obtain ⟨i,rfl⟩ := value_surjective e A
  obtain ⟨j,rfl⟩ := value_surjective e B
  rw [forcingCoordinates_value,forcingCoordinates_value] at he
  have hij : i = j := by
    fin_cases i <;> fin_cases j <;> simp_all
  exact congrArg (value e) hij

theorem forcingCoordinates_choice_top (e : Fin 2 ≃ Role) (A B : WinnerSet Role) :
    forcingCoordinates e (WinnerSet.choice (e 0) A B) =
      ((forcingCoordinates e A).1 || (forcingCoordinates e B).1,
       (forcingCoordinates e A).2 && (forcingCoordinates e B).2) := by
  obtain ⟨i,rfl⟩ := value_surjective e A
  obtain ⟨j,rfl⟩ := value_surjective e B
  simp only [choice_top,forcingCoordinates_value]
  fin_cases i <;> fin_cases j <;> decide

theorem forcingCoordinates_choice_bottom (e : Fin 2 ≃ Role) (A B : WinnerSet Role) :
    forcingCoordinates e (WinnerSet.choice (e 1) A B) =
      ((forcingCoordinates e A).1 && (forcingCoordinates e B).1,
       (forcingCoordinates e A).2 || (forcingCoordinates e B).2) := by
  obtain ⟨i,rfl⟩ := value_surjective e A
  obtain ⟨j,rfl⟩ := value_surjective e B
  simp only [choice_bottom,forcingCoordinates_value]
  fin_cases i <;> fin_cases j <;> decide

theorem forcingCoordinates_swap (e : Fin 2 ≃ Role) (A : WinnerSet Role) :
    forcingCoordinates e (WinnerSet.rename (Equiv.swap (e 0) (e 1)) A) =
      ((forcingCoordinates e A).2,(forcingCoordinates e A).1) := by
  obtain ⟨i,rfl⟩ := value_surjective e A
  simp only [rename_swap,forcingCoordinates_value]
  fin_cases i <;> decide

/-- The image is exactly the Boolean pairs in which at most one player wins. -/
theorem forcingCoordinates_range (e : Fin 2 ≃ Role) (p : Bool × Bool) :
    (∃ A, forcingCoordinates e A = p) ↔ ¬(p.1 = true ∧ p.2 = true) := by
  constructor
  · rintro ⟨A,rfl⟩
    obtain ⟨i,rfl⟩ := value_surjective e A
    simp only [forcingCoordinates_value]
    fin_cases i <;> decide
  · rcases p with ⟨a,b⟩
    cases a <;> cases b
    · exact fun _ => ⟨value e 1,by simp⟩
    · exact fun _ => ⟨value e 0,by simp⟩
    · exact fun _ => ⟨value e 2,by simp⟩
    · simp

end KFOL.TwoPlayers
