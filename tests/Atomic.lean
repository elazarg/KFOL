module

import KFOL.Algebra.Atomic.Classification

namespace KFOL.AtomicRegression

universe u v

/-- Complete paper-facing S2 statement, including actual term realization. -/
theorem atomic_functions {Role : Type u} [Finite Role] (three : Fin 3 ↪ Role)
    {Var : Type v} [Finite Var] [Nonempty Var] (f : (Var → Role) → Role) :
    (∃ t : Term Role Var,
      (∀ x : Var → Role, ∃ r,
        t.eval (fun i => WinnerSet.singleton (x i)) = WinnerSet.singleton r) ∧
      (∀ x : Var → Role,
        t.eval (fun i => WinnerSet.singleton (x i)) = WinnerSet.singleton (f x))) ↔
      (∃ i : Var, ∃ g : Role → Role, ∀ x, f x = g (x i)) ∨
      (∃ a b : Role, ∀ x, f x = a ∨ f x = b) := by
  let _ : Nonempty Role := ⟨three 0⟩
  exact Term.atomic_function_classification_with_preservation f

/-- Complete determinacy corollary; no finite label hypothesis is needed. -/
theorem determinacy {Role : Type u} (three : Fin 3 ↪ Role)
    {Var : Type v} [Finite Var] (t : Term Role Var)
    (ha : ∀ x : Var → Role, ∃ r,
      t.eval (fun i => WinnerSet.singleton (x i)) = WinnerSet.singleton r)
    (hd : ∀ A : WinnerSet Role, t.eval (fun _ => A) = A) :
    ∃ i : Var, ∀ x : Var → Role,
      t.eval (fun j => WinnerSet.singleton (x j)) = WinnerSet.singleton (x i) :=
  t.atomic_determinacy three ha (fun r => hd (WinnerSet.singleton r))

example : ∃ t : Term (Fin 4) (Fin 3), t.AtomicRealizes
    (fun v => if v 0 = v 1 then 0 else 3) := by
  apply Term.atomic_realization_atMostTwo
  refine ⟨0,3,fun v => ?_⟩
  dsimp only
  split <;> simp_all

example : ∃ t : Term (Fin 5) (Fin 2), t.AtomicRealizes
    (fun v => if v 1 = 4 then 2 else v 1) :=
  Term.atomic_realization_unary 1 (fun x => if x = 4 then 2 else x)

example : ∃ t : Term (Fin 3) (Fin 0), t.AtomicRealizes (fun _ => 2) :=
  Term.atomic_realization_atMostTwo _ ⟨2,2,fun _ => Or.inl rfl⟩

end KFOL.AtomicRegression

#print axioms KFOL.Term.atomic_function_classification
#print axioms KFOL.Term.atomic_determinacy
