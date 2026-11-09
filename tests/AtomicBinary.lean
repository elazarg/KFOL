module

import KFOL.Algebra.Atomic.Binary

namespace KFOL.AtomicBinaryRegression

universe u

/-- Complete binary classification with explicit public-language hypotheses. -/
theorem binary {Role : Type u} (three : Fin 3 ↪ Role) (t : Term Role (Fin 2))
    (ha : ∀ x : Fin 2 → Role, ∃ r,
      t.eval (fun i => WinnerSet.singleton (x i)) = WinnerSet.singleton r)
    (hd : ∀ A : WinnerSet Role, t.eval (fun _ => A) = A) :
    (∀ v : Fin 2 → WinnerSet Role, t.eval v = v 0) ∨
    (∀ v : Fin 2 → WinnerSet Role, t.eval v = v 1) ∨
    (∀ v : Fin 2 → WinnerSet Role, t.eval v = (v 0).reset (v 1)) ∨
    (∀ v : Fin 2 → WinnerSet Role, t.eval v = (v 1).reset (v 0)) :=
  t.binary_atom_preserving three ha hd

/-- Complete converse: all four and only these have a realizing idempotent,
atom-preserving core term. -/
theorem binary_iff {Role : Type u} [Finite Role] (three : Fin 3 ↪ Role)
    (f : (Fin 2 → WinnerSet Role) → WinnerSet Role) :
    (∃ t : Term Role (Fin 2), t.IsCore ∧
      (∀ x : Fin 2 → Role, ∃ r,
        t.eval (fun i => WinnerSet.singleton (x i)) = WinnerSet.singleton r) ∧
      (∀ A : WinnerSet Role, t.eval (fun _ => A) = A) ∧ (∀ v, t.eval v = f v)) ↔
    (∀ v : Fin 2 → WinnerSet Role, f v = v 0) ∨
    (∀ v : Fin 2 → WinnerSet Role, f v = v 1) ∨
    (∀ v : Fin 2 → WinnerSet Role, f v = (v 0).reset (v 1)) ∨
    (∀ v : Fin 2 → WinnerSet Role, f v = (v 1).reset (v 0)) :=
  Term.binary_operation_classification three f

private def three : Fin 3 ↪ Fin 4 := ⟨fun i => ⟨i.val,by omega⟩,by
  intro i j he
  exact Fin.ext (congrArg (Fin.val (n := 4)) he)⟩

example : ∃ t : Term (Fin 4) (Fin 2), t.IsCore ∧ t.AtomPreserving ∧
    (∀ A : WinnerSet (Fin 4), t.eval (fun _ => A) = A) ∧
    (∀ v, t.eval v = (v 1).reset (v 0)) := by
  apply (Term.binary_operation_classification three _).mpr
  exact Or.inr (Or.inr (Or.inr (fun _ => rfl)))

example (t : Term (Fin 4) (Fin 2)) (ha : t.AtomPreserving)
    (hd : ∀ A : WinnerSet (Fin 4), t.eval (fun _ => A) = A) :
    ∃ s : Reset.Term (Fin 2), ∀ v : Fin 2 → WinnerSet (Fin 4), t.eval v = s.eval v :=
  t.binary_reset_representation three ha hd

end KFOL.AtomicBinaryRegression

#print axioms KFOL.Term.binary_atom_preserving
#print axioms KFOL.Term.binary_operation_classification
#print axioms KFOL.Term.binary_reset_representation
