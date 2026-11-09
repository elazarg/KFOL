module

public import KFOL.Definitions.Reset
public import KFOL.Algebra.Idempotent

/-! # Elementary reset laws and a binary induction interface -/

@[expose] public section

namespace KFOL

universe u v

namespace WinnerSet

variable {Role : Type u} (A B : WinnerSet Role)

@[simp] theorem reset_singleton (r : Role) : A.reset (singleton r) = singleton r := by
  have h : ¬Ambiguous (singleton r) := fun h => h r rfl
  simp [reset, h]

theorem reset_of_ambiguous (hB : B.Ambiguous) : A.reset B = A.union B := by
  simp [reset, hB]

@[simp] theorem ambiguous_reset : (A.reset B).Ambiguous ↔ B.Ambiguous := by
  classical
  by_cases hB : B.Ambiguous
  · rw [reset_of_ambiguous A B hB]
    exact ⟨fun _ => hB, fun _ => by rw [union_comm]; exact hB.union_left⟩
  · simp [reset, hB]

@[simp] theorem mem_reset (r : Role) :
    r ∈ (A.reset B).val ↔ r ∈ B.val ∨ (B.Ambiguous ∧ r ∈ A.val) := by
  classical
  by_cases hB : B.Ambiguous <;> simp [reset, hB, or_comm]

@[simp] theorem reset_self : A.reset A = A := by
  classical
  by_cases hA : A.Ambiguous <;> simp [reset, hA]

end WinnerSet

namespace Reset.Term

variable {Var : Type v} {Role : Type u}

@[simp] theorem root_step (s t : Term Var) : (step s t).root = t.root := rfl

@[simp] theorem size_var (j : Var) : size (.var j) = 1 := rfl
@[simp] theorem size_step (s t : Term Var) : (step s t).size = 1 + s.size + t.size := rfl

@[simp] theorem selected_step (s t : Term Var) (B : Set Var) (j : Var) :
    (step s t).Selected B j ↔ t.Selected B j ∨ (t.root ∈ B ∧ s.Selected B j) := Iff.rfl

@[simp] theorem eval_var (j : Var) (v : Var → WinnerSet Role) :
    eval (.var j) v = v j := rfl

@[simp] theorem eval_step (s t : Term Var) (v : Var → WinnerSet Role) :
    (step s t).eval v = (s.eval v).reset (t.eval v) := rfl

/-- Ordinary binary-tree induction while retaining mathlib's term datatype. -/
@[elab_as_elim] theorem induction_reset {P : Term Var → Prop}
    (var : ∀ j, P (.var j)) (step : ∀ s t, P s → P t → P (Term.step s t))
    (t : Term Var) : P t := by
  induction t with
  | var j => exact var j
  | @func n f args ih =>
    cases f
    have he : FirstOrder.Language.Term.func Symbol.reset args = Term.step (args 0) (args 1) := by
      congr 1
      funext i
      have hi : i = 0 ∨ i = 1 := by omega
      rcases hi with rfl | rfl <;> rfl
    rw [he]
    exact step _ _ (ih 0) (ih 1)

end Reset.Term
end KFOL
