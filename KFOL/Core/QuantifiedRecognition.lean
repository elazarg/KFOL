module

public import KFOL.Core.BichainRecognition

/-! # Quantified Boolean formulas as recognition of core term operations

The rows of a prenex formula give one explicit operation on finitely many
inputs. It is a core term operation exactly when the formula is true.
-/

@[expose] public section
namespace KFOL.Bichain.Quantified

universe u

variable {Role : Type u} (three : Fin 3 ↪ Role) (F : Formula) (α : ℕ → Bool)

theorem eval_neutral {V : Type*} : ∀ p : Term V, p.IsPure → p.eval (fun _ => .neutral) = .neutral := by
  intro p
  induction p with
  | var j => intro _; rfl
  | inf x y hx hy => intro h; simp [Term.eval, hx h.1, hy h.2, Value.inf]
  | sup x y hx hy => intro h; simp [Term.eval, hx h.1, hy h.2, Value.sup]
  | union x y hx hy => intro h; exact h.elim

/-- A prenex formula is true exactly when its operation is a core term operation. -/
theorem sat_iff_operation (hwf : F.WF) :
    sat F F.n 0 α ↔ ∃ t : KFOL.Term Role (Input F), t.IsCore ∧
      ∀ v, t.eval v = operation three F α v := by
  rw [sat_iff_separator F hwf α, operation, Recognition.recognition_iff]
  constructor
  · rintro ⟨p, hp, hrows, hX, hY⟩
    refine ⟨p, hp, fun z => ?_, hX, hY⟩
    cases z with
    | inl b =>
      change p.eval (fun _ => Value.neutral) ≠ _
      rw [eval_neutral p hp]
      decide
    | inr z => exact hrows z.val z.property
  · rintro ⟨p, hp, hrows, hX, hY⟩
    exact ⟨p, hp, fun z hz => hrows (.inr ⟨z, hz⟩), hX, hY⟩

end KFOL.Bichain.Quantified
