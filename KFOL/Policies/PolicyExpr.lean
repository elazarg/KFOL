module

public import KFOL.Policies.Lattice

/-! Bounded lattice policy expressions expand to the original native reset/R
signature. Endpoints are reset macros, not added operation symbols. -/

@[expose] public section

namespace KFOL.Policies

universe u v w

namespace PolicyExpr

variable {Role : Type u} {Label : Type w} {Var : Type v}

@[simp] theorem eval_expand (D : Label → Set Role) (E : PolicyExpr Label)
    (X Y Z : Term Label Var) (v : Var → WinnerSet Role) :
    (E.expand X Y Z).eval D v = WinnerSet.policyReset (E.eval D) (X.eval D v) (Y.eval D v) (Z.eval D v) := by
  induction E generalizing X Y Z with
  | atom d => rfl
  | bottom => simp only [expand, eval, Term.eval_step, WinnerSet.policyReset_empty]
  | top => simp only [expand, eval, Term.eval_step, WinnerSet.policyReset_univ]
  | sup E F ihE ihF => rw [expand, ihE, ihF, eval, WinnerSet.policyReset_union]
  | inf E F ihE ihF => rw [expand, Term.eval_step, ihE, ihF, eval, WinnerSet.policyReset_inter]

@[simp] theorem eval_gate (D : Label → Set Role) (E : PolicyExpr Label)
    (root test : Var) (continuation : Term Label Var) (v : Var → WinnerSet Role) :
    (E.gate root test continuation).eval D v =
      WinnerSet.policyReset (E.eval D) (v root) (v test) (continuation.eval D v) := by
  rw [gate, eval_expand, Term.eval_var, Term.eval_var]

/-- Exact primitive tree size, including every copied continuation. -/
theorem size_gate (E : PolicyExpr Label) (root test : Var) (continuation : Term Label Var) :
    (E.gate root test continuation).size = E.continuationCopies * continuation.size + E.overhead := by
  induction E generalizing continuation with
  | atom d =>
    change 1 + 1 + 1 + continuation.size = 1 * continuation.size + 3
    omega
  | bottom =>
    change 1 + (1 + 1 + 1) + (1 + continuation.size + 1) = 1 * continuation.size + 6
    omega
  | top =>
    change 1 + (1 + continuation.size + 1) + 1 = 1 * continuation.size + 4
    omega
  | sup E F ihE ihF =>
    change (E.gate root test (F.gate root test continuation)).size = _
    rw [ihE, ihF]
    simp only [continuationCopies, overhead, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]
  | inf E F ihE ihF =>
    change 1 + (E.gate root test continuation).size + (F.gate root test continuation).size = _
    rw [ihE, ihF]
    simp only [continuationCopies, overhead, Nat.add_mul]
    omega

theorem continuationCopies_pos (E : PolicyExpr Label) : 0 < E.continuationCopies := by
  induction E with
  | atom | bottom | top => exact Nat.zero_lt_one
  | sup E F hE hF => exact Nat.mul_pos hE hF
  | inf E F hE _ => exact Nat.add_pos_left hE _

end PolicyExpr
end KFOL.Policies

namespace KFOL.Policies.PolicyExpr

universe u v w x

variable {Role : Type u} {Label : Type w}

@[simp] theorem not_mem_eval_unionLabels (D : Label → Set Role) (r : Role) (labels : List Label) :
    r ∉ (unionLabels labels).eval D ↔ ∀ d ∈ labels, r ∉ D d := by
  induction labels with
  | nil => simp [unionLabels, eval]
  | cons d ds ih => simp [unionLabels, eval, ih]

@[simp] theorem mem_eval_meetAll (D : Label → Set Role) (r : Role) (Es : List (PolicyExpr Label)) :
    r ∈ (meetAll Es).eval D ↔ ∀ E ∈ Es, r ∈ E.eval D := by
  induction Es with
  | nil => simp [meetAll, eval]
  | cons E Es ih => simp [meetAll, eval, ih]

end KFOL.Policies.PolicyExpr
