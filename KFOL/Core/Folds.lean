module

public import KFOL.Core.Protected

/-! # Finite owned folds, with exact native atom and upper-marker semantics -/

@[expose] public section

namespace KFOL.Core

universe u v

variable {Role : Type u} [DecidableEq Role] {Var : Type v}

attribute [local instance] Native.structureOf

/-- A finite owned fold with an explicit final argument. Nonempty finite
families can repeat one argument as the final argument by idempotence. -/
def foldTerm (r : Role) (xs : List (Equational.Term (Equational.CoreSymbol Role) Var))
    (last : Equational.Term (Equational.CoreSymbol Role) Var) :
    Equational.Term (Equational.CoreSymbol Role) Var :=
  xs.foldr (choiceTerm r) last

@[simp] theorem profile_fold_owner (r : Role) (v : Var → Bool)
    (xs : List (Equational.Term (Equational.CoreSymbol Role) Var))
    (last : Equational.Term (Equational.CoreSymbol Role) Var) :
    profile r v (foldTerm r xs last) = true ↔
      profile r v last = true ∨ ∃ x ∈ xs, profile r v x = true := by
  induction xs with
  | nil => simp [foldTerm]
  | cons x xs ih =>
    change profile r v (choiceTerm r x (foldTerm r xs last)) = true ↔ _
    simp only [profile_choice, ite_true, Bool.or_eq_true, ih, List.mem_cons, exists_eq_or_imp]
    tauto

theorem profile_fold_other (r i : Role) (hri : r ≠ i) (v : Var → Bool)
    (xs : List (Equational.Term (Equational.CoreSymbol Role) Var))
    (last : Equational.Term (Equational.CoreSymbol Role) Var) :
    profile i v (foldTerm r xs last) = true ↔
      profile i v last = true ∧ ∀ x ∈ xs, profile i v x = true := by
  induction xs with
  | nil => simp [foldTerm]
  | cons x xs ih =>
    change profile i v (choiceTerm r x (foldTerm r xs last)) = true ↔ _
    simp only [profile_choice, ite_eq_right hri, Bool.and_eq_true, ih, List.mem_cons,
      forall_eq_or_imp]
    tauto

@[simp] theorem realize_fold_atom_owner (r : Role) (v : Var → Native Role)
    (xs : List (Equational.Term (Equational.CoreSymbol Role) Var))
    (last : Equational.Term (Equational.CoreSymbol Role) Var) :
    (foldTerm r xs last).realize v = Native.atom r ↔
      last.realize v = Native.atom r ∨ ∃ x ∈ xs, x.realize v = Native.atom r := by
  simp only [realize_eq_atom_iff_profile, profile_fold_owner]

theorem realize_fold_atom_other (r i : Role) (hri : r ≠ i) (v : Var → Native Role)
    (xs : List (Equational.Term (Equational.CoreSymbol Role) Var))
    (last : Equational.Term (Equational.CoreSymbol Role) Var) :
    (foldTerm r xs last).realize v = Native.atom i ↔
      last.realize v = Native.atom i ∧ ∀ x ∈ xs, x.realize v = Native.atom i := by
  simp only [realize_eq_atom_iff_profile, profile_fold_other r i hri]

/-- An upper marker survives an owned fold exactly when at least one
input is upper and every input avoids the owning atom. -/
theorem realize_fold_upper (r : Role) (v : Var → Native Role)
    (xs : List (Equational.Term (Equational.CoreSymbol Role) Var))
    (last : Equational.Term (Equational.CoreSymbol Role) Var) :
    (foldTerm r xs last).realize v = Native.upper ↔
      (last.realize v = Native.upper ∨ ∃ x ∈ xs, x.realize v = Native.upper) ∧
      last.realize v ≠ Native.atom r ∧ ∀ x ∈ xs, x.realize v ≠ Native.atom r := by
  induction xs with
  | nil => simp [foldTerm]; intro h; rw [h]; simp
  | cons x xs ih =>
    change Native.choice r (x.realize v) ((foldTerm r xs last).realize v) = Native.upper ↔ _
    rw [Native.choice_eq_upper, ih]
    simp only [ne_eq, realize_fold_atom_owner]
    simp only [List.mem_cons, exists_eq_or_imp, forall_eq_or_imp]
    simp only [not_or, not_exists, not_and]
    have hup : x.realize v = Native.upper → x.realize v ≠ Native.atom r := by
      intro h; rw [h]; simp
    have hlast : last.realize v = Native.upper → last.realize v ≠ Native.atom r := by
      intro h; rw [h]; simp
    tauto

end KFOL.Core
