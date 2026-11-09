module

import KFOL.Algebra.Semilattice

namespace KFOL.PublicFoldsRegression

universe u v w

/-- Every finite nonempty family of continuations folds to an actual binary
term; its owner-absorption and union cases hold for every valuation. -/
theorem finite_choices {Role : Type u} {Var : Type v} {Index : Type w}
    (r : Role) (S : Finset Index) (hS : S.Nonempty) (terms : Index → Term Role Var) :
    (∃ t : Term Role Var, ∀ v : Var → WinnerSet Role,
      t.eval v = WinnerSet.choiceFold r S hS (fun i => (terms i).eval v)) ∧
    (∀ v : Var → WinnerSet Role,
      WinnerSet.choiceFold r S hS (fun i => (terms i).eval v) = WinnerSet.singleton r ↔
        ∃ i ∈ S, (terms i).eval v = WinnerSet.singleton r) ∧
    (∀ v : Var → WinnerSet Role, (∀ i ∈ S, (terms i).eval v ≠ WinnerSet.singleton r) →
      ∀ a : Role, a ∈ (WinnerSet.choiceFold r S hS (fun i => (terms i).eval v)).val ↔
        ∃ i ∈ S, a ∈ ((terms i).eval v).val) :=
  ⟨Term.exists_choice_fold r S hS terms,
    fun v => WinnerSet.choiceFold_eq_owner_iff r S hS (fun i => (terms i).eval v),
    fun v hn a => WinnerSet.mem_choiceFold_of_no_owner r S hS (fun i => (terms i).eval v) hn a⟩

example : WinnerSet.choiceFold (0 : Fin 3) ({0,1,2} : Finset (Fin 3))
    (by simp) WinnerSet.singleton = WinnerSet.singleton 0 := by
  apply (WinnerSet.choiceFold_eq_owner_iff _ _ _ _).mpr
  exact ⟨0,by simp,rfl⟩

example : ∃ t : Term (Fin 3) (Fin 3), ∀ v : Fin 3 → WinnerSet (Fin 3),
    t.eval v = WinnerSet.choiceFold 0 ({0,1,2} : Finset (Fin 3)) (by simp) v := by
  simpa only [Term.eval] using Term.exists_choice_fold (Role := Fin 3) (Var := Fin 3)
    0 ({0,1,2} : Finset (Fin 3)) (by simp) Term.var

end KFOL.PublicFoldsRegression

#print axioms KFOL.WinnerSet.choiceSemilattice
#print axioms KFOL.WinnerSet.choiceFold_eq_owner_iff
#print axioms KFOL.Term.exists_choice_fold
