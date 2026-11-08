module

public import KFOL.Reset.Tables

/-! # Canonical tables respect actual mathlib term substitution -/

@[expose] public section

namespace KFOL.Reset.Term

universe u v w

variable {Var : Type v} {Var' : Type w}

@[simp] theorem varFinset_step [DecidableEq Var] (s t : Term Var) :
    (step s t).varFinset = s.varFinset ∪ t.varFinset := by
  simp [step, FirstOrder.Language.Term.varFinset, Finset.univ_fin2]

/-- Unused declared positions never contribute an output. -/
theorem mem_varFinset_of_selected [DecidableEq Var] (t : Term Var) (B : Set Var) (j : Var)
    (hj : t.Selected B j) : j ∈ t.varFinset := by
  induction t using induction_reset with
  | var i =>
    simpa only [Selected, FirstOrder.Language.Term.varFinset, Finset.mem_singleton] using hj
  | step s t hs ht =>
    rw [varFinset_step]
    rcases hj with hj | ⟨_, hj⟩
    · exact Finset.mem_union_right _ (ht hj)
    · exact Finset.mem_union_left _ (hs hj)

/-- Evaluation/substitution is mathlib's structural substitution theorem. -/
theorem eval_subst {Role : Type u} (t : Term Var) (s : Var → Term Var')
    (v : Var' → WinnerSet Role) :
    eval (t.subst s) v = t.eval (fun i => (s i).eval v) := by
  let _ := structureOf (WinnerSet.reset (Role := Role))
  exact FirstOrder.Language.Term.realize_subst

/-- The explicit finite guard composition has the substituted selector. -/
theorem selected_iff_composedGuards [DecidableEq Var] [DecidableEq Var']
    (t : Term Var) (s : Var → Term Var') (B : Set Var') (j : Var') :
    Selected (t.subst s) B j ↔ ∃ A ∈ composedGuards t s j, (A : Set Var') ⊆ B := by
  rw [selected_subst]
  constructor
  · rintro ⟨i, hi, hj⟩
    have himem := t.mem_varFinset_of_selected _ i hi
    obtain ⟨A, hA, hAB⟩ := (t.selected_iff_table _ i).mp hi
    obtain ⟨C, hC, hCB⟩ := ((s i).selected_iff_table B j).mp hj
    refine ⟨A.image (fun k => (s k).root) ∪ C, ?_, ?_⟩
    · exact Finset.mem_biUnion.mpr ⟨i, himem,
        Finset.mem_biUnion.mpr ⟨A, hA, Finset.mem_image.mpr ⟨C, hC, rfl⟩⟩⟩
    · intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
        exact hAB hk
      · exact hCB hx
  · rintro ⟨D, hD, hDB⟩
    obtain ⟨i, _, hD⟩ := Finset.mem_biUnion.mp hD
    obtain ⟨A, hA, hD⟩ := Finset.mem_biUnion.mp hD
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hD
    refine ⟨i, (t.selected_iff_table _ i).mpr ⟨A, hA, ?_⟩,
      ((s i).selected_iff_table B j).mpr ⟨C, hC, ?_⟩⟩
    · intro k hk
      exact hDB (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k, hk, rfl⟩))
    · intro x hx
      exact hDB (Finset.mem_union_right _ hx)

/-- Equation `reset:eq:substitution`: canonical tables compose by taking unions
of root-translated outer guards and inner guards, then deleting nonminimal sets. -/
theorem table_subst [DecidableEq Var] [DecidableEq Var']
    (t : Term Var) (s : Var → Term Var') (j : Var') :
    table (t.subst s) j = minimize (composedGuards t s j) := by
  apply minimize_eq_of_upward
  intro B
  exact ((selected_iff_guard (t.subst s) B j).symm).trans
    (t.selected_iff_composedGuards s B j)

end KFOL.Reset.Term
