module

public import KFOL.Reset.Tables

/-! # The fixed three-value chain separates every reset equation -/

@[expose] public section

namespace KFOL.Reset

universe u v w

variable {Role : Type u} {Var : Type v}

@[simp] theorem chainValue_zero (three : Fin 3 ↪ Role) :
    chainValue three 0 = WinnerSet.singleton (three 0) := rfl

@[simp] theorem chainValue_one (three : Fin 3 ↪ Role) :
    chainValue three 1 =
      (WinnerSet.singleton (three 0)).union (WinnerSet.singleton (three 1)) := rfl

@[simp] theorem chainValue_two (three : Fin 3 ↪ Role) :
    chainValue three 2 = (WinnerSet.singleton (three 2)).union
      ((WinnerSet.singleton (three 0)).union (WinnerSet.singleton (three 1))) := rfl

@[simp] theorem ambiguous_chainValue (three : Fin 3 ↪ Role) (i : Fin 3) :
    (chainValue three i).Ambiguous ↔ i ≠ 0 := by
  have h01 := three.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have h1 : (chainValue three 1).Ambiguous := WinnerSet.ambiguous_of_two_mem _ _ _ h01
    (Or.inl rfl) (Or.inr rfl)
  have h2 : (chainValue three 2).Ambiguous := by
    rw [chainValue_two, WinnerSet.union_comm]
    exact h1.union_left
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  · exact ⟨fun h => False.elim (h (three 0) rfl), fun h => False.elim (h rfl)⟩
  · exact ⟨fun _ => by decide, fun _ => h1⟩
  · exact ⟨fun _ => by decide, fun _ => h2⟩

@[simp] theorem marker_chainValue (three : Fin 3 ↪ Role) (i : Fin 3) :
    three 2 ∈ (chainValue three i).val ↔ i = 2 := by
  have h20 := three.injective.ne (show (2 : Fin 3) ≠ 0 by decide)
  have h21 := three.injective.ne (show (2 : Fin 3) ≠ 1 by decide)
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;>
    simp [chainValue, WinnerSet.union, WinnerSet.singleton, h20, h21]

/-- Three nested values are closed under reset. This is the paper's complete
multiplication table, rather than a bounded equation check. -/
theorem reset_chainValue (three : Fin 3 ↪ Role) (i j : Fin 3) :
    (chainValue three i).reset (chainValue three j) =
      chainValue three (if j = 0 then 0 else max i j) := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl
  all_goals first
    | exact WinnerSet.reset_singleton _ _
    | (rw [WinnerSet.reset_of_ambiguous _ _ ((ambiguous_chainValue three _).mpr (by decide))]
       apply Subtype.ext
       ext r
       simp [chainValue, WinnerSet.union, WinnerSet.singleton, or_comm, or_left_comm, or_assoc])

namespace Term

/-- Assign the marker value only to j, with all other statuses given by B. -/
private noncomputable def markerValuation (three : Fin 3 ↪ Role) (B : Set Var)
    (j i : Var) : WinnerSet Role := by
  classical
  exact chainValue three (if i = j then 2 else if i ∈ B then 1 else 0)

private theorem markerValuation_status (three : Fin 3 ↪ Role) (B : Set Var) (j i : Var) :
    (markerValuation three B j i).Ambiguous ↔ i = j ∨ i ∈ B := by
  classical
  simp only [markerValuation, ambiguous_chainValue]
  by_cases hij : i = j <;> by_cases hi : i ∈ B <;> simp [hij, hi]

private theorem markerValuation_mem (three : Fin 3 ↪ Role) (B : Set Var) (j i : Var) :
    three 2 ∈ (markerValuation three B j i).val ↔ i = j := by
  classical
  by_cases hij : i = j <;> by_cases hi : i ∈ B <;>
    simp [markerValuation, hij, hi]

private theorem marker_eval (t : Term Var) (three : Fin 3 ↪ Role) (B : Set Var) (j : Var) :
    three 2 ∈ (t.eval (markerValuation three B j)).val ↔ t.Selected B j := by
  let C : Set Var := {i | (markerValuation three B j i).Ambiguous}
  have hc : ∀ i, i ≠ j → (i ∈ C ↔ i ∈ B) := by
    intro i hij
    exact (markerValuation_status three B j i).trans (or_iff_right hij)
  rw [mem_eval]
  constructor
  · rintro ⟨i, hi, hm⟩
    obtain rfl := (markerValuation_mem three B j i).mp hm
    exact (t.selected_self_independent C B i hc).mp hi
  · intro hj
    exact ⟨j, (t.selected_self_independent C B j hc).mpr hj,
      (markerValuation_mem three B j j).mpr rfl⟩

/-- Every selector difference has a countervaluation on the fixed chain. -/
theorem selected_iff_of_chain_eq (s t : Term Var) (three : Fin 3 ↪ Role)
    (he : ∀ v : Var → WinnerSet Role, (∀ i, ∃ k, v i = chainValue three k) →
      s.eval v = t.eval v) : ∀ B j, s.Selected B j ↔ t.Selected B j := by
  intro B j
  have hv : ∀ i, ∃ k, markerValuation three B j i = chainValue three k := by
    classical
    intro i
    exact ⟨if i = j then 2 else if i ∈ B then 1 else 0, rfl⟩
  have h := he (markerValuation three B j) hv
  have hm : three 2 ∈ (s.eval (markerValuation three B j)).val ↔
      three 2 ∈ (t.eval (markerValuation three B j)).val := by rw [h]
  exact (s.marker_eval three B j).symm.trans (hm.trans (t.marker_eval three B j))

/-- Equal selectors determine all mixed winner-set valuations. -/
theorem eval_eq_of_selected (s t : Term Var)
    (h : ∀ B j, s.Selected B j ↔ t.Selected B j) (v : Var → WinnerSet Role) :
    s.eval v = t.eval v := by
  apply Subtype.ext
  ext r
  rw [mem_eval, mem_eval]
  exact exists_congr (fun j => and_congr (h _ j) Iff.rfl)

/-- The fixed three-value chain tests equality, with no finiteness assumption
on variable or role types. -/
theorem eval_eq_iff_chain (s t : Term Var) (three : Fin 3 ↪ Role) :
    (∀ v : Var → WinnerSet Role, s.eval v = t.eval v) ↔
      ∀ v : Var → WinnerSet Role, (∀ i, ∃ k, v i = chainValue three k) →
        s.eval v = t.eval v :=
  ⟨fun h v _ => h v, fun h => s.eval_eq_of_selected t (s.selected_iff_of_chain_eq t three h)⟩

/-- Canonical minimal tables exactly classify all reset term operations. -/
theorem eval_eq_iff_table [DecidableEq Var] (s t : Term Var) (three : Fin 3 ↪ Role) :
    (∀ v : Var → WinnerSet Role, s.eval v = t.eval v) ↔ s.table = t.table :=
  ⟨fun h => (s.table_eq_iff_selected t).mpr
      (s.selected_iff_of_chain_eq t three (fun v _ => h v)),
    fun h => s.eval_eq_of_selected t ((s.table_eq_iff_selected t).mp h)⟩

/-- The identity theory is independent of the role set once three roles exist. -/
theorem eval_eq_iff_roles {Role' : Type w} (s t : Term Var)
    (three : Fin 3 ↪ Role) (three' : Fin 3 ↪ Role') :
    (∀ v : Var → WinnerSet Role, s.eval v = t.eval v) ↔
      ∀ v : Var → WinnerSet Role', s.eval v = t.eval v := by
  classical
  rw [eval_eq_iff_table s t three, eval_eq_iff_table s t three']

end Term
/-- The canonical-table theorem is directly usable by the generic equational
basis API; no separate reset validity predicate or syntax transport is needed. -/
theorem identity_holds_iff_table (three : Fin 3 ↪ Role) (e : Equational.Identity Symbol) :
    letI := structureOf (WinnerSet.reset (Role := Role))
    e.Holds (WinnerSet Role) ↔ Term.table e.lhs = Term.table e.rhs := by
  let _ := structureOf (WinnerSet.reset (Role := Role))
  exact Term.eval_eq_iff_table e.lhs e.rhs three

end KFOL.Reset
