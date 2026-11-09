module

public import KFOL.Reset.Antimatroid.Product

/-! # Every reset term has a rooted antimatroid representation -/

@[expose] public section

namespace KFOL.Reset

universe v

variable {Var : Type v} [DecidableEq Var]

namespace RootedAntimatroid

/-- The family with just the empty set and one singleton. -/
def singleton (i : Var) : RootedAntimatroid Var where
  ground := {i}
  feasible := {A | A = ∅ ∨ A = {i}}
  root := i
  empty_mem := Or.inl rfl
  ground_mem := Or.inr rfl
  subset_ground := by
    rintro A (rfl | rfl)
    · exact Finset.empty_subset _
    · exact subset_rfl
  union_mem := by
    rintro A (rfl | rfl) B (rfl | rfl) <;> simp
  accessible := by
    rintro A (rfl | rfl) hne
    · simp at hne
    · exact ⟨i, Finset.mem_singleton_self _, Or.inl (by simp)⟩
  root_mem := Or.inr rfl
  singleton_unique := by
    rintro a (he | he)
    · simp at he
    · have hm : a ∈ ({i} : Finset Var) := he ▸ Finset.mem_singleton_self a
      exact Finset.mem_singleton.mp hm

@[simp] theorem ready_singleton (i j : Var) (B : Set Var) :
    (singleton i).Ready B j ↔ j = i := by
  constructor
  · rintro ⟨A, hA, hj, _⟩
    rcases hA with rfl | rfl
    · simp at hj
    · exact Finset.mem_singleton.mp hj
  · intro he
    subst j
    exact (singleton i).ready_root B

end RootedAntimatroid

namespace Term

/-- Interpret a term by the independent feasible-family product. -/
def antimatroid : Term Var → RootedAntimatroid Var
  | .var i => RootedAntimatroid.singleton i
  | .func .reset args => (antimatroid (args 0)).product (antimatroid (args 1))

@[simp] theorem antimatroid_step (s t : Term Var) :
    antimatroid (step s t) = s.antimatroid.product t.antimatroid := rfl

@[simp] theorem antimatroid_root (t : Term Var) : t.antimatroid.root = t.root := by
  induction t using induction_reset with
  | var => rfl
  | step s t _ ih => exact ih

@[simp] theorem antimatroid_ground (t : Term Var) : t.antimatroid.ground = t.varFinset := by
  induction t using induction_reset with
  | var => rfl
  | step s t hs ht =>
    simpa only [antimatroid_step, RootedAntimatroid.product_ground, varFinset_step] using
      congrArg₂ (fun A B : Finset Var => A ∪ B) hs ht

/-- Readiness and the independently defined selector agree on every status set. -/
theorem ready_antimatroid (t : Term Var) (B : Set Var) (j : Var) :
    t.antimatroid.Ready B j ↔ t.Selected B j := by
  induction t using induction_reset with
  | var i => exact RootedAntimatroid.ready_singleton i j B
  | step s t hs ht =>
    rw [antimatroid_step, RootedAntimatroid.ready_product, antimatroid_root, hs, ht, selected_step]

/-- The recursive family is exactly the feasible-set formula in the paper. -/
theorem feasible_antimatroid (t : Term Var) : t.antimatroid.feasible = t.feasible := by
  ext A
  constructor
  · intro hA
    refine ⟨?_, ?_⟩
    · rw [← antimatroid_ground]
      exact t.antimatroid.subset_ground A hA
    · intro j hj
      exact (t.ready_antimatroid _ j).mp ((t.antimatroid.feasible_iff_ready A).mp hA j hj)
  · rintro ⟨_, hA⟩
    exact (t.antimatroid.feasible_iff_ready A).mpr (fun j hj =>
      (t.ready_antimatroid _ j).mpr (hA j hj))

omit [DecidableEq Var] in
/-- An atomic root status prevents any other position from being selected. -/
theorem selected_of_root_absent (t : Term Var) (B : Set Var) (j : Var) :
    t.root ∉ B → (t.Selected B j ↔ j = t.root) := by
  induction t using induction_reset with
  | var => exact fun _ => Iff.rfl
  | step s t _ ih =>
    intro hr
    change t.root ∉ B at hr
    simpa only [selected_step, root_step, hr, false_and, or_false] using ih hr

omit [DecidableEq Var] in
/-- For terms sharing a root, reset is union of selectors. -/
theorem selected_common_root (s t : Term Var) (hr : s.root = t.root) (B : Set Var) (j : Var) :
    (step s t).Selected B j ↔ s.Selected B j ∨ t.Selected B j := by
  rw [selected_step]
  constructor
  · rintro (hj | ⟨_, hj⟩)
    · exact Or.inr hj
    · exact Or.inl hj
  · rintro (hj | hj)
    · by_cases hb : t.root ∈ B
      · exact Or.inr ⟨hb, hj⟩
      · have he := (s.selected_of_root_absent B j (hr ▸ hb)).mp hj
        rw [he, hr]
        exact Or.inl (t.selected_root B)
    · exact Or.inl hj

/-- All syntactically used inputs contribute when all of them are ambiguous. -/
theorem selected_of_support_subset (t : Term Var) (B : Set Var) :
    (t.varFinset : Set Var) ⊆ B → ∀ j ∈ t.varFinset, t.Selected B j := by
  induction t using induction_reset with
  | var i =>
    intro _ j hj
    exact Finset.mem_singleton.mp hj
  | step s t hs ht =>
    rw [varFinset_step]
    intro hB j hj
    have hS : (s.varFinset : Set Var) ⊆ B := fun _ hj => hB (Finset.mem_union_left _ hj)
    have hT : (t.varFinset : Set Var) ⊆ B := fun _ hj => hB (Finset.mem_union_right _ hj)
    rcases Finset.mem_union.mp hj with hj | hj
    · exact Or.inr ⟨hT (t.mem_varFinset_of_selected Set.univ t.root (t.selected_root Set.univ)),
        hs hS j hj⟩
    · exact Or.inl (ht hT j hj)

/-- A used input contributes if every other used input is ambiguous. -/
theorem selected_of_support_insert (t : Term Var) (B : Set Var) (j : Var)
    (hj : j ∈ t.varFinset) (hB : (t.varFinset : Set Var) ⊆ insert j B) : t.Selected B j := by
  have he := t.selected_of_support_subset (insert j B) hB j hj
  exact (t.selected_self_independent (insert j B) B j (by
    intro i hij
    simp [hij])).mp he

end Term
end KFOL.Reset
