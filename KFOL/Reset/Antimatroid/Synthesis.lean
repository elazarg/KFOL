module

public import KFOL.Reset.Antimatroid.Paths

/-! # Every finite rooted antimatroid is represented by a reset term

This existence construction joins accessible-order paths for feasible sets.
Compact synthesis and polynomial bounds are separate algorithmic obligations.
-/

@[expose] public section

namespace KFOL.Reset

universe v

namespace Term

variable {Var : Type v}

/-- Join common-root terms, with the root projection as the empty join. -/
def joinPaths (r : Var) (ts : List (Term Var)) : Term Var := ts.foldr step (.var r)

@[simp] theorem root_joinPaths (r : Var) (ts : List (Term Var)) : root (joinPaths r ts) = r := by
  induction ts with
  | nil => rfl
  | cons t ts ih => exact ih

theorem selected_joinPaths (r : Var) (ts : List (Term Var)) (B : Set Var) (j : Var)
    (hroot : ∀ t ∈ ts, t.root = r) :
    Selected (joinPaths r ts) B j ↔ j = r ∨ ∃ t ∈ ts, t.Selected B j := by
  induction ts with
  | nil => simp [joinPaths]
  | cons t ts ih =>
    change (step t (joinPaths r ts)).Selected B j ↔ _
    rw [selected_common_root t _ ((hroot t List.mem_cons_self).trans
      (root_joinPaths r ts).symm), ih (fun s hs => hroot s (List.mem_cons_of_mem _ hs))]
    constructor
    · rintro (hj | hj | ⟨s, hs, hj⟩)
      · exact Or.inr ⟨t, List.mem_cons_self, hj⟩
      · exact Or.inl hj
      · exact Or.inr ⟨s, List.mem_cons_of_mem _ hs, hj⟩
    · rintro (hj | ⟨s, hs, hj⟩)
      · exact Or.inr (Or.inl hj)
      · rcases List.mem_cons.mp hs with he | hs
        · subst s
          exact Or.inl hj
        · exact Or.inr (Or.inr ⟨s, hs, hj⟩)

end Term

namespace RootedAntimatroid

variable {Var : Type v} [DecidableEq Var]

/-- Full representation, with no certificate or realizability assumption:
the independently axiomatized family itself supplies all required paths. -/
theorem exists_term (F : RootedAntimatroid Var) : ∃ t : Term Var, t.antimatroid = F := by
  classical
  let S := F.ground.powerset.filter (fun A => A ∈ F.feasible ∧ A.Nonempty)
  have hp : ∀ A : S, ∃ t : Term Var, t.root = F.root ∧ t.varFinset = A.val ∧
      ∀ B j, t.Selected B j → F.Ready B j := by
    intro A
    have hh := (Finset.mem_filter.mp A.property).2
    exact F.exists_path hh.1 hh.2
  choose pieces hroots hvars hready using hp
  let ts := S.attach.toList.map pieces
  have hroot : ∀ t ∈ ts, t.root = F.root := by
    rintro t ht
    obtain ⟨A, _, rfl⟩ := List.mem_map.mp ht
    exact hroots A
  let t := Term.joinPaths F.root ts
  have hs : ∀ B j, t.Selected B j ↔ F.Ready B j := by
    intro B j
    rw [Term.selected_joinPaths F.root ts B j hroot]
    constructor
    · rintro (he | ⟨s, hmem, hj⟩)
      · subst j
        exact F.ready_root B
      · obtain ⟨A, _, rfl⟩ := List.mem_map.mp hmem
        exact hready A B j hj
    · rintro ⟨A, hA, hjA, hAB⟩
      have hm : A ∈ S := Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (F.subset_ground _ hA), hA, ⟨j, hjA⟩⟩
      let i : S := ⟨A, hm⟩
      have hmem : pieces i ∈ ts := List.mem_map.mpr ⟨i, by simp, rfl⟩
      have hj : j ∈ (pieces i).varFinset := by rw [hvars]; exact hjA
      have hsub : ((pieces i).varFinset : Set Var) ⊆ insert j B := by
        rw [hvars]
        exact hAB
      exact Or.inr ⟨pieces i, hmem, (pieces i).selected_of_support_insert B j hj hsub⟩
  refine ⟨t, ?_⟩
  apply RootedAntimatroid.ext
  ext A
  constructor
  · intro hA
    apply (F.feasible_iff_ready A).mpr
    intro j hj
    exact (hs A j).mp ((t.ready_antimatroid A j).mp
      ((t.antimatroid.feasible_iff_ready A).mp hA j hj))
  · intro hA
    apply (t.antimatroid.feasible_iff_ready A).mpr
    intro j hj
    exact (t.ready_antimatroid A j).mpr ((hs A j).mpr
      ((F.feasible_iff_ready A).mp hA j hj))

end RootedAntimatroid
end KFOL.Reset
