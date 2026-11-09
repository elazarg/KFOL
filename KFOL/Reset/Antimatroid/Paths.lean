module

public import KFOL.Reset.Antimatroid.Term
public import KFOL.Reset.Antimatroid.Orders
public import KFOL.Reset.Basis.Coverage

/-! # Accessible orders give genuine common-root reset paths -/

@[expose] public section

namespace KFOL.Reset

universe v

variable {Var : Type v} [DecidableEq Var]

namespace Term

omit [DecidableEq Var] in
@[simp] theorem root_pathTerm (r : Var) (xs : List Var) : root (pathTerm r xs) = r := by
  cases xs <;> rfl

omit [DecidableEq Var] in
theorem pathTerm_append (r q : Var) (xs : List Var) :
    pathTerm r (xs ++ [q]) = step (pathTerm q xs) (.var r) := by
  cases xs <;> simp [pathTerm, List.foldl_append]

private theorem varFinset_fold (t : Term Var) (xs : List Var) :
    (xs.foldl (fun t i => step t (.var i)) t).varFinset = t.varFinset ∪ xs.toFinset := by
  induction xs generalizing t with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, varFinset_step, FirstOrder.Language.Term.varFinset,
      List.toFinset_cons]
    ext j
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
    tauto

@[simp] theorem varFinset_pathTerm (r : Var) (xs : List Var) :
    (pathTerm r xs).varFinset = insert r xs.toFinset := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    simp only [pathTerm, varFinset_step, varFinset_fold, FirstOrder.Language.Term.varFinset,
      List.toFinset_cons]
    ext j
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
    tauto

omit [DecidableEq Var] in
/-- Path selection is the already checked suffix predicate, including repeats. -/
theorem selected_pathTerm (r : Var) (xs : List Var) (B : Set Var) (j : Var) :
    Selected (pathTerm r xs) B j ↔ WordSelected (xs ++ [r]) B j := by
  induction xs using List.reverseRecOn generalizing r with
  | nil => simp [pathTerm, WordSelected]
  | append_singleton xs q ih =>
    rw [pathTerm_append, selected_step, root_var, selected_var, ih]
    exact (wordSelected_append (xs ++ [q]) r B j).symm

end Term

namespace RootedAntimatroid.FeasibleOrder

variable {F : RootedAntimatroid Var} {xs : List Var}

/-- Reversing a feasible order yields a path whose every contribution is
already permitted by the original family. -/
theorem path_ready (h : F.FeasibleOrder xs) (B : Set Var) (j : Var)
    (hj : Term.Selected (Term.pathTerm F.root xs.reverse) B j) : F.Ready B j := by
  rw [Term.selected_pathTerm, wordSelected_append] at hj
  rcases hj with rfl | ⟨hrB, hj⟩
  · exact F.ready_root B
  · obtain ⟨before, after, he, hafter⟩ := (wordSelected_iff xs.reverse B j).mp hj
    have hx : xs = after.reverse ++ j :: before.reverse := by
      simpa [List.reverse_append, List.reverse_cons, List.append_assoc] using
        congrArg List.reverse he
    refine ⟨insert j (insert F.root after.reverse.toFinset), h.prefix_insert hx,
      Finset.mem_insert_self _ _, ?_⟩
    intro x hm
    rcases Finset.mem_insert.mp hm with rfl | hm
    · exact Or.inl rfl
    rcases Finset.mem_insert.mp hm with rfl | hm
    · exact Set.mem_insert_of_mem j hrB
    · exact Set.mem_insert_of_mem j (hafter x (by simpa using hm))

end RootedAntimatroid.FeasibleOrder

namespace RootedAntimatroid

/-- One accessible-order path realizes every member of its feasible support
without introducing any readiness not allowed by the family. -/
theorem exists_path (F : RootedAntimatroid Var) {A : Finset Var}
    (hA : A ∈ F.feasible) (hne : A.Nonempty) :
    ∃ t : Term Var, t.root = F.root ∧ t.varFinset = A ∧
      ∀ B j, t.Selected B j → F.Ready B j := by
  obtain ⟨xs, hxs, hs⟩ := F.exists_order hA hne
  refine ⟨Term.pathTerm F.root xs.reverse, Term.root_pathTerm _ _, ?_, hxs.path_ready⟩
  simpa only [Term.varFinset_pathTerm, List.toFinset_reverse] using hs

end RootedAntimatroid
end KFOL.Reset
