module

public import KFOL.Reset.Antimatroid.Synthesis

/-! # Exact primitive-tree sizes for the compact path construction -/

@[expose] public section

namespace KFOL.Reset

universe v

namespace Term

variable {Var : Type v}

private theorem size_fold (t : Term Var) (xs : List Var) :
    size (xs.foldl (fun t i => step t (.var i)) t) = t.size + 2 * xs.length := by
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, size_step, size_var, List.length_cons]
    omega

@[simp] theorem size_pathTerm (r : Var) (xs : List Var) :
    size (pathTerm r xs) = 2 * xs.length + 1 := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    simp only [pathTerm, size_step, size_fold, size_var, List.length_cons]
    omega

/-- The added operation per join is included in the bound. -/
theorem size_joinPaths_le (r : Var) (ts : List (Term Var)) (L : ℕ)
    (h : ∀ t ∈ ts, t.size + 1 ≤ L) : size (joinPaths r ts) ≤ 1 + ts.length * L := by
  induction ts with
  | nil => simp [joinPaths]
  | cons t ts ih =>
    have ht := h t List.mem_cons_self
    have hs := ih (fun s hs => h s (List.mem_cons_of_mem _ hs))
    change 1 + t.size + size (joinPaths r ts) ≤ 1 + (ts.length + 1) * L
    rw [Nat.add_mul]
    omega

end Term

namespace RootedAntimatroid

variable {Var : Type v} [DecidableEq Var]

/-- A feasible support has a path with exactly one leaf per position. -/
theorem exists_path_sized (F : RootedAntimatroid Var) {A : Finset Var}
    (hA : A ∈ F.feasible) (hne : A.Nonempty) :
    ∃ t : Term Var, t.root = F.root ∧ t.varFinset = A ∧
      (∀ B j, t.Selected B j → F.Ready B j) ∧ t.size + 1 = 2 * A.card := by
  obtain ⟨xs, hxs, hs⟩ := F.exists_order hA hne
  refine ⟨Term.pathTerm F.root xs.reverse, Term.root_pathTerm _ _, ?_, hxs.path_ready, ?_⟩
  · simpa only [Term.varFinset_pathTerm, List.toFinset_reverse] using hs
  · have hn : F.root ∉ xs.toFinset := by simpa only [List.mem_toFinset] using hxs.root_not_mem
    have hc := congrArg Finset.card hs
    rw [Finset.card_insert_of_notMem hn, List.toFinset_card_of_nodup hxs.nodup] at hc
    simp only [Term.size_pathTerm, List.length_reverse]
    omega

end RootedAntimatroid
end KFOL.Reset
