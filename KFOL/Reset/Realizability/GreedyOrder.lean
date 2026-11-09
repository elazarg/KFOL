module

public import KFOL.Reset.Realizability.Model
public import KFOL.Reset.Realizability.Size

/-! # A computable accessible order and its path specification -/

@[expose] public section

namespace KFOL.Reset.GuardTable

universe v

variable {Var : Type v} [LinearOrder Var] (G : GuardTable Var)

@[simp] theorem mem_greedyCandidates (A : Finset Var) (xs : List Var) (j : Var) :
    j ∈ G.greedyCandidates A xs ↔ j ∈ A ∧ j ∉ insert G.root xs.toFinset ∧
      G.Enabled ((insert G.root xs.toFinset : Finset Var) : Set Var) j := by
  simp only [greedyCandidates, Finset.mem_filter, Finset.mem_sdiff, Enabled]
  tauto

private theorem support_append (r j : Var) (xs : List Var) :
    insert r (xs ++ [j]).toFinset = insert j (insert r xs.toFinset) := by
  simp [Finset.insert_comm]

theorem greedyOrder_subset {A : Finset Var} (hr : G.root ∈ A) (k : ℕ) :
    insert G.root (G.greedyOrder A k).toFinset ⊆ A := by
  induction k with
  | zero => simpa [greedyOrder] using hr
  | succ k ih =>
    simp only [greedyOrder]
    split
    next h =>
      rw [support_append]
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact ((G.mem_greedyCandidates _ _ _).mp (Finset.min'_mem _ h)).1
      · exact ih hj
    next => exact ih

theorem greedyOrder_mono_step (A : Finset Var) (k : ℕ) :
    insert G.root (G.greedyOrder A k).toFinset ⊆
      insert G.root (G.greedyOrder A (k + 1)).toFinset := by
  simp only [greedyOrder]
  split
  next => rw [support_append]; exact Finset.subset_insert _ _
  next => exact subset_rfl

/-- Every chosen extension is feasible in the independent candidate model. -/
theorem greedyOrder_feasible [Fintype Var] (h : G.WellFormed) (A : Finset Var) (k : ℕ) :
    (G.antimatroid h).FeasibleOrder (G.greedyOrder A k) := by
  induction k with
  | zero => exact RootedAntimatroid.FeasibleOrder.nil _
  | succ k ih =>
    simp only [greedyOrder]
    split
    next hn =>
      obtain ⟨_, hf, he⟩ := (G.mem_greedyCandidates _ _ _).mp (Finset.min'_mem _ hn)
      apply ih.append _ hf
      exact Constructible.insert _ ih.support_mem hf he
    next => exact ih

/-- Greedy choices reach every constructible target containing the root. -/
theorem greedyOrder_support {A : Finset Var} (hr : G.root ∈ A) (hA : G.Constructible A) :
    insert G.root (G.greedyOrder A A.card).toFinset = A := by
  have bound (k : ℕ) : k ≤ (insert G.root (G.greedyOrder A k).toFinset).card ∨
      insert G.root (G.greedyOrder A k).toFinset = A := by
    induction k with
    | zero => exact Or.inl (Nat.zero_le _)
    | succ k ih =>
      by_cases he : insert G.root (G.greedyOrder A k).toFinset = A
      · exact Or.inr (Finset.Subset.antisymm (G.greedyOrder_subset hr _) (by
          intro j hj
          exact G.greedyOrder_mono_step A k ((Finset.ext_iff.mp he j).mpr hj)))
      · have hns : ¬A ⊆ insert G.root (G.greedyOrder A k).toFinset :=
          fun hs => he (Finset.Subset.antisymm (G.greedyOrder_subset hr k) hs)
        obtain ⟨j, hj, hf, hen⟩ := hA.exists_enabled hns
        have hn : (G.greedyCandidates A (G.greedyOrder A k)).Nonempty :=
          ⟨j, (G.mem_greedyCandidates _ _ j).mpr ⟨hj, hf, hen⟩⟩
        have hfresh := ((G.mem_greedyCandidates _ _ _).mp (Finset.min'_mem _ hn)).2.1
        have hc : (insert G.root (G.greedyOrder A (k + 1)).toFinset).card =
            (insert G.root (G.greedyOrder A k).toFinset).card + 1 := by
          simp only [greedyOrder, dite_eq_left hn, support_append,
            Finset.card_insert_of_notMem hfresh]
        have hk := ih.resolve_right he
        exact Or.inl (by omega)
  rcases bound A.card with hc | he
  · exact Finset.eq_of_subset_of_card_le (G.greedyOrder_subset hr _) hc
  · exact he

/-- The executable path has the desired support and introduces only permitted
selectors, with an exact count of primitive occurrences. -/
theorem greedyPath_spec [Fintype Var] (h : G.WellFormed) {A : Finset Var}
    (hr : G.root ∈ A) (hA : G.Constructible A) :
    (G.greedyPath A).root = G.root ∧ (G.greedyPath A).varFinset = A ∧
      (∀ B j, (G.greedyPath A).Selected B j → G.Enabled B j) ∧
      (G.greedyPath A).size + 1 = 2 * A.card := by
  have ho := G.greedyOrder_feasible h A A.card
  have hs := G.greedyOrder_support hr hA
  refine ⟨Term.root_pathTerm _ _, ?_, ?_, ?_⟩
  · simpa only [greedyPath, Term.varFinset_pathTerm, List.toFinset_reverse] using hs
  · intro B j hj
    exact (G.ready_antimatroid h B j).mp (ho.path_ready B j hj)
  · have hn : G.root ∉ (G.greedyOrder A A.card).toFinset :=
      fun hm => ho.root_not_mem (List.mem_toFinset.mp hm)
    have hc := congrArg Finset.card hs
    rw [Finset.card_insert_of_notMem hn, List.toFinset_card_of_nodup ho.nodup] at hc
    simp only [greedyPath, Term.size_pathTerm, List.length_reverse]
    omega

end KFOL.Reset.GuardTable
