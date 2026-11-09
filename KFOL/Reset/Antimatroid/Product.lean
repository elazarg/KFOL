module

public import KFOL.Reset.Antimatroid.Basic

/-! # The reset operation on rooted antimatroid families -/

@[expose] public section

namespace KFOL.Reset.RootedAntimatroid

universe v

variable {Var : Type v} [DecidableEq Var]

/-- The independent family product preserves the finite antimatroid axioms. -/
def product (F G : RootedAntimatroid Var) : RootedAntimatroid Var where
  ground := F.ground ∪ G.ground
  feasible := familyProduct F.feasible G.feasible
  root := G.root
  empty_mem := Or.inl rfl
  ground_mem := Or.inr ⟨F.ground, F.ground_mem, G.ground, G.ground_mem,
    G.ground_nonempty, rfl⟩
  subset_ground := by
    rintro D (rfl | ⟨A, hA, C, hC, _, rfl⟩)
    · exact Finset.empty_subset _
    · exact Finset.union_subset_union (F.subset_ground _ hA) (G.subset_ground _ hC)
  union_mem := by
    intro D hD E hE
    rcases hD with rfl | ⟨A, hA, C, hC, hne, rfl⟩
    · simpa only [Finset.empty_union] using hE
    rcases hE with rfl | ⟨A', hA', C', hC', _, rfl⟩
    · rw [Finset.union_empty]
      exact Or.inr ⟨A, hA, C, hC, hne, rfl⟩
    refine Or.inr ⟨A ∪ A', F.union_mem _ hA _ hA', C ∪ C', G.union_mem _ hC _ hC',
      hne.mono Finset.subset_union_left, ?_⟩
    ext x
    simp only [Finset.mem_union]
    tauto
  accessible := by
    rintro D (rfl | ⟨A, hA, C, hC, hne, rfl⟩) hD
    · exact False.elim (Finset.not_nonempty_empty hD)
    by_cases hAC : A ⊆ C
    · have hu : A ∪ C = C := Finset.union_eq_right.mpr hAC
      obtain ⟨c, hc, hCe⟩ := G.accessible C hC hne
      refine ⟨c, Finset.mem_union_right _ hc, ?_⟩
      rw [hu]
      by_cases he : C.erase c = ∅
      · exact Or.inl he
      · exact Or.inr ⟨∅, F.empty_mem, C.erase c, hCe,
          Finset.nonempty_iff_ne_empty.mpr he, (Finset.empty_union _).symm⟩
    · obtain ⟨a, ha, _, A', hA', hu⟩ := F.remove_from_union hA hAC
      exact ⟨a, Finset.mem_union_left _ ha,
        Or.inr ⟨A', hA', C, hC, hne, hu.symm⟩⟩
  root_mem := Or.inr ⟨∅, F.empty_mem, {G.root}, G.root_mem,
    Finset.singleton_nonempty _, (Finset.empty_union _).symm⟩
  singleton_unique := by
    rintro a (he | ⟨A, _, C, hC, hne, hu⟩)
    · exact False.elim (Finset.singleton_ne_empty a he)
    have hr := G.root_mem_of_nonempty hC hne
    have hm : G.root ∈ ({a} : Finset Var) := hu ▸ Finset.mem_union_right A hr
    exact (Finset.mem_singleton.mp hm).symm

@[simp] theorem product_ground (F G : RootedAntimatroid Var) :
    (F.product G).ground = F.ground ∪ G.ground := rfl

@[simp] theorem product_root (F G : RootedAntimatroid Var) : (F.product G).root = G.root := rfl

/-- Family readiness obeys the reset selector recursion, including overlaps
between the two grounds and repeated variable labels. -/
theorem ready_product (F G : RootedAntimatroid Var) (B : Set Var) (j : Var) :
    (F.product G).Ready B j ↔ G.Ready B j ∨ (G.root ∈ B ∧ F.Ready B j) := by
  constructor
  · rintro ⟨D, hD, hj, hDB⟩
    rcases hD with rfl | ⟨A, hA, C, hC, hne, rfl⟩
    · simp at hj
    have hCB : (C : Set Var) ⊆ insert j B := fun _ hx => hDB (Finset.mem_union_right _ hx)
    by_cases hjC : j ∈ C
    · exact Or.inl ⟨C, hC, hjC, hCB⟩
    · have hrC := G.root_mem_of_nonempty hC hne
      have hrB : G.root ∈ B := by
        rcases Set.mem_insert_iff.mp (hCB hrC) with hr | hr
        · exact False.elim (hjC (hr ▸ hrC))
        · exact hr
      have hjA := (Finset.mem_union.mp hj).resolve_right hjC
      exact Or.inr ⟨hrB, A, hA, hjA, fun _ hx => hDB (Finset.mem_union_left _ hx)⟩
  · rintro (⟨C, hC, hjC, hCB⟩ | ⟨hrB, A, hA, hjA, hAB⟩)
    · exact ⟨C, Or.inr ⟨∅, F.empty_mem, C, hC, ⟨j, hjC⟩,
        (Finset.empty_union _).symm⟩, hjC, hCB⟩
    · refine ⟨A ∪ {G.root}, Or.inr ⟨A, hA, {G.root}, G.root_mem,
        Finset.singleton_nonempty _, rfl⟩, Finset.mem_union_left _ hjA, ?_⟩
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hAB hx
      · have he := Finset.mem_singleton.mp hx
        exact Set.mem_insert_of_mem j (he ▸ hrB)

end KFOL.Reset.RootedAntimatroid
