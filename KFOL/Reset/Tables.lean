module

public import KFOL.Reset.Selection
public import Mathlib.Data.Finset.Max

/-! # Canonical finite guard antichains and table completeness -/

@[expose] public section

namespace KFOL.Reset.Term

universe v

variable {Var : Type v} [DecidableEq Var]

@[simp] theorem guards_step (s t : Term Var) (j : Var) :
    (step s t).guards j = t.guards j ∪ (s.guards j).image (insert t.root) := rfl

/-- The structural guards give exactly the mixed-input selector. -/
theorem selected_iff_guard (t : Term Var) (B : Set Var) (j : Var) :
    t.Selected B j ↔ ∃ A ∈ t.guards j, (A : Set Var) ⊆ B := by
  induction t using induction_reset with
  | var i =>
    by_cases hi : j = i <;> simp [Selected, guards, hi]
  | step s t hs ht =>
    rw [selected_step, hs, ht, guards_step]
    constructor
    · rintro (⟨A, hA, hB⟩ | ⟨hr, A, hA, hB⟩)
      · exact ⟨A, Finset.mem_union_left _ hA, hB⟩
      · refine ⟨insert t.root A,
          Finset.mem_union_right _ (Finset.mem_image.mpr ⟨A, hA, rfl⟩), ?_⟩
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hr
        · exact hB hi
    · rintro ⟨A, hA, hB⟩
      rcases Finset.mem_union.mp hA with hA | hA
      · exact Or.inl ⟨A, hA, hB⟩
      · obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hA
        exact Or.inr ⟨hB (Finset.mem_insert_self _ _), C, hC,
          fun _ hi => hB (Finset.mem_insert_of_mem hi)⟩

@[simp] theorem mem_minimize (G : Finset (Finset Var)) (A : Finset Var) :
    A ∈ minimize G ↔ A ∈ G ∧ ∀ B ∈ G, B ⊆ A → A ⊆ B := by
  simp only [minimize, Finset.mem_filter]

/-- A finite family has a minimal prerequisite below each member. -/
theorem exists_mem_minimize_subset (G : Finset (Finset Var)) {A : Finset Var} (hA : A ∈ G) :
    ∃ B ∈ minimize G, B ⊆ A := by
  obtain ⟨B, hB, hmin⟩ := (G.filter (fun B => B ⊆ A)).exists_min_image Finset.card
    ⟨A, Finset.mem_filter.mpr ⟨hA, subset_rfl⟩⟩
  obtain ⟨hBG, hBA⟩ := Finset.mem_filter.mp hB
  refine ⟨B, (mem_minimize G B).mpr ⟨hBG, ?_⟩, hBA⟩
  intro C hC hCB
  have hcard := hmin C (Finset.mem_filter.mpr ⟨hC, hCB.trans hBA⟩)
  exact (Finset.eq_of_subset_of_card_le hCB hcard).symm.subset

/-- Antichain minimization does not alter the upward-closed predicate. -/
theorem exists_minimize_iff (G : Finset (Finset Var)) (B : Set Var) :
    (∃ A ∈ minimize G, (A : Set Var) ⊆ B) ↔ ∃ A ∈ G, (A : Set Var) ⊆ B := by
  constructor
  · rintro ⟨A, hA, hB⟩
    exact ⟨A, ((mem_minimize G A).mp hA).1, hB⟩
  · rintro ⟨A, hA, hB⟩
    obtain ⟨C, hC, hCA⟩ := exists_mem_minimize_subset G hA
    exact ⟨C, hC, fun _ hi => hB (hCA hi)⟩

/-- Minimal finite antichains are determined by their upward closures. -/
theorem minimize_eq_of_upward (G H : Finset (Finset Var))
    (h : ∀ B : Set Var,
      (∃ A ∈ G, (A : Set Var) ⊆ B) ↔ ∃ A ∈ H, (A : Set Var) ⊆ B) :
    minimize G = minimize H := by
  have transfer (G H : Finset (Finset Var))
      (h : ∀ B : Set Var,
        (∃ A ∈ G, (A : Set Var) ⊆ B) → ∃ A ∈ H, (A : Set Var) ⊆ B)
      (h' : ∀ B : Set Var,
        (∃ A ∈ H, (A : Set Var) ⊆ B) → ∃ A ∈ G, (A : Set Var) ⊆ B)
      (A : Finset Var) (hA : A ∈ minimize G) : A ∈ minimize H := by
    obtain ⟨hAG, hmin⟩ := (mem_minimize G A).mp hA
    obtain ⟨B, hB, hBA⟩ := h A ⟨A, hAG, subset_rfl⟩
    obtain ⟨C, hC, hCB⟩ := h' B ⟨B, hB, subset_rfl⟩
    have he : A = B := Finset.Subset.antisymm ((hmin C hC (hCB.trans hBA)).trans hCB) hBA
    subst B
    refine (mem_minimize H A).mpr ⟨hB, ?_⟩
    intro D hD hDA
    obtain ⟨C, hC, hCD⟩ := h' D ⟨D, hD, subset_rfl⟩
    exact (hmin C hC (hCD.trans hDA)).trans hCD
  ext A
  exact ⟨transfer G H (fun B => (h B).mp) (fun B => (h B).mpr) A,
    transfer H G (fun B => (h B).mpr) (fun B => (h B).mp) A⟩

/-- Exact table semantics, for arbitrary sets of ambiguous input positions. -/
theorem selected_iff_table (t : Term Var) (B : Set Var) (j : Var) :
    t.Selected B j ↔ ∃ A ∈ t.table j, (A : Set Var) ⊆ B :=
  (t.selected_iff_guard B j).trans (exists_minimize_iff (t.guards j) B).symm

/-- Membership in the table means precisely being an inclusion-minimal
finite set of ambiguity statuses enabling that output position. -/
theorem mem_table_iff (t : Term Var) (j : Var) (A : Finset Var) :
    A ∈ t.table j ↔ t.Selected (A : Set Var) j ∧
      ∀ B : Finset Var, B ⊆ A → t.Selected (B : Set Var) j → A ⊆ B := by
  constructor
  · intro hA
    obtain ⟨hAG, hmin⟩ := (mem_minimize _ _).mp hA
    refine ⟨(t.selected_iff_guard _ j).mpr ⟨A, hAG, subset_rfl⟩, ?_⟩
    intro B hBA hB
    obtain ⟨C, hC, hCB⟩ := (t.selected_iff_guard _ j).mp hB
    exact (hmin C hC (hCB.trans hBA)).trans hCB
  · rintro ⟨hA, hmin⟩
    obtain ⟨B, hB, hBA⟩ := (t.selected_iff_guard _ j).mp hA
    have he : A = B := Finset.Subset.antisymm (hmin B hBA
      ((t.selected_iff_guard _ j).mpr ⟨B, hB, subset_rfl⟩)) hBA
    subst B
    exact (mem_minimize _ _).mpr ⟨hB, fun C hC hCA => hmin C hCA
      ((t.selected_iff_guard _ j).mpr ⟨C, hC, subset_rfl⟩)⟩

/-- Tables are canonical, not just sufficient certificates for equality. -/
theorem table_eq_iff_selected (s t : Term Var) :
    s.table = t.table ↔ ∀ B j, s.Selected B j ↔ t.Selected B j := by
  constructor
  · intro he B j
    rw [selected_iff_table, selected_iff_table, he]
  · intro he
    funext j
    ext A
    simp only [mem_table_iff, he]

/-- Minimal prerequisites form an antichain for each output position. -/
theorem table_antichain (t : Term Var) (j : Var) {A B : Finset Var}
    (hA : A ∈ t.table j) (hB : B ∈ t.table j) (hAB : A ⊆ B) : A = B := by
  have ha := (t.mem_table_iff j A).mp hA
  have hb := (t.mem_table_iff j B).mp hB
  exact Finset.Subset.antisymm hAB (hb.2 A hAB ha.1)

/-- The unique position with an empty prerequisite is the actual root. -/
@[simp] theorem empty_mem_table (t : Term Var) (j : Var) :
    ∅ ∈ t.table j ↔ j = t.root := by
  rw [mem_table_iff]
  simp only [Finset.coe_empty, selected_empty, Finset.empty_subset, implies_true, and_true]

/-- A minimal prerequisite never contains its own selected position. -/
theorem not_mem_of_mem_table (t : Term Var) (j : Var) {A : Finset Var}
    (hA : A ∈ t.table j) : j ∉ A := by
  intro hj
  have h := (t.mem_table_iff j A).mp hA
  have hi : t.Selected (↑(A.erase j)) j :=
    (t.selected_self_independent (↑A) (↑(A.erase j)) j (by
      intro i hij
      simp [hij])).mp h.1
  have bad := h.2 _ (Finset.erase_subset _ _) hi hj
  simp at bad

end KFOL.Reset.Term
