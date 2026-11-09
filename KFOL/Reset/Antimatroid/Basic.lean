module

public import KFOL.Definitions.Reset
public import KFOL.Reset.Substitution

/-! # Finite accessible families, readiness and their actual support -/

@[expose] public section

namespace KFOL.Reset.RootedAntimatroid

universe v

variable {Var : Type v} [DecidableEq Var]

/-- Every nonempty feasible set contains the unique feasible singleton. -/
theorem root_mem_of_nonempty (F : RootedAntimatroid Var) {A : Finset Var}
    (hA : A ∈ F.feasible) (hne : A.Nonempty) : F.root ∈ A := by
  induction hn : A.card using Nat.strong_induction_on generalizing A with
  | h n ih =>
    obtain ⟨a, ha, herase⟩ := F.accessible A hA hne
    by_cases he : A.erase a = ∅
    · have hsingle : A = {a} := by
        apply Finset.Subset.antisymm
        · intro x hx
          by_cases hxa : x = a
          · exact Finset.mem_singleton.mpr hxa
          · have bad := Finset.mem_erase.mpr ⟨hxa, hx⟩
            rw [he] at bad
            simp at bad
        · exact Finset.singleton_subset_iff.mpr ha
      have har := F.singleton_unique a (hsingle ▸ hA)
      simp only [hsingle, har, Finset.mem_singleton]
    · have hc : (A.erase a).card < n := by
        rw [← hn]
        exact Finset.card_lt_card (Finset.erase_ssubset ha)
      exact Finset.mem_of_mem_erase (ih _ hc herase (Finset.nonempty_iff_ne_empty.mpr he) rfl)

theorem root_mem_ground (F : RootedAntimatroid Var) : F.root ∈ F.ground :=
  F.subset_ground _ F.root_mem (Finset.mem_singleton_self _)

theorem ground_nonempty (F : RootedAntimatroid Var) : F.ground.Nonempty :=
  ⟨F.root, F.root_mem_ground⟩

theorem ready_root (F : RootedAntimatroid Var) (B : Set Var) : F.Ready B F.root :=
  ⟨{F.root}, F.root_mem, Finset.mem_singleton_self _, by simp⟩

theorem ready_mono (F : RootedAntimatroid Var) {B C : Set Var} (hBC : B ⊆ C) {j : Var}
    (hj : F.Ready B j) : F.Ready C j := by
  obtain ⟨A, hA, hj, hAB⟩ := hj
  exact ⟨A, hA, hj, hAB.trans (Set.insert_subset_insert hBC)⟩

theorem mem_ground_of_ready (F : RootedAntimatroid Var) {B : Set Var} {j : Var}
    (hj : F.Ready B j) : j ∈ F.ground := by
  obtain ⟨A, hA, hj, _⟩ := hj
  exact F.subset_ground A hA hj

/-- Union closure extends to any finite collection of feasible sets. -/
theorem biUnion_mem (F : RootedAntimatroid Var) (S : Finset (Finset Var))
    (hS : ∀ A ∈ S, A ∈ F.feasible) : S.biUnion id ∈ F.feasible := by
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.biUnion_empty] using F.empty_mem
  | @insert A S ha ih =>
    rw [Finset.biUnion_insert]
    exact F.union_mem A (hS A (Finset.mem_insert_self _ _)) _
      (ih (fun B hB => hS B (Finset.mem_insert_of_mem hB)))

/-- A family is recovered exactly by requiring every member to be ready. -/
theorem feasible_iff_ready (F : RootedAntimatroid Var) (A : Finset Var) :
    A ∈ F.feasible ↔ ∀ j ∈ A, F.Ready (A : Set Var) j := by
  classical
  constructor
  · intro hA j hj
    exact ⟨A, hA, hj, Set.subset_insert _ _⟩
  · intro h
    have choices : ∀ j : A, ∃ B ∈ F.feasible, j.val ∈ B ∧ B ⊆ A := by
      intro j
      obtain ⟨B, hB, hj, hBA⟩ := h j.val j.property
      exact ⟨B, hB, hj, fun k hk => by
        rcases Set.mem_insert_iff.mp (hBA hk) with rfl | hk
        · exact j.property
        · exact hk⟩
    choose pieces hpieces hj hsub using choices
    let S : Finset (Finset Var) := Finset.univ.image pieces
    have hS : ∀ B ∈ S, B ∈ F.feasible := by
      rintro B hB
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hB
      exact hpieces j
    have he : S.biUnion id = A := by
      ext j
      constructor
      · intro hm
        obtain ⟨B, hB, hjB⟩ := Finset.mem_biUnion.mp hm
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hB
        exact hsub i hjB
      · intro hm
        exact Finset.mem_biUnion.mpr ⟨pieces ⟨j, hm⟩,
          Finset.mem_image.mpr ⟨⟨j, hm⟩, Finset.mem_univ _, rfl⟩, hj ⟨j, hm⟩⟩
    rw [← he]
    exact F.biUnion_mem S hS

/-- The family itself determines the finite ground and the unique root. -/
@[ext] theorem ext {F G : RootedAntimatroid Var} (h : F.feasible = G.feasible) : F = G := by
  have hg : F.ground = G.ground := Finset.Subset.antisymm
    (G.subset_ground _ (h ▸ F.ground_mem)) (F.subset_ground _ (h.symm ▸ G.ground_mem))
  have hr : F.root = G.root := G.singleton_unique F.root (h ▸ F.root_mem)
  cases F
  cases G
  cases hg
  cases hr
  cases h
  rfl

/-- Accessibility can remove a position outside an arbitrary comparison set,
skipping intermediate removals already covered by that set. -/
theorem remove_from_union (F : RootedAntimatroid Var) {A C : Finset Var}
    (hA : A ∈ F.feasible) (hne : ¬A ⊆ C) :
    ∃ a ∈ A, a ∉ C ∧ ∃ A' ∈ F.feasible, A' ∪ C = (A ∪ C).erase a := by
  induction hn : A.card using Nat.strong_induction_on generalizing A with
  | h n ih =>
    have han : A.Nonempty := by
      by_contra hempty
      exact hne (by simpa only [Finset.not_nonempty_iff_eq_empty.mp hempty] using
        (Finset.empty_subset C))
    obtain ⟨a, ha, he⟩ := F.accessible A hA han
    by_cases hac : a ∈ C
    · have hsub : ¬A.erase a ⊆ C := by
        intro hs
        apply hne
        intro x hx
        by_cases hxa : x = a
        · exact hxa ▸ hac
        · exact hs (Finset.mem_erase.mpr ⟨hxa, hx⟩)
      have hc : (A.erase a).card < n := by
        rw [← hn]
        exact Finset.card_lt_card (Finset.erase_ssubset ha)
      obtain ⟨b, hb, hbc, A', hA', hu⟩ := ih _ hc he hsub rfl
      refine ⟨b, Finset.mem_of_mem_erase hb, hbc, A', hA', ?_⟩
      have hunion : A.erase a ∪ C = A ∪ C := by
        ext x
        by_cases hxa : x = a <;> simp_all
      rwa [hunion] at hu
    · refine ⟨a, ha, hac, A.erase a, he, ?_⟩
      ext x
      by_cases hxa : x = a <;> simp_all

end KFOL.Reset.RootedAntimatroid
