module

public import KFOL.Reset.Realizability.GreedyOrder
public import KFOL.Reset.Realizability.Recognition

/-! # Executable compact synthesis, exact tables and primitive-tree size -/

@[expose] public section

namespace KFOL.Reset.GuardTable

universe v

section Tables

variable {Var : Type v} [DecidableEq Var]

/-- Antichain minimization fixes an already minimal candidate table. -/
theorem minimize_eq {G : GuardTable Var} (h : G.IsAntichain) (j : Var) :
    Term.minimize (G.guards j) = G.guards j := by
  ext A
  rw [Term.mem_minimize]
  constructor
  · exact And.left
  · intro hA
    refine ⟨hA, ?_⟩
    intro B hB hBA
    rw [h j B hB A hA hBA]

/-- Equal enabling predicates identify canonical tables with minimal candidates. -/
theorem table_eq_of_selected (G : GuardTable Var) (h : G.IsAntichain) (t : Term Var)
    (he : ∀ B j, t.Selected B j ↔ G.Enabled B j) : t.table = G.guards := by
  funext j
  rw [← minimize_eq h j]
  apply Term.minimize_eq_of_upward
  intro B
  exact (t.selected_iff_guard B j).symm.trans (he B j)

end Tables

section Ordered

variable {Var : Type v} [LinearOrder Var] (G : GuardTable Var)

@[simp] theorem mem_guardList (j : Var) (A : Finset Var) :
    A ∈ G.guardList j ↔ A ∈ G.guards j := by
  simp [guardList]

@[simp] theorem length_guardList (j : Var) :
    (G.guardList j).length = (G.guards j).card := by
  simp only [guardList, List.length_map, Finset.length_sort, Finset.card_map]

variable [Fintype Var]

theorem mem_synthesisPaths (t : Term Var) : t ∈ G.synthesisPaths ↔
    ∃ j, ∃ A ∈ G.guards j, G.greedyPath (insert j A) = t := by
  simp [synthesisPaths]

theorem length_synthesisPaths : G.synthesisPaths.length = G.entryCount := by
  simp only [synthesisPaths, List.length_flatMap, List.length_map,
    length_guardList]
  have he := List.sum_toFinset (fun j => (G.guards j).card)
    (Finset.sort_nodup (Finset.univ : Finset Var) (· ≤ ·))
  simpa only [Finset.sort_toFinset, entryCount] using he.symm

/-- Every listed prerequisite produces a path with exactly its support and
only permitted selectors. Repeated input occurrences are counted independently. -/
theorem synthesisPath_spec (h : G.WellFormed) (j : Var) {A : Finset Var}
    (hA : A ∈ G.guards j) :
    (G.greedyPath (insert j A)).root = G.root ∧
      (G.greedyPath (insert j A)).varFinset = insert j A ∧
      (∀ B k, (G.greedyPath (insert j A)).Selected B k → G.Enabled B k) ∧
      (G.greedyPath (insert j A)).size + 1 ≤ 2 * Fintype.card Var := by
  have hb : G.Constructible (insert j A) :=
    .insert j (h.2.2.2.2 _ _ hA) (h.2.2.2.1 _ _ hA) ⟨A, hA, subset_rfl⟩
  have hr := hb.root_mem h.2.2.1 (Finset.insert_nonempty _ _)
  obtain ⟨hr, hs, he, hc⟩ := G.greedyPath_spec h hr hb
  refine ⟨hr, hs, he, ?_⟩
  have hn : (insert j A).card ≤ Fintype.card Var := Finset.card_le_univ _
  omega

/-- The actual term returned by the algorithm realizes all and only the
candidate guards, with the compact bound on the expanded primitive tree. -/
theorem join_synthesisPaths_spec (h : G.WellFormed) :
    let t := Term.joinPaths G.root G.synthesisPaths
    t.root = G.root ∧ t.table = G.guards ∧
      t.size ≤ 1 + 2 * Fintype.card Var * G.entryCount := by
  have hroots : ∀ t ∈ G.synthesisPaths, t.root = G.root := by
    intro t ht
    obtain ⟨j, A, hA, rfl⟩ := (G.mem_synthesisPaths t).mp ht
    exact (G.synthesisPath_spec h j hA).1
  have hsel : ∀ B j, Term.Selected (Term.joinPaths G.root G.synthesisPaths) B j ↔
      G.Enabled B j := by
    intro B j
    rw [Term.selected_joinPaths _ _ _ _ hroots]
    constructor
    · rintro (he | ⟨s, hs, hj⟩)
      · subst j
        exact ⟨∅, by rw [h.2.1]; simp, by simp⟩
      · obtain ⟨k, A, hA, rfl⟩ := (G.mem_synthesisPaths s).mp hs
        exact (G.synthesisPath_spec h k hA).2.2.1 B j hj
    · rintro ⟨A, hA, hAB⟩
      let s := G.greedyPath (insert j A)
      have hs := (G.synthesisPath_spec h j hA).2.1
      refine Or.inr ⟨s, (G.mem_synthesisPaths s).mpr ⟨j, A, hA, rfl⟩, ?_⟩
      apply s.selected_of_support_insert B j
      · rw [hs]
        exact Finset.mem_insert_self _ _
      · rw [hs]
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact Or.inl rfl
        · exact Or.inr (hAB hk)
  refine ⟨Term.root_joinPaths _ _, G.table_eq_of_selected h.1 _ hsel, ?_⟩
  have hp : ∀ s ∈ G.synthesisPaths, s.size + 1 ≤ 2 * Fintype.card Var := by
    intro s hs
    obtain ⟨j, A, hA, rfl⟩ := (G.mem_synthesisPaths s).mp hs
    exact (G.synthesisPath_spec h j hA).2.2.2
  have hh := Term.size_joinPaths_le G.root G.synthesisPaths (2 * Fintype.card Var) hp
  rw [G.length_synthesisPaths] at hh
  simpa only [Nat.mul_comm G.entryCount (2 * Fintype.card Var)] using hh

/-- Executable synthesis succeeds exactly on the independently specified
realizability conditions. -/
theorem synthesize_isSome_iff : G.synthesize.isSome = true ↔ G.WellFormed := by
  simp only [synthesize]
  split
  next h => simpa using G.check_eq_true.mp h
  next h =>
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    exact fun hw => h (G.check_eq_true.mpr hw)

/-- Soundness of every successful output, including its primitive-tree size. -/
theorem synthesize_spec {t : Term Var} (ht : G.synthesize = some t) :
    t.root = G.root ∧ t.table = G.guards ∧
      t.size ≤ 1 + 2 * Fintype.card Var * G.entryCount := by
  simp only [synthesize] at ht
  split at ht
  next hc =>
    have he := Option.some.inj ht
    rw [← he]
    exact G.join_synthesisPaths_spec (G.check_eq_true.mp hc)
  next => cases ht

end Ordered

/-- The order-free mathematical existence theorem follows from executable
synthesis. A finite enumeration supplies an order only inside this proof. -/
theorem exists_term_bounded {Var : Type v} [deq : DecidableEq Var] [Fintype Var]
    (G : GuardTable Var) (h : G.WellFormed) :
    ∃ t : Term Var, t.root = G.root ∧ t.table = G.guards ∧
      t.size ≤ 1 + 2 * Fintype.card Var * G.entryCount := by
  classical
  let _ : LinearOrder Var := LinearOrder.lift' (Fintype.equivFin Var)
    (Fintype.equivFin Var).injective
  have hd : deq = (fun a b : Var => LinearOrder.toDecidableEq a b) := Subsingleton.elim _ _
  rw [hd] at h ⊢
  exact ⟨Term.joinPaths G.root G.synthesisPaths, G.join_synthesisPaths_spec h⟩

end KFOL.Reset.GuardTable
