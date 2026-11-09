module

public import KFOL.Reset.Realizability.Model
public import KFOL.Reset.Realizability.Size

/-! # Compact path synthesis from independent candidate tables -/

@[expose] public section

namespace KFOL.Reset.GuardTable

universe v

variable {Var : Type v} [DecidableEq Var] [Fintype Var]

omit [Fintype Var] in
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

omit [Fintype Var] in
/-- Equal enabling predicates identify canonical tables with minimal candidates. -/
theorem table_eq_of_selected (G : GuardTable Var) (h : G.IsAntichain) (t : Term Var)
    (he : ∀ B j, t.Selected B j ↔ G.Enabled B j) : t.table = G.guards := by
  funext j
  rw [← minimize_eq h j]
  apply Term.minimize_eq_of_upward
  intro B
  exact (t.selected_iff_guard B j).symm.trans (he B j)

/-- One path per prerequisite suffices, with a bound on the actual expanded
primitive syntax tree. No enumeration of all feasible sets is used. -/
theorem exists_term_bounded (G : GuardTable Var) (h : G.WellFormed) :
    ∃ t : Term Var, t.root = G.root ∧ t.table = G.guards ∧
      t.size ≤ 1 + 2 * Fintype.card Var * G.entryCount := by
  classical
  let F := G.antimatroid h
  let I : Finset (Σ _ : Var, Finset Var) := Finset.univ.sigma G.guards
  have hp : ∀ p : I, ∃ t : Term Var, t.root = G.root ∧
      t.varFinset = insert p.val.1 p.val.2 ∧
      (∀ B j, t.Selected B j → G.Enabled B j) ∧ t.size + 1 ≤ 2 * Fintype.card Var := by
    intro p
    have hA := (Finset.mem_sigma.mp p.property).2
    have hb : G.Constructible (insert p.val.1 p.val.2) :=
      .insert _ (h.2.2.2.2 _ _ hA) (h.2.2.2.1 _ _ hA) ⟨p.val.2, hA, subset_rfl⟩
    obtain ⟨t, hr, ht, he, hsize⟩ := F.exists_path_sized hb (Finset.insert_nonempty _ _)
    refine ⟨t, hr, ht, ?_, ?_⟩
    · intro B j hj
      exact (G.ready_antimatroid h B j).mp (he B j hj)
    · have hc : (insert p.val.1 p.val.2).card ≤ Fintype.card Var := by
        simpa only [Finset.card_univ] using
          Finset.card_le_card (Finset.subset_univ (insert p.val.1 p.val.2))
      omega
  choose pieces hroot hvars hen hsize using hp
  let ts := I.attach.toList.map pieces
  have hroots : ∀ t ∈ ts, t.root = G.root := by
    rintro t ht
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp ht
    exact hroot p
  let t := Term.joinPaths G.root ts
  have hsel : ∀ B j, t.Selected B j ↔ G.Enabled B j := by
    intro B j
    rw [Term.selected_joinPaths G.root ts B j hroots]
    constructor
    · rintro (he | ⟨s, hs, hj⟩)
      · subst j
        exact ⟨∅, by rw [h.2.1]; simp, by simp⟩
      · obtain ⟨p, _, rfl⟩ := List.mem_map.mp hs
        exact hen p B j hj
    · rintro ⟨A, hA, hAB⟩
      let p : I := ⟨⟨j, A⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hA⟩⟩
      refine Or.inr ⟨pieces p, List.mem_map.mpr ⟨p, by simp, rfl⟩, ?_⟩
      apply (pieces p).selected_of_support_insert B j
      · rw [hvars]
        exact Finset.mem_insert_self _ _
      · rw [hvars]
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact Or.inl rfl
        · exact Or.inr (hAB hk)
  refine ⟨t, Term.root_joinPaths _ _, G.table_eq_of_selected h.1 t hsel, ?_⟩
  have hs : ∀ s ∈ ts, s.size + 1 ≤ 2 * Fintype.card Var := by
    rintro s hs
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hs
    exact hsize p
  have hc : ts.length = G.entryCount := by
    simp only [ts, List.length_map, Finset.length_toList, Finset.card_attach,
      I, Finset.card_sigma, entryCount]
  have hh := Term.size_joinPaths_le G.root ts (2 * Fintype.card Var) hs
  rw [hc] at hh
  simpa only [Nat.mul_comm G.entryCount (2 * Fintype.card Var)] using hh

end KFOL.Reset.GuardTable
