module

public import KFOL.Reset.Realizability.Constructible

/-! # The accessible family determined by a well-formed candidate table -/

@[expose] public section

namespace KFOL.Reset.GuardTable

universe v

variable {Var : Type v} [DecidableEq Var] [Fintype Var]

/-- The model construction is mathematical; candidate recognition does not
need to enumerate its feasible sets. -/
noncomputable def antimatroid (G : GuardTable Var) (h : G.WellFormed) :
    RootedAntimatroid Var := by
  classical
  obtain ⟨_, hr, hu, hs, hc⟩ := h
  let S := Finset.univ.filter (fun j => (G.guards j).Nonempty)
  have hsub : ∀ A, G.Constructible A → A ⊆ S := by
    intro A hA j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA.active hj⟩
  have hfull : G.Constructible S := by
    have per : ∀ j : S, ∃ A, G.Constructible A ∧ j.val ∈ A ∧ A ⊆ S := by
      intro j
      obtain ⟨A, hA⟩ := (Finset.mem_filter.mp j.property).2
      have hb : G.Constructible (insert j.val A) :=
        .insert j.val (hc _ _ hA) (hs _ _ hA) ⟨A, hA, subset_rfl⟩
      exact ⟨insert j.val A, hb, Finset.mem_insert_self _ _, hsub _ hb⟩
    choose pieces hp hj hps using per
    let T := Finset.univ.image pieces
    have ht : G.Constructible (T.biUnion id) := constructible_biUnion T (by
      rintro A hA
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hA
      exact hp j)
    have he : T.biUnion id = S := by
      ext j
      constructor
      · intro hm
        obtain ⟨A, hA, hjA⟩ := Finset.mem_biUnion.mp hm
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hA
        exact hps i hjA
      · intro hm
        exact Finset.mem_biUnion.mpr ⟨pieces ⟨j, hm⟩,
          Finset.mem_image.mpr ⟨⟨j, hm⟩, Finset.mem_univ _, rfl⟩, hj ⟨j, hm⟩⟩
    rwa [he] at ht
  refine { ground := S
           feasible := {A | G.Constructible A}
           root := G.root
           empty_mem := .empty
           ground_mem := hfull
           subset_ground := hsub
           union_mem := fun _ hA _ hB => hA.union hB
           accessible := fun _ hA hne => hA.accessible hne
           root_mem := ?_
           singleton_unique := ?_ }
  · exact .insert G.root .empty (by simp) ⟨∅, by rw [hr]; simp, by simp⟩
  · intro j hj
    exact (Finset.mem_singleton.mp (hj.root_mem hu (Finset.singleton_nonempty _))).symm

/-- Feasibility is exactly the independent constructibility predicate. -/
@[simp] theorem feasible_antimatroid (G : GuardTable Var) (h : G.WellFormed) (A : Finset Var) :
    A ∈ (G.antimatroid h).feasible ↔ G.Constructible A := Iff.rfl

@[simp] theorem root_antimatroid (G : GuardTable Var) (h : G.WellFormed) :
    (G.antimatroid h).root = G.root := rfl

/-- Candidate enabling is precisely readiness in the constructed family. -/
theorem ready_antimatroid (G : GuardTable Var) (h : G.WellFormed) (B : Set Var) (j : Var) :
    (G.antimatroid h).Ready B j ↔ G.Enabled B j := by
  obtain ⟨_, _, _, hs, hc⟩ := h
  constructor
  · rintro ⟨C, hC, hj, hCB⟩
    change G.Constructible C at hC
    apply enabled_mono (G := G) (B := (C.erase j : Set Var)) _ (hC.enabled_of_mem hj)
    intro k hk
    obtain ⟨hkj, hk⟩ := Finset.mem_erase.mp hk
    exact (Set.mem_insert_iff.mp (hCB hk)).resolve_left hkj
  · rintro ⟨A, hA, hAB⟩
    refine ⟨insert j A, .insert j (hc _ _ hA) (hs _ _ hA) ⟨A, hA, subset_rfl⟩,
      Finset.mem_insert_self _ _, ?_⟩
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact Or.inl rfl
    · exact Or.inr (hAB hk)

end KFOL.Reset.GuardTable
