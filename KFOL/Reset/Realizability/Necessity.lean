module

public import KFOL.Reset.Realizability.Constructible
public import KFOL.Reset.Antimatroid.Paths

/-! # Canonical prerequisites are constructible -/

@[expose] public section

namespace KFOL.Reset.Term

universe v

variable {Var : Type v} [DecidableEq Var]

@[simp] theorem enabled_guardTable (t : Term Var) (B : Set Var) (j : Var) :
    t.guardTable.Enabled B j ↔ t.Selected B j := (t.selected_iff_table B j).symm

/-- Every feasible set has a construction using the canonical prerequisites. -/
theorem constructible_of_feasible (t : Term Var) {A : Finset Var}
    (hA : A ∈ t.antimatroid.feasible) : t.guardTable.Constructible A := by
  induction hn : A.card using Nat.strong_induction_on generalizing A with
  | h n ih =>
    by_cases he : A = ∅
    · subst A
      exact .empty
    · obtain ⟨j, hj, hAe⟩ := t.antimatroid.accessible A hA
        (Finset.nonempty_iff_ne_empty.mpr he)
      have hc : (A.erase j).card < n := by
        rw [← hn]
        exact Finset.card_lt_card (Finset.erase_ssubset hj)
      have hbuild := ih _ hc hAe rfl
      have hready : t.antimatroid.Ready (A.erase j : Set Var) j := by
        refine ⟨A, hA, hj, ?_⟩
        intro k hk
        by_cases hkj : k = j
        · exact Or.inl hkj
        · exact Or.inr (Finset.mem_erase.mpr ⟨hkj, hk⟩)
      have hen := (t.enabled_guardTable _ j).mpr ((t.ready_antimatroid _ j).mp hready)
      have hb := GuardTable.Constructible.insert j hbuild (by simp) hen
      rwa [Finset.insert_erase hj] at hb

/-- A minimal prerequisite is itself feasible; arbitrary enabling supersets
need not be, which is why minimality is used explicitly here. -/
theorem feasible_of_mem_table (t : Term Var) (j : Var) {A : Finset Var}
    (hA : A ∈ t.table j) : A ∈ t.antimatroid.feasible := by
  have hm := (t.mem_table_iff j A).mp hA
  by_cases hj : j = t.root
  · have hsub := hm.2 ∅ (Finset.empty_subset _) (by
      subst j
      simpa only [Finset.coe_empty] using t.selected_root ∅)
    have he : A = ∅ := Finset.Subset.antisymm hsub (Finset.empty_subset _)
    rw [he]
    exact t.antimatroid.empty_mem
  · obtain ⟨C, hC, hjC, hCA⟩ := (t.ready_antimatroid (A : Set Var) j).mpr hm.1
    obtain ⟨xs, hxs, hs⟩ := t.antimatroid.exists_order hC ⟨j, hjC⟩
    have hjxs : j ∈ xs := by
      rw [← hs] at hjC
      exact List.mem_toFinset.mp ((Finset.mem_insert.mp hjC).resolve_left
        (by simpa only [antimatroid_root] using hj))
    obtain ⟨before, after, hx⟩ := List.mem_iff_append.mp hjxs
    let U := insert t.antimatroid.root before.toFinset
    have hU : U ∈ t.antimatroid.feasible := by
      have hp := hxs.prefix_mem before.length
      rw [hx, List.take_append_of_le_length le_rfl, List.take_length] at hp
      exact hp
    have hjU : j ∉ U := by
      intro hmem
      rcases Finset.mem_insert.mp hmem with hr | hmem
      · exact hj ((antimatroid_root t) ▸ hr)
      · have hnd := hxs.nodup
        rw [hx, List.nodup_append] at hnd
        exact hnd.2.2 j (List.mem_toFinset.mp hmem) j List.mem_cons_self rfl
    have hUC : U ⊆ C := by
      rw [← hs]
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr
          (by rw [hx]; exact List.mem_append_left _ (List.mem_toFinset.mp hk)))
    have hUA : U ⊆ A := by
      intro k hk
      rcases Set.mem_insert_iff.mp (hCA (hUC hk)) with rfl | hkA
      · exact False.elim (hjU hk)
      · exact hkA
    have hready : t.antimatroid.Ready (U : Set Var) j := by
      refine ⟨insert j U, hxs.prefix_insert hx, Finset.mem_insert_self _ _, ?_⟩
      intro k hk
      exact Finset.mem_insert.mp hk
    have hsel := (t.ready_antimatroid U j).mp hready
    have he : A = U := Finset.Subset.antisymm (hm.2 U hUA hsel) hUA
    rwa [he]

/-- Necessity of the paper's constructibility condition. -/
theorem constructible_of_mem_table (t : Term Var) (j : Var) {A : Finset Var}
    (hA : A ∈ t.table j) : t.guardTable.Constructible A :=
  t.constructible_of_feasible (t.feasible_of_mem_table j hA)

@[simp] theorem table_root (t : Term Var) : t.table t.root = {∅} := by
  ext A
  constructor
  · intro hA
    have he := t.table_antichain t.root ((t.empty_mem_table t.root).mpr rfl) hA
      (Finset.empty_subset _)
    exact Finset.mem_singleton.mpr he.symm
  · intro hA
    have he := Finset.mem_singleton.mp hA
    rw [he]
    exact (t.empty_mem_table t.root).mpr rfl

/-- The canonical data satisfy every independent candidate condition. -/
theorem guardTable_wellFormed (t : Term Var) : t.guardTable.WellFormed :=
  ⟨fun j _ hA _ hB hAB => t.table_antichain j hA hB hAB, t.table_root,
    fun j hj => (t.empty_mem_table j).mp hj,
    fun j _ hA => t.not_mem_of_mem_table j hA,
    fun j _ hA => t.constructible_of_mem_table j hA⟩

end KFOL.Reset.Term
