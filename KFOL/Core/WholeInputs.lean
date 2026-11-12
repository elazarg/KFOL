module

public import KFOL.Core.Profiles
public import KFOL.Equational.Native

/-! # Whole-input provenance of core outputs

Every output winner comes from an input menu wholly contained in the output.
Consequently the output is the union of all such input menus.
-/

@[expose] public section
namespace KFOL.Core
universe u v
variable {Role : Type u} {Var : Type v}
attribute [local instance] Equational.coreStructure

/-- Every output winner has a source input whose whole menu survives. -/
theorem whole_input_provenance
    (t : Equational.Term (Equational.CoreSymbol Role) Var)
    (values : Var → WinnerSet Role) (k : Role) (hk : k ∈ (t.realize values).val) :
    ∃ j, k ∈ (values j).val ∧ (values j).val ⊆ (t.realize values).val := by
  classical
  induction t using induction_choice with
  | var j => exact ⟨j, hk, Set.Subset.rfl⟩
  | choice r x y hx hy =>
    change k ∈ (WinnerSet.choice r (x.realize values) (y.realize values)).val at hk
    change ∃ j, k ∈ (values j).val ∧
      (values j).val ⊆ (WinnerSet.choice r (x.realize values) (y.realize values)).val
    by_cases hleft : x.realize values = WinnerSet.singleton r
    · have hparent : WinnerSet.choice r (x.realize values) (y.realize values) =
          x.realize values := by simp [WinnerSet.choice, hleft]
      rw [hparent] at hk ⊢
      exact hx hk
    · by_cases hright : y.realize values = WinnerSet.singleton r
      · have hparent : WinnerSet.choice r (x.realize values) (y.realize values) =
            y.realize values := by simp [WinnerSet.choice, hright]
        rw [hparent] at hk ⊢
        exact hy hk
      · have hparent : WinnerSet.choice r (x.realize values) (y.realize values) =
            (x.realize values).union (y.realize values) := by
          simp [WinnerSet.choice, hleft, hright]
        rw [hparent] at hk ⊢
        rcases hk with h | h
        · obtain ⟨j, hj, hsub⟩ := hx h
          exact ⟨j, hj, hsub.trans Set.subset_union_left⟩
        · obtain ⟨j, hj, hsub⟩ := hy h
          exact ⟨j, hj, hsub.trans Set.subset_union_right⟩

/-- The entire output is the union of all input menus contained in it. -/
theorem realize_eq_iUnion_whole_inputs
    (t : Equational.Term (Equational.CoreSymbol Role) Var)
    (values : Var → WinnerSet Role) :
    (t.realize values).val =
      ⋃ j, ⋃ (_ : (values j).val ⊆ (t.realize values).val), (values j).val := by
  ext k
  simp only [Set.mem_iUnion]
  constructor
  · intro hk
    obtain ⟨j, hj, hsub⟩ := whole_input_provenance t values k hk
    exact ⟨j, hsub, hj⟩
  · rintro ⟨j, hsub, hj⟩
    exact hsub hj

/-- Under an upper output bound, every requested winner has an eligible whole
input source already satisfying that bound. -/
theorem whole_input_provenance_bounded
    (t : Equational.Term (Equational.CoreSymbol Role) Var)
    (values : Var → WinnerSet Role) (U : Set Role)
    (hbound : (t.realize values).val ⊆ U) (k : Role)
    (hk : k ∈ (t.realize values).val) :
    ∃ j, k ∈ (values j).val ∧ (values j).val ⊆ U := by
  obtain ⟨j, hj, hsub⟩ := whole_input_provenance t values k hk
  exact ⟨j, hj, hsub.trans hbound⟩

/-- Whole-input provenance in the native core syntax. -/
theorem whole_input_provenance_of_isCore (t : Term Role Var) (ht : t.IsCore)
    (values : Var → WinnerSet Role) (k : Role) (hk : k ∈ (t.eval values).val) :
    ∃ j, k ∈ (values j).val ∧ (values j).val ⊆ (t.eval values).val := by
  have he : (Equational.Core.encode t ht).realize values = t.eval values := by
    rw [← Equational.Core.eval_decode, Equational.Core.decode_encode]
  have hk' : k ∈ ((Equational.Core.encode t ht).realize values).val := by
    simpa only [he] using hk
  simpa only [he] using whole_input_provenance (Equational.Core.encode t ht) values k hk'

/-- The whole-input union identity in the native core syntax. -/
theorem eval_eq_iUnion_whole_inputs (t : Term Role Var) (ht : t.IsCore)
    (values : Var → WinnerSet Role) :
    (t.eval values).val =
      ⋃ j, ⋃ (_ : (values j).val ⊆ (t.eval values).val), (values j).val := by
  ext k
  simp only [Set.mem_iUnion]
  constructor
  · intro hk
    obtain ⟨j, hj, hsub⟩ := whole_input_provenance_of_isCore t ht values k hk
    exact ⟨j, hsub, hj⟩
  · rintro ⟨j, hsub, hj⟩
    exact hsub hj

end KFOL.Core
