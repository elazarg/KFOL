module

public import KFOL.Core.ChoiceUnion.Probe
public import KFOL.Equational.Completeness

/-! # The three-element table generates every model of the seven laws -/

@[expose] public section

namespace KFOL.Dissemilattice

universe u v

attribute [local instance] Three.structureOf

/-- Every equality of the actual three-element term functions holds in
arbitrary models of the seven laws. The probes force mutual support covers,
and the covers absorb every monomial on both sides. -/
theorem equality_of_three {M : Type u} [(Equational.language Symbol).Structure M]
    (hM : Laws (M := M) add mul) {Var : Type v} (s t : Term Var)
    (hThree : ∀ w : Var → Three, s.realize w = t.realize w) (v : Var → M) :
    s.realize v = t.realize v := by
  have hFG (w : Var → Three) :
      evalNormal three_laws (normalForm s) w = evalNormal three_laws (normalForm t) w := by
    calc
      evalNormal three_laws (normalForm s) w = s.realize w := normalForm_sound (M := Three) three_laws s w
      _ = t.realize w := hThree w
      _ = evalNormal three_laws (normalForm t) w := (normalForm_sound (M := Three) three_laws t w).symm
  have hst := absorb_normal_of_cover hM (normalForm s) (normalForm t)
    (fun A hA j hj => cover_of_three_equality _ _ hFG A hA j hj) v
  have hts := absorb_normal_of_cover hM (normalForm t) (normalForm s)
    (fun A hA j hj => cover_of_three_equality _ _ (fun w => (hFG w).symm) A hA j hj) v
  calc
    s.realize v = evalNormal hM (normalForm s) v := (normalForm_sound hM s v).symm
    _ = add (evalNormal hM (normalForm t) v) (evalNormal hM (normalForm s) v) := hts.symm
    _ = add (evalNormal hM (normalForm s) v) (evalNormal hM (normalForm t) v) := hM.add_comm _ _
    _ = evalNormal hM (normalForm t) v := hst
    _ = t.realize v := normalForm_sound hM t v

/-- Semantic generation of the full variety, with arbitrary carrier universe. -/
theorem inVariety_three_of_laws {M : Type u} [(Equational.language Symbol).Structure M] [Nonempty M]
    (hM : Laws (M := M) add mul) : Equational.InVariety Symbol Three M := by
  refine ⟨inferInstance,?_⟩
  intro e he v
  exact equality_of_three hM e.lhs e.rhs he v

/-- Genuine equational completeness of the literal seven equations for 3_m. -/
theorem basis_three : Equational.IsBasis Three theory := by
  apply (Equational.isBasis_iff_models theory).mpr
  refine ⟨laws_iff_models.mp three_laws,?_⟩
  intro M _ _ hM
  exact inVariety_three_of_laws (laws_iff_models.mpr hM)

end KFOL.Dissemilattice
