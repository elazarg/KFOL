module

public import KFOL.Core.AtomicBasis.Lattice
public import KFOL.Core.AtomicBasis.Separation
public import KFOL.Core.AtomicBasis.Presentation
public import Mathlib.Data.Set.Finite.Lattice

/-! # Completeness of the explicit atomic presentation over arbitrary algebras -/

@[expose] public section

namespace KFOL.Core.AtomicBasis

universe u v

open FirstOrder

variable {Role : Type u} [DecidableEq Role]

namespace LiftingLaws

variable {M : Type v} [(Equational.language (Equational.CoreSymbol Role)).Structure M]
    {three : Fin 3 ↪ Role} (h : AtomicBasis.LiftingLaws (join (M := M) three) (operation (Role := Role) (M := M)))
    [Nontrivial Role]

/-- Principal ideals are closed under every basic operation by pair coverage. -/
def ideal (u : M) : (Equational.language (Equational.CoreSymbol Role)).Substructure M := by
  letI := h.semilattice
  exact {
    carrier := {x | x ≤ u}
    fun_mem := by
      intro n f args hargs
      cases f with
      | choice r =>
        rw [funMap_choice]
        exact h.op_bound_upper r (hargs 0) (hargs 1) }

noncomputable def closureHom (i : Role) (u : M) :
    letI := h.pointDistribLattice i u
    letI := latticeStructure i (h.Point i u)
    h.ideal u →[Equational.language (Equational.CoreSymbol Role)] h.Point i u := by
  letI := h.semilattice
  letI := h.pointDistribLattice i u
  letI := latticeStructure i (h.Point i u)
  refine {
    toFun := fun a => ⟨operation i a.val u,
      h.op_bound_upper i a.property le_rfl, h.closure_idem i a.val u⟩
    map_fun' := ?_ }
  intro n f args
  cases f with
  | choice r =>
    rw [funMap_choice, funMap_choice]
    rw [lattice_operation]
    by_cases hri : r = i
    · subst r
      simp only [ite_true]
      apply Subtype.val_injective
      change operation i ((h.ideal u).subtype.toHom (operation i (args 0) (args 1))) u = _
      rw [hom_operation]
      exact h.closure_own i _ _ _
    · rw [ite_eq_right hri]
      apply Subtype.val_injective
      change operation i ((h.ideal u).subtype.toHom (operation r (args 0) (args 1))) u = _
      rw [hom_operation]
      exact h.closure_other i r (Ne.symm hri) (args 0).property (args 1).property

/-- The closure maps jointly reflect atomic identities on each principal ideal. -/
theorem ideal_holds (rs : List Role) (hn : rs.Nodup)
    (hreset : ∀ x y : M, reset three rs x y = y) (u : M)
    (e : Equational.Identity (Equational.CoreSymbol Role))
    (he : letI := structureOf Role; e.Holds (Carrier Role)) :
    e.Holds (h.ideal u) := by
  let _ := h.semilattice
  intro v
  apply Subtype.val_injective
  apply h.closures_separate rs hn hreset
    (show (e.lhs.realize v).val ≤ u from (e.lhs.realize v).property)
    (show (e.rhs.realize v).val ≤ u from (e.rhs.realize v).property)
  intro i
  let _ := structureOf Role
  let _ := booleanStructure i
  have hb := e.holds_of_surjective (indicatorHom i) (indicator_surjective i) he
  let _ := h.pointDistribLattice i u
  let _ := latticeStructure i (h.Point i u)
  have hl := lattice_holds_of_boolean (M := h.Point i u) i e hb
  have hh := hl (fun j => h.closureHom i u (v j))
  have hh' : h.closureHom i u (e.lhs.realize v) = h.closureHom i u (e.rhs.realize v) := by
    rw [← Language.HomClass.realize_term (h.closureHom i u),
      ← Language.HomClass.realize_term (h.closureHom i u)]
    exact hh
  exact congrArg Subtype.val hh'

end LiftingLaws

/-- Arbitrary nonempty models of the displayed basis satisfy every atomic identity. -/
theorem inVariety_of_models {M : Type v} [Nonempty M]
    [(Equational.language (Equational.CoreSymbol Role)).Structure M]
    (three : Fin 3 ↪ Role) (rs : List Role) (hn : rs.Nodup)
    (hm : Equational.Models (theory three rs) M) :
    letI := structureOf Role
    Equational.InVariety (Equational.CoreSymbol Role) (Carrier Role) M := by
  let _ := structureOf Role
  obtain ⟨h, hr⟩ := (models_iff three rs).mp hm
  let _ := h.semilattice
  let _ : Nontrivial Role := ⟨⟨three 0, three 1, three.injective.ne (by decide)⟩⟩
  refine ⟨inferInstance, ?_⟩
  intro e he v
  obtain ⟨u, hu⟩ := (Set.finite_range v).bddAbove
  let w : Fin e.arity → h.ideal u := fun i => ⟨v i, hu (Set.mem_range_self i)⟩
  have hi := h.ideal_holds rs hn hr u e he w
  have hh := congrArg (fun x : h.ideal u => x.val) hi
  have hmap := Language.HomClass.realize_term (h.ideal u).subtype.toHom
    (t := e.lhs) (v := w)
  have hmap' := Language.HomClass.realize_term (h.ideal u).subtype.toHom
    (t := e.rhs) (v := w)
  exact hmap.trans (hh.trans hmap'.symm)

end KFOL.Core.AtomicBasis
