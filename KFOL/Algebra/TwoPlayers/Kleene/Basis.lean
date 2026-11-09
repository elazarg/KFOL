module

public import KFOL.Algebra.TwoPlayers.Kleene.Completeness
public import KFOL.Algebra.TwoPlayers.Kleene.Presentation
public import KFOL.Equational.Completeness
public import Mathlib.Data.Set.Finite.Range

/-! # A genuine finite equational basis of bounded Kleene algebras -/

@[expose] public section

namespace KFOL.TwoPlayers.Kleene

universe u

/-- Every model of the raw laws satisfies every identity of the actual
three-valued chain. The target structure and carrier universe are arbitrary. -/
theorem inVariety_three_of_laws {M : Type u} [inst : (Equational.language Symbol).Structure M]
    (h : Laws (operationZero M) (operationOne M) (operationJoin M) (operationMeet M) (operationNeg M)) :
    let _ := threeStructure
    Equational.InVariety Symbol (Fin 3) M := by
  let := threeStructure
  dsimp only
  refine ⟨⟨operationZero M⟩,?_⟩
  intro e he
  let := h.distribLattice
  let := h.boundedOrder
  have hn : ∀ x, operationNeg M (operationNeg M x) = x := h.neg_neg
  have hd : ∀ x y, operationNeg M (x ⊓ y) = operationNeg M x ⊔ operationNeg M y := h.neg_mul
  have h0 : operationNeg M ⊥ = ⊤ := h.neg_zero
  have hk : ∀ x y : M, x ⊓ operationNeg M x ≤ y ⊔ operationNeg M y := h.kleene
  let canon : (Equational.language Symbol).Structure M :=
    structureOf (⊥ : M) ⊤ (· ⊔ ·) (· ⊓ ·) (operationNeg M)
  have hs : inst = canon := structure_eq (inst := inst)
  have hprop : @Equational.Identity.Holds Symbol e M inst =
      @Equational.Identity.Holds Symbol e M canon := congrArg (fun s => @Equational.Identity.Holds Symbol e M s) hs
  apply Eq.mpr hprop
  exact equality_of_three (operationNeg M) hn hd h0 hk e.lhs e.rhs he

/-- Equational completeness, not merely semantic soundness, of the displayed
fifteen-equation bounded Kleene presentation for the strong three-valued chain. -/
theorem basis_three :
    let _ := threeStructure
    Equational.IsBasis (Fin 3) basis := by
  let := threeStructure
  apply (Equational.isBasis_iff_models basis).mpr
  refine ⟨laws_iff_models.mp ?_,?_⟩
  · exact three_laws
  · intro M _ _ hM
    exact inVariety_three_of_laws (laws_iff_models.mpr hM)

theorem basis_finite : basis.Finite := Set.finite_range basisAxiom

theorem hasFiniteBasis_three :
    let _ := threeStructure
    Equational.HasFiniteBasis Symbol (Fin 3) := by
  let := threeStructure
  exact ⟨basis,basis_finite,basis_three⟩

end KFOL.TwoPlayers.Kleene
