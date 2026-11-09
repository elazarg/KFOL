module

public import KFOL.Algebra.TwoPlayers.Kleene.Basis
public import KFOL.Algebra.TwoPlayers.CoreFailure

/-! # The finite Kleene basis applies to the actual two-player winner algebra -/

@[expose] public section

namespace KFOL.TwoPlayers.Kleene

universe u w

open FirstOrder

variable {Role : Type u}

/-- The strong-Kleene identification is an actual language homomorphism,
including both constants and the role switch. -/
noncomputable def winnerHom (e : Fin 2 ≃ Role) :
    let _ := winnerStructure e
    let _ := threeStructure
    WinnerSet Role →[Equational.language Symbol] Fin 3 := by
  classical
  let := winnerStructure e
  let := threeStructure
  exact {
    toFun := rank e
    map_fun' := by
      intro n f args
      cases f
      · change rank e (WinnerSet.singleton (e 1)) = 0
        exact rank_value e 0
      · change rank e (WinnerSet.singleton (e 0)) = 2
        exact rank_value e 2
      · exact rank_rename_swap e (args 0)
      · exact rank_choice_top e (args 0) (args 1)
      · exact rank_choice_bottom e (args 0) (args 1)
    map_rel' := by intro n r; cases r }

/-- Equation validity is equivalent on the shared actual winner carrier and
on its three-element chain presentation. -/
theorem winner_holds_iff_three (e : Fin 2 ≃ Role) (eqn : Equational.Identity Symbol) :
    let _ := winnerStructure e
    let _ := threeStructure
    eqn.Holds (WinnerSet Role) ↔ eqn.Holds (Fin 3) := by
  let := winnerStructure e
  let := threeStructure
  exact ⟨fun h => eqn.holds_of_surjective (winnerHom e) (equiv e).surjective h,
    fun h => eqn.holds_of_injective (winnerHom e) (equiv e).injective h⟩

/-- Complete equational basis of the actual bounded two-player winner algebra
with both owned choices and the role switch. -/
theorem basis_winner (e : Fin 2 ≃ Role) :
    let _ := winnerStructure e
    Equational.IsBasis (WinnerSet Role) basis := by
  let := winnerStructure e
  let := threeStructure
  dsimp only
  intro eqn
  exact (winner_holds_iff_three e eqn).trans (basis_three eqn)

/-- Exact model characterization of the winner algebra's generated variety. -/
theorem inVariety_winner_iff_laws (e : Fin 2 ≃ Role) (M : Type w)
    [(Equational.language Symbol).Structure M] :
    let _ := winnerStructure e
    Equational.InVariety Symbol (WinnerSet Role) M ↔
      Laws (operationZero M) (operationOne M) (operationJoin M) (operationMeet M) (operationNeg M) := by
  let := winnerStructure e
  let := threeStructure
  constructor
  · intro h
    apply laws_iff_models.mpr
    apply h.models
    exact Equational.IsBasis.models (basis_winner e)
  · intro h
    have hthree := inVariety_three_of_laws h
    exact ⟨hthree.1,fun eqn he => hthree.2 eqn ((winner_holds_iff_three e eqn).mp he)⟩

/-- The retained main-text two-player finite-basis claim, without a cited
external generation theorem or a conditional completeness assumption. -/
theorem hasFiniteBasis_winner (e : Fin 2 ≃ Role) :
    let _ := winnerStructure e
    Equational.HasFiniteBasis Symbol (WinnerSet Role) := by
  let := winnerStructure e
  exact ⟨basis,basis_finite,basis_winner e⟩

end KFOL.TwoPlayers.Kleene
