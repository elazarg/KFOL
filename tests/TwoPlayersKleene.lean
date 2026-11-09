module

import KFOL.Algebra.TwoPlayers.Kleene.Syntax

namespace KFOL.TwoPlayersKleeneRegression

universe u w

open TwoPlayers.Kleene

/-- Complete finite-basis claim in the actual two-player owned-choice,
winner-constant and role-switch signature. -/
theorem finite_kleene_basis {Role : Type u} (labels : Fin 2 ≃ Role) :
    let _ := winnerStructure labels
    basis.Finite ∧ ∀ e : Equational.Identity Symbol,
      e.Holds (WinnerSet Role) ↔ Equational.Derives basis e.lhs e.rhs := by
  let := winnerStructure labels
  exact ⟨basis_finite,basis_winner labels⟩

/-- Every raw-law model, in an arbitrary universe, satisfies every identity
of the actual two-player winner algebra. -/
theorem model_characterization {Role : Type u} (labels : Fin 2 ≃ Role)
    (M : Type w) [(Equational.language Symbol).Structure M] :
    let _ := winnerStructure labels
    Equational.InVariety Symbol (WinnerSet Role) M ↔
      Laws (operationZero M) (operationOne M) (operationJoin M) (operationMeet M) (operationNeg M) :=
  inVariety_winner_iff_laws labels M

example : let _ := winnerStructure (Equiv.refl (Fin 2))
    Equational.HasFiniteBasis Symbol (WinnerSet (Fin 2)) :=
  hasFiniteBasis_winner (Equiv.refl _)

example : let _ := threeStructure
    Equational.Derives basis (negTerm (topTerm : TwoPlayers.Kleene.Term (Fin 0))) botTerm := by
  let := threeStructure
  dsimp only
  apply (basis_three ⟨0,negTerm topTerm,botTerm⟩).mp
  intro v
  rfl

example (n : Nat) (s t : KFOL.Term (Fin 2) (Fin n)) :
    (∀ v : Fin n → WinnerSet (Fin 2), s.eval v = t.eval v) ↔
      Equational.Derives basis (ofPublic (Equiv.refl _) s) (ofPublic (Equiv.refl _) t) :=
  public_equational_completeness (Equiv.refl _) n s t

end KFOL.TwoPlayersKleeneRegression

#print axioms KFOL.TwoPlayers.Kleene.basis_three
#print axioms KFOL.TwoPlayers.Kleene.basis_winner
#print axioms KFOL.TwoPlayers.Kleene.inVariety_winner_iff_laws
#print axioms KFOL.TwoPlayers.Kleene.hasFiniteBasis_winner
