module

import KFOL.Algebra.TwoPlayers.Coordinates

namespace KFOL.TwoPlayersRegression

universe u

open Classical

/-- Complete two-player strong-Kleene identification. -/
theorem kleene {Role : Type u} (labels : Fin 2 ≃ Role) :
    ∃ q : WinnerSet Role ≃ Fin 3,
      (∀ i, q (TwoPlayers.value labels i) = i) ∧
      (∀ A B, q (WinnerSet.choice (labels 0) A B) = max (q A) (q B)) ∧
      (∀ A B, q (WinnerSet.choice (labels 1) A B) = min (q A) (q B)) ∧
      (∀ A, q (WinnerSet.rename (Equiv.swap (labels 0) (labels 1)) A) = (q A).rev) :=
  TwoPlayers.strong_kleene_identification labels

example : (TwoPlayers.value (Equiv.refl (Fin 2)) 1).Ambiguous :=
  TwoPlayers.ambiguous_middle _

example (A B : WinnerSet (Fin 2)) : A.reset B = B :=
  TwoPlayers.reset_projection (Equiv.refl _) A B

example : ¬∃ t : Term (Fin 2) (Fin 2), ∀ v : Fin 2 → WinnerSet (Fin 2),
    t.eval v = (v 0).union (v 1) :=
  TwoPlayers.union_not_definable (Equiv.refl _)

example : ∃ t : Term (Fin 2) (Fin 2),
    (∀ A : WinnerSet (Fin 2), t.eval (fun _ => A) = A) ∧
    ¬∃ s : Term (Fin 2) (Fin 2), s.IsCore ∧ (∀ v : Fin 2 → WinnerSet (Fin 2), s.eval v = t.eval v) :=
  TwoPlayers.idempotent_not_core (Equiv.refl _)

end KFOL.TwoPlayersRegression

#print axioms KFOL.TwoPlayers.strong_kleene_identification
#print axioms KFOL.TwoPlayers.atom_preserving
#print axioms KFOL.TwoPlayers.idempotent_not_core
#print axioms KFOL.TwoPlayers.forcingCoordinates_injective
