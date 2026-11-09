module

import KFOL.Algebra.ViewOrders.Order

namespace KFOL.ViewOrdersRegression

universe u

/-- Complete actual quotient table and explicit layered semilattice order. -/
theorem player_view_orders {Role : Type u} (three : Fin 3 ↪ Role) (k r : Role) :
    (∀ A B : WinnerSet Role, WinnerSet.view k (WinnerSet.choice r A B) =
      PlayerView.choice r (WinnerSet.view k A) (WinnerSet.view k B)) ∧
    ∃ order : SemilatticeSup (PlayerView k),
      (let _ := order
       (∀ p q : PlayerView k, p ⊔ q = PlayerView.choice r p q) ∧
       (∀ p q : PlayerView k, p ≤ q ↔ match p,q with
         | .possible,.possible => True
         | .possible,.impossible => False
         | .possible,.other j => j.val = r
         | .impossible,.possible | .impossible,.impossible => True
         | .impossible,.other j => j.val = r
         | .other i,.possible | .other i,.impossible => i.val ≠ r
         | .other i,.other j => i = j ∨ j.val = r)) := by
  refine ⟨WinnerSet.view_choice k r,PlayerView.semilatticeSup three k r,?_,?_⟩
  · exact fun _ _ => rfl
  · exact PlayerView.order_layers three k r

example : PlayerView.choice (1 : Fin 3) (.impossible : PlayerView (0 : Fin 3)) .possible = .possible := by
  classical
  simp [PlayerView.choice,PlayerView.union]

example : PlayerView.choice (1 : Fin 3) (.other ⟨1,by decide⟩ : PlayerView (0 : Fin 3)) .possible =
    .other ⟨1,by decide⟩ := by
  classical
  simp [PlayerView.choice]

example : PlayerView.choice (0 : Fin 3) (.other ⟨1,by decide⟩ : PlayerView (0 : Fin 3))
    (.other ⟨2,by decide⟩) = .impossible := by
  classical
  simp [PlayerView.choice,PlayerView.union,Subtype.ext_iff]

end KFOL.ViewOrdersRegression

#print axioms KFOL.WinnerSet.view_choice
#print axioms KFOL.PlayerView.semilatticeSup
#print axioms KFOL.PlayerView.order_layers
