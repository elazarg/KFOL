module

public import KFOL.Algebra.ViewOrders.Table
public import Mathlib.Order.Lattice

/-! # Each player-view owned choice is the join of its explicit layered order -/

@[expose] public section

namespace KFOL.PlayerView

universe u

open Classical

variable {Role : Type u}

theorem choice_comm (three : Fin 3 ↪ Role) (k r : Role) (p q : PlayerView k) :
    choice r p q = choice r q p := by
  have h := congrArg (WinnerSet.view k) (WinnerSet.choice_comm
    (representative three k p) (representative three k q) r)
  simpa only [WinnerSet.view_choice,view_representative] using h

theorem choice_assoc (three : Fin 3 ↪ Role) (k r : Role) (p q s : PlayerView k) :
    choice r (choice r p q) s = choice r p (choice r q s) := by
  have h := congrArg (WinnerSet.view k) (WinnerSet.choice_assoc
    (representative three k p) (representative three k q) r (representative three k s))
  simpa only [WinnerSet.view_choice,view_representative] using h

theorem choice_idempotent (three : Fin 3 ↪ Role) (k r : Role) (p : PlayerView k) :
    choice r p p = p := by
  have h := congrArg (WinnerSet.view k) (WinnerSet.choice_idempotent r (representative three k p))
  simpa only [WinnerSet.view_choice,view_representative] using h

/-- The actual mathlib semilattice structure whose join is owned choice on
views. The chosen three roles are used only to prove quotient realization. -/
@[instance_reducible] noncomputable def semilatticeSup (three : Fin 3 ↪ Role) (k r : Role) :
    SemilatticeSup (PlayerView k) :=
  letI : Max (PlayerView k) := ⟨choice r⟩
  SemilatticeSup.mk' (choice_comm three k r) (choice_assoc three k r) (choice_idempotent three k r)

/-- Complete order table: the nonabsorbing atoms form an antichain below
impossible, then possible; when the owner is another player, its atom is top.
This also covers the observing owner, when no such extra atom exists. -/
theorem order_layers (three : Fin 3 ↪ Role) (k r : Role) (p q : PlayerView k) :
    let _ := semilatticeSup three k r
    p ≤ q ↔ match p,q with
      | .possible,.possible => True
      | .possible,.impossible => False
      | .possible,.other j => j.val = r
      | .impossible,.possible | .impossible,.impossible => True
      | .impossible,.other j => j.val = r
      | .other i,.possible | .other i,.impossible => i.val ≠ r
      | .other i,.other j => i = j ∨ j.val = r := by
  change choice r p q = q ↔ _
  cases p <;> cases q
  all_goals unfold choice union
  all_goals split_ifs <;> simp_all [Subtype.ext_iff]
  all_goals try split_ifs
  all_goals try simp_all [Subtype.ext_iff]
  all_goals aesop

/-- The quotient table is genuinely the join in the displayed order. -/
theorem choice_eq_sup (three : Fin 3 ↪ Role) (k r : Role) (p q : PlayerView k) :
    let _ := semilatticeSup three k r
    choice r p q = p ⊔ q := rfl

end KFOL.PlayerView
