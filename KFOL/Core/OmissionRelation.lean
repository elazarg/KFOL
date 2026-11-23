module

public import KFOL.Core.Profiles
public import KFOL.Equational.Native

/-! # A binary invariant for omitting a set of owners -/

@[expose] public section

namespace KFOL.Core

variable {Role Var : Type*}
attribute [local instance] Equational.coreStructure

/-- Singleton flags outside the chosen owners agree. When the first menu
omits those owners, the menus agree entirely. -/
def OmissionRelation (owners : Set Role) (first second : WinnerSet Role) : Prop :=
  (∀ r ∉ owners, first = WinnerSet.singleton r ↔ second = WinnerSet.singleton r) ∧
    (first.val ⊆ ownersᶜ → first = second)

theorem OmissionRelation.choice {owners : Set Role} {x x' y y' : WinnerSet Role}
    (hx : OmissionRelation owners x x') (hy : OmissionRelation owners y y') (r : Role) :
    OmissionRelation owners (WinnerSet.choice r x y) (WinnerSet.choice r x' y') := by
  classical
  constructor
  · intro s hs
    by_cases hrs : r = s
    · subst s
      rw [WinnerSet.choice_eq_owner_iff, WinnerSet.choice_eq_owner_iff, hx.1 r hs, hy.1 r hs]
    · rw [WinnerSet.choice_eq_other_iff _ _ _ hrs, WinnerSet.choice_eq_other_iff _ _ _ hrs,
        hx.1 s hs, hy.1 s hs]
  · intro homit
    by_cases habsorb : x = WinnerSet.singleton r ∨ y = WinnerSet.singleton r
    · have hfirst := (WinnerSet.choice_eq_owner_iff x y r).2 habsorb
      have hr : r ∉ owners := homit (by simp [hfirst])
      have hsecond : WinnerSet.choice r x' y' = WinnerSet.singleton r :=
        (WinnerSet.choice_eq_owner_iff x' y' r).2
          (habsorb.imp (hx.1 r hr).mp (hy.1 r hr).mp)
      exact hfirst.trans hsecond.symm
    · have hfirst : WinnerSet.choice r x y = x.union y := by
        simp [WinnerSet.choice, habsorb]
      rw [hfirst] at homit
      have hxe := hx.2 (Set.subset_union_left.trans homit)
      have hye := hy.2 (Set.subset_union_right.trans homit)
      rw [hxe, hye]

theorem OmissionRelation.realize {owners : Set Role} {first second : Var → WinnerSet Role}
    (h : ∀ v, OmissionRelation owners (first v) (second v))
    (t : Equational.Term (Equational.CoreSymbol Role) Var) :
    OmissionRelation owners (t.realize first) (t.realize second) := by
  induction t using induction_choice with
  | var v => exact h v
  | choice r x y hx hy =>
    change OmissionRelation owners
      (WinnerSet.choice r (x.realize first) (y.realize first))
      (WinnerSet.choice r (x.realize second) (y.realize second))
    exact hx.choice hy r

end KFOL.Core
