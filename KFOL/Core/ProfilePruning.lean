module

public import KFOL.Core.Profiles
public import KFOL.Algebra.ViewOrders.Monotone

/-! # Restricting variables along a positive singleton profile -/

@[expose] public section

namespace KFOL.Core

universe u v w
variable {Role : Type u} [DecidableEq Role] {Var : Type v}
attribute [local instance] Equational.coreStructure

/-- A positive owner profile on a coalition gives a term using only that coalition,
below the original in the owner's view at every valuation. -/
theorem exists_view_below_of_profile (a : Role) (A : Var → Bool)
    (t : Equational.Term (Equational.CoreSymbol Role) Var) (positive : profile a A t = true) :
    ∃ u : Equational.Term (Equational.CoreSymbol Role) {x // A x = true},
      ∀ v : Var → WinnerSet Role, PlayerView.Below a
        (WinnerSet.view a (u.realize (fun x => v x.val))) (WinnerSet.view a (t.realize v)) := by
  induction t using induction_choice with
  | var x =>
    refine ⟨.var ⟨x, positive⟩, fun _ => (WinnerSet.view_below_iff _ _ _).mpr ?_⟩
    exact ⟨id, fun _ _ => id⟩
  | choice r s t ihs iht =>
    by_cases same : r = a
    · subst r
      simp only [profile_choice, ite_true, Bool.or_eq_true] at positive
      rcases positive with hs | ht
      · obtain ⟨u, hu⟩ := ihs hs
        exact ⟨u, fun v => WinnerSet.view_below_choice_self a (Or.inl (hu v))⟩
      · obtain ⟨u, hu⟩ := iht ht
        exact ⟨u, fun v => WinnerSet.view_below_choice_self a (Or.inr (hu v))⟩
    · simp only [profile_choice, ite_eq_right same, Bool.and_eq_true] at positive
      obtain ⟨u, hu⟩ := ihs positive.1
      obtain ⟨w, hw⟩ := iht positive.2
      exact ⟨choiceTerm r u w, fun v => WinnerSet.view_choice_mono a r (hu v) (hw v)⟩

/-- The same restricted term preserves every omission of the owner on an arbitrary
family of rows, including the marked probes for source coefficients. -/
theorem exists_omitting_of_profile {Row : Type w} (a : Role) (A : Var → Bool)
    (t : Equational.Term (Equational.CoreSymbol Role) Var) (positive : profile a A t = true)
    (rows : Row → Var → WinnerSet Role) (omitted : ∀ j, a ∉ (t.realize (rows j)).val) :
    ∃ u : Equational.Term (Equational.CoreSymbol Role) {x // A x = true},
      ∀ j, a ∉ (u.realize (fun x => rows j x.val)).val := by
  obtain ⟨u, hu⟩ := exists_view_below_of_profile a A t positive
  exact ⟨u, fun j wins => omitted j (((WinnerSet.view_below_iff _ _ _).mp (hu (rows j))).1 wins)⟩

end KFOL.Core
