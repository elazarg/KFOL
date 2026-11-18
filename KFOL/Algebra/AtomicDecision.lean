module

public import KFOL.Definitions.AtomicDecision
public import KFOL.Algebra.ViewOrders.Monotone
public import KFOL.Definitions.Core

/-! # Atomic possible winners without internal role switches -/

@[expose] public section

namespace KFOL

universe u v

namespace Term

private theorem public_observer_max {Role : Type u} {Var : Type v}
    (term : Term Role Var) (publicOnly : term.IsPublic) (k : Role)
    (valuation : Var → WinnerSet Role) :
    PlayerView.Below k (WinnerSet.view k (term.eval valuation))
      (WinnerSet.view k (term.eval (fun _ => WinnerSet.singleton k))) := by
  classical
  induction term with
  | winner r => exact (WinnerSet.view_below_iff _ _ _).mpr ⟨id, fun _ _ equal => equal⟩
  | var name =>
    apply (WinnerSet.view_below_iff _ _ _).mpr
    refine ⟨fun _ => Set.mem_singleton k, ?_⟩
    intro r different equal
    exact False.elim (different (WinnerSet.singleton_inj.mp equal).symm)
  | choice r left right ihl ihr =>
    exact WinnerSet.view_choice_mono k r (ihl publicOnly.1) (ihr publicOnly.2)
  | rename _ _ _ => exact False.elim publicOnly

/-- For public terms, making every input the queried player's singleton
already maximizes that player's possible-win observation. -/
theorem IsPublic.possibleWin_iff {Role : Type u} {Var : Type v}
    {term : Term Role Var} (publicOnly : term.IsPublic) (k : Role) :
    (∃ valuation : Var → WinnerSet Role, k ∈ (term.eval valuation).val) ↔
      k ∈ (term.eval (fun _ => WinnerSet.singleton k)).val := by
  constructor
  · rintro ⟨valuation, wins⟩
    exact ((WinnerSet.view_below_iff _ _ _).mp
      (public_observer_max term publicOnly k valuation)).1 wins
  · exact fun wins => ⟨_, wins⟩

/-- Atomic and unrestricted possible-win existence coincide without role
switches, and both are decided by one original term evaluation. -/
theorem IsPublic.atomicPossibleWin_iff {Role : Type u} {Var : Type v}
    {term : Term Role Var} (publicOnly : term.IsPublic) (k : Role) :
    term.AtomicPossibleWin k ↔
      k ∈ (term.eval (fun _ => WinnerSet.singleton k)).val := by
  constructor
  · rintro ⟨valuation, wins⟩
    exact publicOnly.possibleWin_iff k |>.mp ⟨_, wins⟩
  · exact fun wins => ⟨fun _ => k, wins⟩

end Term
end KFOL
