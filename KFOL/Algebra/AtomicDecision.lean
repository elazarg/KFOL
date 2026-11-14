module

public import KFOL.Definitions.AtomicDecision
public import KFOL.Algebra.Basic
public import KFOL.Definitions.Core

/-! # Atomic possible winners without internal role switches -/

@[expose] public section

namespace KFOL

universe u v

private def ObserverBelow {Role : Type u} (k : Role)
    (left right : WinnerSet Role) : Prop :=
  (k ∈ left.val → k ∈ right.val) ∧
    ∀ r, r ≠ k → right = WinnerSet.singleton r → left = WinnerSet.singleton r

private theorem observerBelow_choice {Role : Type u} (k r : Role)
    {A B C D : WinnerSet Role} (left : ObserverBelow k A C)
    (right : ObserverBelow k B D) :
    ObserverBelow k (WinnerSet.choice r A B) (WinnerSet.choice r C D) := by
  classical
  constructor
  · intro wins
    by_cases absorb : C = WinnerSet.singleton r ∨ D = WinnerSet.singleton r
    · have new : WinnerSet.choice r C D = WinnerSet.singleton r :=
        (WinnerSet.choice_eq_owner_iff C D r).mpr absorb
      rw [new]
      by_cases same : r = k
      · subst r; exact Set.mem_singleton k
      · have old : WinnerSet.choice r A B = WinnerSet.singleton r := by
          apply (WinnerSet.choice_eq_owner_iff A B r).mpr
          exact absorb.imp (left.2 r same) (right.2 r same)
        rw [old] at wins
        exact False.elim (same (Set.mem_singleton_iff.mp wins).symm)
    · rw [WinnerSet.choice, ite_eq_right absorb]
      exact (WinnerSet.choice_subset_union r A B wins).imp left.1 right.1
  · intro other different equal
    by_cases owner : r = other
    · subst r
      apply (WinnerSet.choice_eq_owner_iff A B other).mpr
      exact ((WinnerSet.choice_eq_owner_iff C D other).mp equal).imp
        (left.2 other different) (right.2 other different)
    · apply (WinnerSet.choice_eq_other_iff A B r owner).mpr
      have parts := (WinnerSet.choice_eq_other_iff C D r owner).mp equal
      exact ⟨left.2 other different parts.1, right.2 other different parts.2⟩

namespace Term

private theorem public_observer_max {Role : Type u} {Var : Type v}
    (term : Term Role Var) (publicOnly : term.IsPublic) (k : Role)
    (valuation : Var → WinnerSet Role) :
    ObserverBelow k (term.eval valuation)
      (term.eval (fun _ => WinnerSet.singleton k)) := by
  classical
  induction term with
  | winner r => exact ⟨id, fun _ _ equal => equal⟩
  | var name =>
    refine ⟨fun _ => Set.mem_singleton k, ?_⟩
    intro r different equal
    exact False.elim (different (WinnerSet.singleton_inj.mp equal).symm)
  | choice r left right ihl ihr =>
    exact observerBelow_choice k r (ihl publicOnly.1) (ihr publicOnly.2)
  | rename _ _ _ => exact False.elim publicOnly

/-- For public terms, making every input the queried player's singleton
already maximizes that player's possible-win observation. -/
theorem IsPublic.possibleWin_iff {Role : Type u} {Var : Type v}
    {term : Term Role Var} (publicOnly : term.IsPublic) (k : Role) :
    (∃ valuation : Var → WinnerSet Role, k ∈ (term.eval valuation).val) ↔
      k ∈ (term.eval (fun _ => WinnerSet.singleton k)).val := by
  constructor
  · rintro ⟨valuation, wins⟩
    exact (public_observer_max term publicOnly k valuation).1 wins
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
