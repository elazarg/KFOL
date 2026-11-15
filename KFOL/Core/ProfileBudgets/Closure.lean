module

public import KFOL.Definitions.ProfileBudgets

/-! # The Horn closure and the greatest simultaneously safe support -/

@[expose] public section
namespace KFOL.Core.ProfileBudgets
universe u v w
variable {Role : Type u} {Var : Type v} {Row : Type w}
variable (b : Row → Budget Role Var) (r : Role)

theorem subset_budgetClosure (T : Set Var) : T ⊆ budgetClosure b r T :=
  fun _ hj _ hTC _ => hTC hj

theorem budgetClosure_le {T C : Set Var} (hTC : T ⊆ C) (hC : BudgetClosed b r C) :
    budgetClosure b r T ⊆ C := fun _ hj => hj C hTC hC

theorem budgetClosure_closed (T : Set Var) : BudgetClosed b r (budgetClosure b r T) := by
  intro i hp j hj C hTC hC
  apply hC i ?_ j hj
  intro hr k hk
  exact hp hr k hk C hTC hC

/-- The complement Horn rules express precisely simultaneous fold safety. -/
theorem safeSupport_iff_closed (S : Set Var) :
    SafeSupport b r S ↔ BudgetClosed b r Sᶜ := by
  classical
  constructor
  · intro h i hp j hj hjS
    rcases h i with hs | ⟨hr,k,hk,hke⟩
    · exact hj (hs j hjS)
    · exact hp hr k hke hk
  · intro h i
    by_cases hs : ∀ j ∈ S, ((b i).values j).val ⊆ (b i).allowed
    · exact Or.inl hs
    · right
      by_contra hn
      have hp : r ∈ (b i).allowed →
          ∀ j, (b i).values j = WinnerSet.singleton r → j ∈ Sᶜ := by
        intro hr j hj hjS
        exact hn ⟨hr,j,hjS,hj⟩
      apply hs
      intro j hj
      by_contra hbad
      exact h i hp j hbad hj

theorem greatestSupport_subset (D : Set Var) : greatestSupport b r D ⊆ D := by
  intro j hj
  by_contra hn
  exact hj (subset_budgetClosure b r Dᶜ hn)

theorem greatestSupport_safe (D : Set Var) : SafeSupport b r (greatestSupport b r D) := by
  apply (safeSupport_iff_closed b r _).mpr
  simpa only [greatestSupport,compl_compl] using budgetClosure_closed b r Dᶜ

theorem safeSupport_le_greatest {S D : Set Var} (hS : SafeSupport b r S) (hSD : S ⊆ D) :
    S ⊆ greatestSupport b r D := by
  intro j hj hcl
  have hDC : Dᶜ ⊆ Sᶜ := fun _ hd hs => hd (hSD hs)
  exact budgetClosure_le b r hDC ((safeSupport_iff_closed b r S).mp hS) hcl hj

/-- A single closure computes simultaneous feasibility with arbitrary permitted
positions and a required position in a second set. -/
theorem greatestSupport_meets_iff (D H : Set Var) :
    (∃ j ∈ greatestSupport b r D, j ∈ H) ↔
      ∃ S : Set Var, SafeSupport b r S ∧ S ⊆ D ∧ ∃ j ∈ S, j ∈ H := by
  constructor
  · intro h
    exact ⟨greatestSupport b r D,greatestSupport_safe b r D,
      greatestSupport_subset b r D,h⟩
  · rintro ⟨S,hs,hsd,j,hj,hH⟩
    exact ⟨j,safeSupport_le_greatest b r hs hsd hj,hH⟩

end KFOL.Core.ProfileBudgets
