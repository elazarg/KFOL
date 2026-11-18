module

public import KFOL.Core.ProfileSynthesis
public import KFOL.Algebra.Semilattice

/-! # Absorption by a singleton winning coalition -/

@[expose] public section

namespace KFOL.Core

universe u v

variable {Role : Type u} [DecidableEq Role] {Var : Type v} [DecidableEq Var]
attribute [local instance] Equational.coreStructure

/-- If one input can force the owner singleton, each value either is that
singleton or includes the entire menu at this input. -/
theorem eq_singleton_or_subset_of_profile_singleton
    (t : Equational.Term (Equational.CoreSymbol Role) Var) (r : Role) (j : Var)
    (v : Var → WinnerSet Role) (hp : profile r (fun x => decide (x = j)) t = true) :
    t.realize v = WinnerSet.singleton r ∨ (v j).val ⊆ (t.realize v).val := by
  classical
  induction t using induction_choice with
  | var x =>
    obtain rfl : x = j := of_decide_eq_true hp
    exact Or.inr (fun _ h => h)
  | choice s x y hx hy =>
    change WinnerSet.choice s (x.realize v) (y.realize v) = _ ∨
      (v j).val ⊆ (WinnerSet.choice s (x.realize v) (y.realize v)).val
    by_cases hs : s = r
    · subst s
      by_cases ha : x.realize v = WinnerSet.singleton r ∨ y.realize v = WinnerSet.singleton r
      · exact Or.inl ((WinnerSet.choice_eq_owner_iff _ _ r).mpr ha)
      · simp only [WinnerSet.choice, ite_eq_right ha]
        rw [profile_choice, ite_eq_left rfl, Bool.or_eq_true] at hp
        rcases hp with hp | hp
        · exact Or.inr (((hx hp).resolve_left (not_or.mp ha).1).trans Set.subset_union_left)
        · exact Or.inr (((hy hp).resolve_left (not_or.mp ha).2).trans Set.subset_union_right)
    · rw [profile_choice, ite_eq_right hs, Bool.and_eq_true] at hp
      have hleft := hx hp.1
      have hright := hy hp.2
      by_cases ha : x.realize v = WinnerSet.singleton s ∨ y.realize v = WinnerSet.singleton s
      · rw [show WinnerSet.choice s (x.realize v) (y.realize v) = WinnerSet.singleton s
              from (WinnerSet.choice_eq_owner_iff _ _ s).mpr ha]
        rcases ha with he | he
        · rwa [he] at hleft
        · rwa [he] at hright
      · simp only [WinnerSet.choice, ite_eq_right ha]
        rcases hleft with he | hsub
        · rcases hright with he' | hsub
          · exact Or.inl ((WinnerSet.union_eq_singleton_iff _ _ r).mpr ⟨he, he'⟩)
          · exact Or.inr (hsub.trans Set.subset_union_right)
        · exact Or.inr (hsub.trans Set.subset_union_left)

/-- A singleton winning coalition is absorbed at every valuation, including
when its input menu is the owner's singleton. -/
theorem choice_eq_of_profile_singleton
    (t : Equational.Term (Equational.CoreSymbol Role) Var) (r : Role) (j : Var)
    (v : Var → WinnerSet Role) (hp : profile r (fun x => decide (x = j)) t = true) :
    WinnerSet.choice r (v j) (t.realize v) = t.realize v := by
  classical
  apply (WinnerSet.choice_le_iff r _ _).mpr
  by_cases hj : v j = WinnerSet.singleton r
  · apply Or.inl
    apply (winnerSet_eq_singleton_iff_profile t r v).mpr
    exact profile_mono r _ _ (fun x hx => by
      obtain rfl : x = j := of_decide_eq_true hx
      exact decide_eq_true hj) t hp
  · exact (eq_singleton_or_subset_of_profile_singleton t r j v hp).imp_right (And.intro hj)

/-- The input alone can force the owner exactly when adjoining the input
by the owner's choice preserves the operation. Two distinct possible
roles suffice to read the prescribed profile bit from a valuation. -/
theorem profile_singleton_iff_choice_eq [Nontrivial Role]
    (t : Equational.Term (Equational.CoreSymbol Role) Var) (r : Role) (j : Var) :
    profile r (fun x => decide (x = j)) t = true ↔
      ∀ v : Var → WinnerSet Role, WinnerSet.choice r (v j) (t.realize v) = t.realize v := by
  classical
  constructor
  · exact fun hp v => choice_eq_of_profile_singleton t r j v hp
  · intro h
    obtain ⟨s, hs⟩ := exists_ne r
    let v (x : Var) := WinnerSet.singleton (if x = j then r else s)
    have hj : v j = WinnerSet.singleton r := by simp [v]
    have he : t.realize v = WinnerSet.singleton r :=
      (h v).symm.trans ((WinnerSet.choice_eq_owner_iff _ _ r).mpr (Or.inl hj))
    have hbits : (fun x => decide (v x = WinnerSet.singleton r)) = (fun x => decide (x = j)) := by
      funext x
      by_cases hx : x = j <;> simp [v, hx, hs]
    simpa only [hbits] using (winnerSet_eq_singleton_iff_profile t r v).mp he

end KFOL.Core
