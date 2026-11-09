module

public import KFOL.Algebra.Atomic.Necessity
public import Mathlib.Data.Fintype.Card

/-! # Every unary map has an atomic term realization -/

@[expose] public section

namespace KFOL

universe u v

namespace WinnerSet

variable {Role : Type u}

/-- A choice against a transposed copy merges one atomic label into another. -/
theorem choice_swap_singleton [DecidableEq Role] (a b x : Role) :
    choice a (singleton x) (rename (Equiv.swap a b) (singleton x)) =
      singleton (if x = b then a else x) := by
  classical
  rw [rename_singleton]
  by_cases hxb : x = b
  · subst x
    simp [choice]
  · by_cases hxa : x = a
    · subst x
      simp [choice,hxb]
    · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]
      simp only [hxb,ite_false,choice,singleton_inj,hxa,or_self,ite_false]
      apply Subtype.ext
      exact Set.union_self _

end WinnerSet

namespace Term

variable {Role : Type u} {Var : Type v}

/-- Finite unary maps are realized by permutations and elementary merges.
The induction strictly increases the image until the map is a permutation. -/
theorem atomic_realization_unary [Finite Role] (i : Var) (h : Role → Role) :
    ∃ t : Term Role Var, t.AtomicRealizes (fun v => h (v i)) := by
  classical
  let := Fintype.ofFinite Role
  have aux : ∀ n : Nat, ∀ h : Role → Role,
      Fintype.card Role - (Finset.univ.image h).card = n →
      ∃ t : Term Role Var, t.AtomicRealizes (fun v => h (v i)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro h hn
      by_cases hinj : Function.Injective h
      · let p : Equiv.Perm Role := Equiv.ofBijective h
          ⟨hinj,Finite.surjective_of_injective hinj⟩
        exact ⟨.rename p (.var i),fun v => by exact WinnerSet.rename_singleton (v i) p⟩
      · obtain ⟨a,b,hab,he⟩ : ∃ a b, a ≠ b ∧ h a = h b := by
          by_contra hno
          apply hinj
          intro a b he
          by_contra hab
          exact hno ⟨a,b,hab,he⟩
        have hsurj : ¬Function.Surjective h :=
          fun hs => hinj ((Finite.injective_iff_surjective).mpr hs)
        obtain ⟨c,hc⟩ : ∃ c, ∀ x, h x ≠ c := by
          simpa only [Function.Surjective,not_forall,not_exists] using hsurj
        let g : Role → Role := Function.update h b c
        have sub : Finset.univ.image h ⊆ Finset.univ.image g := by
          intro z hz
          obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hz
          by_cases hx : x = b
          · subst x
            exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,by simp [g,hab,he]⟩
          · exact Finset.mem_image.mpr ⟨x,Finset.mem_univ _,by simp [g,hx]⟩
        have strict : Finset.univ.image h ⊂ Finset.univ.image g := by
          apply Finset.ssubset_iff_subset_ne.mpr
          refine ⟨sub,?_⟩
          intro heq
          have hcin : c ∈ Finset.univ.image g :=
            Finset.mem_image.mpr ⟨b,Finset.mem_univ _,by simp [g]⟩
          rw [← heq] at hcin
          obtain ⟨x,_,hx⟩ := Finset.mem_image.mp hcin
          exact hc x hx
        have hcard := Finset.card_lt_card strict
        have hbound := Finset.card_le_card (Finset.subset_univ (Finset.univ.image g))
        have hlt : Fintype.card Role - (Finset.univ.image g).card < n := by
          simp only [Finset.card_univ] at hbound
          omega
        obtain ⟨t,ht⟩ := ih _ hlt g rfl
        refine ⟨.choice (h b) t (.rename (Equiv.swap (h b) c) t),?_⟩
        intro v
        change WinnerSet.choice (h b) (t.eval _) (WinnerSet.rename _ (t.eval _)) = _
        rw [ht v,WinnerSet.choice_swap_singleton]
        apply congrArg WinnerSet.singleton
        by_cases hv : v i = b
        · simp [g,hv]
        · simp [g,hv,hc]
  exact aux _ h rfl

end Term

end KFOL
