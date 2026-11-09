module

public import KFOL.Definitions.Public
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.GroupTheory.Perm.Basic

/-! # Elementary facts about nonempty winner sets and term substitution -/

@[expose] public section

namespace KFOL

universe u v w

/-- Three distinct roles ensure a role outside any specified pair. -/
theorem exists_role_outside_pair {Role : Type u} (three : Fin 3 ↪ Role) (a b : Role) :
    ∃ k, k ≠ a ∧ k ≠ b := by
  have h01 := three.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have h02 := three.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have h12 := three.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  by_cases h0 : three 0 = a ∨ three 0 = b
  · by_cases h1 : three 1 = a ∨ three 1 = b
    · rcases h0 with ha | hb <;> rcases h1 with ha' | hb'
      · exact False.elim (h01 (ha.trans ha'.symm))
      · exact ⟨three 2, fun h => h02 (ha.trans h.symm),
          fun h => h12 (hb'.trans h.symm)⟩
      · exact ⟨three 2, fun h => h12 (ha'.trans h.symm),
          fun h => h02 (hb.trans h.symm)⟩
      · exact False.elim (h01 (hb.trans hb'.symm))
    · exact ⟨three 1, fun h => h1 (Or.inl h), fun h => h1 (Or.inr h)⟩
  · exact ⟨three 0, fun h => h0 (Or.inl h), fun h => h0 (Or.inr h)⟩

namespace WinnerSet

variable {Role : Type u} (A B : WinnerSet Role) (r : Role)

@[simp] theorem val_singleton : (singleton r).val = {r} := rfl

@[simp] theorem val_union : (union A B).val = A.val ∪ B.val := rfl

@[simp] theorem singleton_inj {a b : Role} : singleton a = singleton b ↔ a = b := by
  constructor
  · intro h
    have := congrArg Subtype.val h
    exact Set.singleton_injective this
  · rintro rfl
    rfl

theorem eq_singleton_of_subset (h : A.val ⊆ {r}) : A = singleton r := by
  apply Subtype.ext
  exact Set.eq_singleton_iff_nonempty_unique_mem.mpr ⟨A.property, fun _ ha => h ha⟩

theorem union_eq_singleton_iff : union A B = singleton r ↔
    A = singleton r ∧ B = singleton r := by
  constructor
  · intro h
    have hval : A.val ∪ B.val = {r} := congrArg Subtype.val h
    exact ⟨eq_singleton_of_subset A r (by rw [← hval]; exact Set.subset_union_left),
      eq_singleton_of_subset B r (by rw [← hval]; exact Set.subset_union_right)⟩
  · rintro ⟨rfl, rfl⟩
    apply Subtype.ext
    exact Set.union_self _

theorem choice_eq_owner_iff : choice r A B = singleton r ↔
    A = singleton r ∨ B = singleton r := by
  classical
  by_cases h : A = singleton r ∨ B = singleton r
  · simp [choice, h]
  · simp only [choice, ite_eq_right h, union_eq_singleton_iff]
    exact ⟨fun hab => False.elim (h (Or.inl hab.1)), fun hab => False.elim (h hab)⟩

theorem choice_eq_other_iff {i : Role} (hri : r ≠ i) :
    choice r A B = singleton i ↔ A = singleton i ∧ B = singleton i := by
  classical
  by_cases h : A = singleton r ∨ B = singleton r
  · have hn : ¬ (A = singleton i ∧ B = singleton i) := by
      rintro ⟨ha, hb⟩
      rcases h with h | h
      · exact hri (singleton_inj.mp (h.symm.trans ha))
      · exact hri (singleton_inj.mp (h.symm.trans hb))
    simp [choice, h, hri, hn]
  · simp only [choice, ite_eq_right h, union_eq_singleton_iff]

@[simp] theorem rename_singleton (p : Equiv.Perm Role) :
    rename p (singleton r) = singleton (p r) := by
  apply Subtype.ext
  exact Set.image_singleton

theorem rename_injective (p : Equiv.Perm Role) : Function.Injective (rename p) := by
  intro A B h
  apply Subtype.ext
  exact Set.image_injective.mpr p.injective (congrArg Subtype.val h)

theorem rename_eq_singleton_iff (p : Equiv.Perm Role) :
    rename p A = singleton (p r) ↔ A = singleton r := by
  rw [← rename_singleton]
  exact (rename_injective p).eq_iff

@[simp] theorem rename_one (A : WinnerSet Role) : rename 1 A = A := by
  apply Subtype.ext
  exact Set.image_id _

@[simp] theorem rename_mul (p q : Equiv.Perm Role) (A : WinnerSet Role) :
    rename (p * q) A = rename p (rename q A) := by
  apply Subtype.ext
  exact (Set.image_image p q A.val).symm

@[simp] theorem rename_union (p : Equiv.Perm Role) (A B : WinnerSet Role) :
    rename p (union A B) = union (rename p A) (rename p B) := by
  apply Subtype.ext
  exact Set.image_union _ _ _

/-- Owned choice is equivariant when the owner is transported as well. -/
theorem rename_choice (p : Equiv.Perm Role) (r : Role) (A B : WinnerSet Role) :
    rename p (choice r A B) = choice (p r) (rename p A) (rename p B) := by
  classical
  have hA := rename_eq_singleton_iff A r p
  have hB := rename_eq_singleton_iff B r p
  by_cases h : A = singleton r ∨ B = singleton r
  · simp [choice, h, (or_congr hA hB).mpr h]
  · have hn : ¬(rename p A = singleton (p r) ∨ rename p B = singleton (p r)) :=
      fun hh => h ((or_congr hA hB).mp hh)
    simp [choice, h, hn]

@[simp] theorem union_self : union A A = A := by
  apply Subtype.ext
  exact Set.union_self _

theorem union_comm : union A B = union B A := by
  apply Subtype.ext
  exact Set.union_comm _ _

@[simp] theorem choice_self : choice r A A = A := by
  classical
  by_cases h : A = singleton r
  · simp [choice, h]
  · simp [choice, h]

theorem choice_comm : choice r A B = choice r B A := by
  classical
  by_cases h : A = singleton r ∨ B = singleton r
  · have h' : B = singleton r ∨ A = singleton r := h.symm
    simp [choice, h, h']
  · have h' : ¬ (B = singleton r ∨ A = singleton r) := fun h' => h h'.symm
    simpa only [choice, ite_eq_right h, ite_eq_right h'] using union_comm A B

theorem singleton_union_of_mem (a : Role) (ha : a ∈ A.val) :
    union (singleton a) A = A := by
  apply Subtype.ext
  change {a} ∪ A.val = A.val
  rw [Set.singleton_union, Set.insert_eq_of_mem ha]

/-- Each owned choice is associative, including all tie cases. -/
theorem choice_assoc (C : WinnerSet Role) : choice r (choice r A B) C = choice r A (choice r B C) := by
  classical
  by_cases ha : A = singleton r <;> by_cases hb : B = singleton r <;>
    by_cases hc : C = singleton r
  all_goals simp_all [choice, union_eq_singleton_iff]
  apply Subtype.ext
  exact Set.union_assoc _ _ _

theorem choice_singleton_of_mem (a : Role) (har : a ≠ r) (ha : a ∈ A.val) :
    choice r (singleton a) A = A := by
  classical
  have hA : A ≠ singleton r := by
    intro he
    have : a = r := by simpa [he] using ha
    exact har this
  simp only [choice, singleton_inj, har, hA, or_self]
  exact singleton_union_of_mem A a ha

/-- Three distinct owners express neutral set union. -/
theorem three_owner_union (r s t : Role) (hrs : r ≠ s) (hrt : r ≠ t)
    (hst : s ≠ t) : choice t (choice r A B) (choice s A B) = union A B := by
  classical
  by_cases hr : A = singleton r ∨ B = singleton r
  · by_cases hs : A = singleton s ∨ B = singleton s
    · rcases hr with ha | hb <;> rcases hs with hc | hd
      · exact False.elim (hrs (singleton_inj.mp (ha.symm.trans hc)))
      · rw [ha, hd]
        simp [choice, hrs, Ne.symm hrs, hrt, hst]
      · rw [hc, hb]
        simpa [choice, hrs, Ne.symm hrs, hrt, hst] using
          (union_comm (singleton r) (singleton s))
      · exact False.elim (hrs (singleton_inj.mp (hb.symm.trans hd)))
    · have hm : r ∈ (union A B).val := by
        rcases hr with ha | hb
        · exact Or.inl (by simp [ha])
        · exact Or.inr (by simp [hb])
      rw [show choice r A B = singleton r by simp [choice, hr]]
      rw [show choice s A B = union A B by simp [choice, hs]]
      exact choice_singleton_of_mem (union A B) t r hrt hm
  · by_cases hs : A = singleton s ∨ B = singleton s
    · have hm : s ∈ (union A B).val := by
        rcases hs with ha | hb
        · exact Or.inl (by simp [ha])
        · exact Or.inr (by simp [hb])
      rw [show choice r A B = union A B by simp [choice, hr]]
      rw [show choice s A B = singleton s by simp [choice, hs], choice_comm]
      exact choice_singleton_of_mem (union A B) t s hst hm
    · rw [show choice r A B = union A B by simp [choice, hr],
        show choice s A B = union A B by simp [choice, hs]]
      exact choice_self (union A B) t

theorem eq_pair_of_ambiguous_subset (A : WinnerSet Role) (a b : Role)
    (hA : Ambiguous A) (hsub : A.val ⊆ {a, b}) : A.val = {a, b} := by
  have ha : a ∈ A.val := by
    apply Classical.byContradiction
    intro ha
    apply hA b
    apply WinnerSet.eq_singleton_of_subset
    intro x hx
    rcases Set.mem_insert_iff.mp (hsub hx) with h | h
    · exact False.elim (ha (h ▸ hx))
    · exact h
  have hb : b ∈ A.val := by
    apply Classical.byContradiction
    intro hb
    apply hA a
    apply WinnerSet.eq_singleton_of_subset
    intro x hx
    rcases Set.mem_insert_iff.mp (hsub hx) with h | h
    · exact h
    · exact False.elim (hb (Set.mem_singleton_iff.mp h ▸ hx))
  exact Set.Subset.antisymm hsub (Set.pair_subset_iff.mpr ⟨ha, hb⟩)


end WinnerSet

namespace Term

variable {Role : Type u} {Var : Type v} {Var' : Type w}

/-- Evaluation commutes with substitution in every full-signature context. -/
theorem eval_subst (t : Term Role Var) (replacement : Var → Term Role Var')
    (valuation : Var' → WinnerSet Role) :
    (t.subst replacement).eval valuation = t.eval (fun x => (replacement x).eval valuation) := by
  induction t with
  | winner => rfl
  | var => rfl
  | choice r s t hs ht => simp only [subst, eval, hs, ht]
  | rename p t ht => simp only [subst, eval, ht]

end Term

end KFOL
