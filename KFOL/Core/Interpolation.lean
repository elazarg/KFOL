module

public import KFOL.Algebra.Atomic.CoreSupport
public import KFOL.Algebra.PublicContexts
public import KFOL.Algebra.Monotone
public import KFOL.Algebra.Views
public import Mathlib.Data.Fin.VecNotation

/-! # A compatibility law coupling singleton and ambiguous outputs

The proof uses unary constant-or-extensive contexts to exclude two possible
absorbing atoms, then follows a child that retains the required membership.
No finiteness of the role or variable type is assumed.
-/

@[expose] public section

namespace KFOL.Core

universe u v

open WinnerSet

variable {Role : Type u} {Var : Type v}

namespace Interpolation

private def first (a b : Role) (tag : Var → Fin 3) : Var → WinnerSet Role :=
  fun x => ![(WinnerSet.singleton a).union (WinnerSet.singleton b), WinnerSet.singleton b, WinnerSet.singleton b] (tag x)

private def second (a b c : Role) (tag : Var → Fin 3) : Var → WinnerSet Role :=
  fun x => ![WinnerSet.singleton b, (WinnerSet.singleton b).union (WinnerSet.singleton c),
    (WinnerSet.singleton a).union (WinnerSet.singleton b)] (tag x)

private def third (a b c : Role) (tag : Var → Fin 3) : Var → WinnerSet Role :=
  fun x => ![WinnerSet.singleton a, WinnerSet.singleton b, WinnerSet.singleton c] (tag x)

private theorem mem_second (a b c : Role) (tag : Var → Fin 3) (x : Var) :
    b ∈ (second a b c tag x).val := by
  have hx : tag x = 0 ∨ tag x = 1 ∨ tag x = 2 := by omega
  rcases hx with hx | hx | hx <;> simp [second, hx]

private theorem second_mem (a b c : Role) (tag : Var → Fin 3) (t : Term Role Var)
    (ht : t.IsCore) : b ∈ (t.eval (second a b c tag)).val := by
  have h := t.eval_mono (v := fun _ => WinnerSet.singleton b) (w := second a b c tag)
    (fun x => Set.singleton_subset_iff.mpr (mem_second a b c tag x))
  rw [ht.eval_diagonal] at h
  exact h rfl

private theorem no_first_atom (a b c : Role) (hab : a ≠ b) (hac : a ≠ c)
    (tag : Var → Fin 3) (t : Term Role Var) (ht : t.IsCore)
    (hf : t.eval (first a b tag) = WinnerSet.singleton b) :
    t.eval (third a b c tag) ≠ WinnerSet.singleton a := by
  classical
  intro hg
  let active : Var → Bool := fun x => decide (tag x = 0)
  let fixed : Var → WinnerSet Role := fun _ => WinnerSet.singleton b
  have ha : t.eval (fun x => if active x then WinnerSet.singleton a else fixed x) = WinnerSet.singleton a := by
    apply (ht.isPublic.eval_singleton_iff_of_tests a (third a b c tag) _ ?_).mp hg
    intro x
    have hx : tag x = 0 ∨ tag x = 1 ∨ tag x = 2 := by omega
    rcases hx with hx | hx | hx <;> simp [third, active, fixed, hx, Ne.symm hab, hac.symm]
  have hb : t.eval (fun x => if active x then (WinnerSet.singleton a).union (WinnerSet.singleton b)
      else fixed x) = WinnerSet.singleton b := by
    convert hf using 1
    congr 1
    funext x
    have hx : tag x = 0 ∨ tag x = 1 ∨ tag x = 2 := by omega
    rcases hx with hx | hx | hx <;> simp [first, active, fixed, hx]
  rcases ht.isPublic.unary_constant_or_extensive active fixed with ⟨d, hd⟩ | hd
  · exact hab (singleton_inj.mp (ha.symm.trans ((hd (WinnerSet.singleton a)).trans
      ((hd ((WinnerSet.singleton a).union (WinnerSet.singleton b))).symm.trans hb))))
  · have hm := hd ((WinnerSet.singleton a).union (WinnerSet.singleton b)) (Or.inl rfl)
    rw [hb] at hm
    exact hab hm

private theorem no_third_atom (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (tag : Var → Fin 3) (t : Term Role Var) (ht : t.IsCore)
    (hs : (t.eval (second a b c tag)).val ⊆ {b, c}) :
    t.eval (third a b c tag) ≠ WinnerSet.singleton c := by
  classical
  intro hg
  let active : Var → Bool := fun x => decide (tag x = 2)
  let fixed : Var → WinnerSet Role := second a b c tag
  have hc : t.eval (fun x => if active x then WinnerSet.singleton c else fixed x) = WinnerSet.singleton c := by
    apply (ht.isPublic.eval_singleton_iff_of_tests c (third a b c tag) _ ?_).mp hg
    intro x
    have hx : tag x = 0 ∨ tag x = 1 ∨ tag x = 2 := by omega
    rcases hx with hx | hx | hx <;> simp [third, second, active, fixed, hx, hbc, hac,
      (ambiguous_of_two_mem ((WinnerSet.singleton b).union (WinnerSet.singleton c)) b c hbc
        (Or.inl rfl) (Or.inr rfl)) c]
  have he : (fun x => if active x then (WinnerSet.singleton a).union (WinnerSet.singleton b) else fixed x) =
      second a b c tag := by
    funext x
    have hx : tag x = 0 ∨ tag x = 1 ∨ tag x = 2 := by omega
    rcases hx with hx | hx | hx <;> simp [second, active, fixed, hx]
  rcases ht.isPublic.unary_constant_or_extensive active fixed with ⟨d, hd⟩ | hd
  · have eqc : t.eval (second a b c tag) = WinnerSet.singleton c := by
      rw [← he, hd, ← hd (WinnerSet.singleton c), hc]
    have hm := second_mem a b c tag t ht
    rw [eqc] at hm
    exact hbc hm
  · have hm := hd ((WinnerSet.singleton a).union (WinnerSet.singleton b)) (Or.inl rfl)
    rw [he] at hm
    rcases hs hm with hm | hm
    · exact hab hm
    · exact hac hm

private theorem third_atom_mem (a b c : Role) (tag : Var → Fin 3)
    (t : Term Role Var) (ht : t.IsCore) (r : Role)
    (he : t.eval (third a b c tag) = WinnerSet.singleton r) : r = a ∨ r = b ∨ r = c := by
  classical
  have hs := ht.eval_subset_of_support (third a b c tag) {a, b, c} (by
    intro x _ y hy
    have hx : tag x = 0 ∨ tag x = 1 ∨ tag x = 2 := by omega
    rcases hx with hx | hx | hx <;> simp_all [third])
  have hm := hs (show r ∈ (t.eval (third a b c tag)).val by simp [he])
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hm

private theorem eq_pair (b c : Role) (S : WinnerSet Role) (hb : b ∈ S.val)
    (hs : S.val ⊆ {b, c}) (hn : S ≠ WinnerSet.singleton b) : S = (WinnerSet.singleton b).union (WinnerSet.singleton c) := by
  classical
  have hc : c ∈ S.val := by
    by_contra hc
    apply hn
    apply eq_singleton_of_subset S b
    intro x hx
    rcases hs hx with he | he
    · exact he
    · exact False.elim (hc (he ▸ hx))
  apply Subtype.ext
  exact Set.Subset.antisymm hs (Set.union_subset
    (Set.singleton_subset_iff.mpr hb) (Set.singleton_subset_iff.mpr hc))

private theorem persistence (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (tag : Var → Fin 3) (t : Term Role Var) (ht : t.IsCore) :
    t.eval (first a b tag) = WinnerSet.singleton b →
    t.eval (second a b c tag) = (WinnerSet.singleton b).union (WinnerSet.singleton c) →
    b ∈ (t.eval (third a b c tag)).val := by
  classical
  induction t with
  | winner => exact False.elim ht
  | rename => exact False.elim ht
  | var x =>
    intro hf hs
    have hx : tag x = 0 ∨ tag x = 1 ∨ tag x = 2 := by omega
    rcases hx with hx | hx | hx
    · have hm : a ∈ (WinnerSet.singleton b).val := by
        rw [← hf]; simp [Term.eval, first, hx]
      exact False.elim (hab hm)
    · simp [Term.eval, third, hx]
    · have hm : c ∈ ((WinnerSet.singleton a).union (WinnerSet.singleton b)).val := by
        have hc : c ∈ ((Term.var x : Term Role Var).eval (second a b c tag)).val := by
          rw [hs]; exact Or.inr rfl
        simpa [Term.eval, second, hx] using hc
      exact False.elim (hm.elim (fun h => hac h.symm) (fun h => hbc h.symm))
  | choice r s t ihs iht =>
    intro hf hs
    have hamb : ((WinnerSet.singleton b).union (WinnerSet.singleton c)).Ambiguous :=
      ambiguous_of_two_mem _ b c hbc (Or.inl rfl) (Or.inr rfl)
    have hn : ¬(s.eval (second a b c tag) = WinnerSet.singleton r ∨
        t.eval (second a b c tag) = WinnerSet.singleton r) := by
      intro hh
      apply hamb r
      exact hs.symm.trans ((choice_eq_owner_iff _ _ r).mpr hh)
    have hj : (s.eval (second a b c tag)).union (t.eval (second a b c tag)) =
        (WinnerSet.singleton b).union (WinnerSet.singleton c) := by
      simpa only [Term.eval, choice, ite_eq_right hn] using hs
    have hsB : (s.eval (second a b c tag)).val ⊆ {b, c} := by
      intro x hx
      have hm : x ∈ ((s.eval (second a b c tag)).union
          (t.eval (second a b c tag))).val := Or.inl hx
      simpa only [hj, val_union, val_singleton, Set.mem_union, Set.mem_insert_iff,
        Set.mem_singleton_iff] using hm
    have htB : (t.eval (second a b c tag)).val ⊆ {b, c} := by
      intro x hx
      have hm : x ∈ ((s.eval (second a b c tag)).union
          (t.eval (second a b c tag))).val := Or.inr hx
      simpa only [hj, val_union, val_singleton, Set.mem_union, Set.mem_insert_iff,
        Set.mem_singleton_iff] using hm
    by_cases hrb : r = b
    · subst r
      have hes := eq_pair b c _ (second_mem a b c tag s ht.1) hsB (not_or.mp hn).1
      have het := eq_pair b c _ (second_mem a b c tag t ht.2) htB (not_or.mp hn).2
      rcases (choice_eq_owner_iff _ _ b).mp hf with hsf | htf
      · exact (mem_choice_owner b _ _).mpr (Or.inl (ihs ht.1 hsf hes))
      · exact (mem_choice_owner b _ _).mpr (Or.inr (iht ht.2 htf het))
    · obtain ⟨hsf, htf⟩ := (choice_eq_other_iff _ _ r hrb).mp hf
      have no_atom (u : Term Role Var) (hu : u.IsCore)
          (huf : u.eval (first a b tag) = WinnerSet.singleton b)
          (huB : (u.eval (second a b c tag)).val ⊆ {b, c}) :
          u.eval (third a b c tag) ≠ WinnerSet.singleton r := by
        by_cases hra : r = a
        · subst r; exact no_first_atom a b c hab hac tag u hu huf
        by_cases hrc : r = c
        · subst r; exact no_third_atom a b c hab hac hbc tag u hu huB
        intro he
        rcases third_atom_mem a b c tag u hu r he with ha | hb | hc
        · exact hra ha
        · exact hrb hb
        · exact hrc hc
      have hc : c ∈ ((s.eval (second a b c tag)).union (t.eval (second a b c tag))).val := by
        rw [hj]; exact Or.inr rfl
      have hnC : ¬(s.eval (third a b c tag) = WinnerSet.singleton r ∨
          t.eval (third a b c tag) = WinnerSet.singleton r) :=
        not_or.mpr ⟨no_atom s ht.1 hsf hsB, no_atom t ht.2 htf htB⟩
      change b ∈ (choice r _ _).val
      rw [choice, ite_eq_right hnC]
      rcases hc with hc | hc
      · have hes := eq_pair b c _ (second_mem a b c tag s ht.1) hsB (by
          intro he; rw [he] at hc; exact hbc hc.symm)
        exact Or.inl (ihs ht.1 hsf hes)
      · have het := eq_pair b c _ (second_mem a b c tag t ht.2) htB (by
          intro he; rw [he] at hc; exact hbc hc.symm)
        exact Or.inr (iht ht.2 htf het)

end Interpolation

/-- A mixed singleton/ambiguity interpolation law, uniformly for arbitrary
input partitions and arbitrary role types. Singleton profiles alone do not
express this implication. -/
theorem three_valuation_persistence (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (tag : Var → Fin 3) (t : Term Role Var) (ht : t.IsCore)
    (hf : t.eval (fun x => ![(WinnerSet.singleton a).union (WinnerSet.singleton b), WinnerSet.singleton b,
      WinnerSet.singleton b] (tag x)) = WinnerSet.singleton b)
    (hs : t.eval (fun x => ![WinnerSet.singleton b, (WinnerSet.singleton b).union (WinnerSet.singleton c),
      (WinnerSet.singleton a).union (WinnerSet.singleton b)] (tag x)) = (WinnerSet.singleton b).union (WinnerSet.singleton c)) :
    b ∈ (t.eval (fun x => ![WinnerSet.singleton a, WinnerSet.singleton b, WinnerSet.singleton c] (tag x))).val :=
  Interpolation.persistence a b c hab hac hbc tag t ht hf hs

end KFOL.Core
