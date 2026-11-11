module

public import KFOL.Algebra.Basic
public import Mathlib.Data.Finset.Basic

/-! # Finite status models for named owned choices

Replacing passive markers by nonempty sets preserves union. It also preserves
an owned choice when the named absorbing atom has exactly one marker preimage.
A computable nonempty-finset model connects finite status certificates to the
independent winner-set semantics.
-/

@[expose] public section

open KFOL

namespace KFOL.WinnerSet.StatusModel

variable {Marker Role : Type*}

noncomputable def expand (seed : Marker → WinnerSet Role) (A : WinnerSet Marker) :
    WinnerSet Role :=
  ⟨{k | ∃ x ∈ A.val, k ∈ (seed x).val}, by
    obtain ⟨x, hx⟩ := A.property
    obtain ⟨k, hk⟩ := (seed x).property
    exact ⟨k, x, hx, hk⟩⟩

@[simp] theorem expand_singleton (seed : Marker → WinnerSet Role) (x : Marker) :
    expand seed (singleton x) = seed x := by
  apply Subtype.ext
  ext k
  simp [expand, val_singleton]

@[simp] theorem expand_union (seed : Marker → WinnerSet Role) (A B : WinnerSet Marker) :
    expand seed (A.union B) = (expand seed A).union (expand seed B) := by
  apply Subtype.ext
  ext k
  simp only [expand, val_union, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨x, hx | hx, hk⟩
    · exact Or.inl ⟨x, hx, hk⟩
    · exact Or.inr ⟨x, hx, hk⟩
  · rintro (⟨x, hx, hk⟩ | ⟨x, hx, hk⟩)
    · exact ⟨x, Or.inl hx, hk⟩
    · exact ⟨x, Or.inr hx, hk⟩

theorem expand_eq_singleton_iff (seed : Marker → WinnerSet Role) (r : Marker) (k : Role)
    (h : ∀ x, seed x = singleton k ↔ x = r) (A : WinnerSet Marker) :
    expand seed A = singleton k ↔ A = singleton r := by
  constructor
  · intro he
    have only (x : Marker) (hx : x ∈ A.val) : x = r := by
      apply (h x).mp
      apply eq_singleton_of_subset
      intro y hy
      have hh : y ∈ (expand seed A).val := ⟨x, hx, hy⟩
      simpa [he] using hh
    apply Subtype.ext
    ext x
    constructor
    · exact only x
    · intro hx
      have hxr : x = r := hx
      obtain ⟨y, hy⟩ := A.property
      have hyr := only y hy
      simpa [hxr, hyr] using hy
  · rintro rfl
    simpa using (h r).mpr rfl

theorem expand_choice (seed : Marker → WinnerSet Role) (r : Marker) (k : Role)
    (h : ∀ x, seed x = singleton k ↔ x = r) (A B : WinnerSet Marker) :
    expand seed (choice r A B) = choice k (expand seed A) (expand seed B) := by
  classical
  have ha := expand_eq_singleton_iff seed r k h A
  have hb := expand_eq_singleton_iff seed r k h B
  have hr : seed r = singleton k := (h r).mpr rfl
  by_cases hab : A = singleton r ∨ B = singleton r
  · have hh : expand seed A = singleton k ∨ expand seed B = singleton k := by
      simpa only [ha, hb] using hab
    simp only [choice, hab, hh, ite_true, expand_singleton, hr]
  · have hh : ¬(expand seed A = singleton k ∨ expand seed B = singleton k) := by
      simpa only [ha, hb] using hab
    simp only [choice, hab, hh, ite_false, expand_union]

end KFOL.WinnerSet.StatusModel

namespace KFOL.WinnerSet.StatusModel

abbrev Value (α : Type*) := {A : Finset α // A.Nonempty}

namespace Value

variable {α : Type*} [DecidableEq α]

def singleton (r : α) : Value α := ⟨{r}, Finset.singleton_nonempty r⟩

def union (A B : Value α) : Value α :=
  ⟨A.val ∪ B.val, A.property.mono Finset.subset_union_left⟩

def choice (r : α) (A B : Value α) : Value α :=
  if A = singleton r ∨ B = singleton r then singleton r else union A B

def toWinner (A : Value α) : WinnerSet α := ⟨A.val, by simpa using A.property⟩

omit [DecidableEq α] in
theorem toWinner_injective : Function.Injective (toWinner (α := α)) := by
  intro A B h
  apply Subtype.ext
  exact Finset.coe_injective (congrArg Subtype.val h)

omit [DecidableEq α] in
@[simp] theorem toWinner_singleton (r : α) :
    toWinner (singleton r) = WinnerSet.singleton r := by
  apply Subtype.ext
  simp [toWinner, singleton, val_singleton]

@[simp] theorem toWinner_union (A B : Value α) :
    toWinner (union A B) = (toWinner A).union (toWinner B) := by
  apply Subtype.ext
  simp [toWinner, union, val_union]

@[simp] theorem toWinner_choice (r : α) (A B : Value α) :
    toWinner (choice r A B) = WinnerSet.choice r (toWinner A) (toWinner B) := by
  classical
  have ha : toWinner A = WinnerSet.singleton r ↔ A = singleton r := by
    rw [← toWinner_singleton]
    exact toWinner_injective.eq_iff
  have hb : toWinner B = WinnerSet.singleton r ↔ B = singleton r := by
    rw [← toWinner_singleton]
    exact toWinner_injective.eq_iff
  by_cases hab : A = singleton r ∨ B = singleton r
  · simp only [choice, WinnerSet.choice, ha, hb, hab, ite_true, toWinner_singleton]
  · simp only [choice, WinnerSet.choice, ha, hb, hab, ite_false, toWinner_union]

end Value

end KFOL.WinnerSet.StatusModel
