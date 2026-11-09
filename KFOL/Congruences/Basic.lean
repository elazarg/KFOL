module

public import KFOL.Definitions.Congruences
public import KFOL.Algebra.Views
public import Mathlib.Order.Preorder.Finite

/-! # Congruence compatibility, atomic collapse and finite class maxima -/

@[expose] public section

namespace KFOL.WinnerSet

universe u

variable {Role : Type u}

@[simp] theorem full_val [Nonempty Role] : (full (Role := Role)).val = Set.univ := rfl

theorem le_full [Nonempty Role] (A : WinnerSet Role) : A ≤ full := Set.subset_univ _

namespace Congruence

@[ext] theorem ext {θ η : Congruence Role} (h : ∀ A B, θ.r A B ↔ η.r A B) : θ = η := by
  have hs : θ.toSetoid = η.toSetoid := Setoid.ext h
  cases θ
  cases η
  cases hs
  rfl

theorem refl (θ : Congruence Role) (A : WinnerSet Role) : θ.r A A := θ.iseqv.refl A
theorem symm (θ : Congruence Role) {A B : WinnerSet Role} (h : θ.r A B) : θ.r B A := θ.iseqv.symm h
theorem trans (θ : Congruence Role) {A B C : WinnerSet Role} (h : θ.r A B) (h' : θ.r B C) :
    θ.r A C := θ.iseqv.trans h h'

/-- Derived union preserves every congruence in exactly the original
owned-choice signature. -/
theorem union (θ : Congruence Role) (three : Fin 3 ↪ Role) {A B C D : WinnerSet Role}
    (hAC : θ.r A C) (hBD : θ.r B D) : θ.r (A.union B) (C.union D) := by
  have h := θ.choice (three 2) (θ.choice (three 0) hAC hBD) (θ.choice (three 1) hAC hBD)
  rw [three_owner_union _ _ _ _ _ (three.injective.ne (by decide))
    (three.injective.ne (by decide)) (three.injective.ne (by decide)),
    three_owner_union _ _ _ _ _ (three.injective.ne (by decide))
    (three.injective.ne (by decide)) (three.injective.ne (by decide))] at h
  exact h

/-- Identifying a singleton with a different value forces its collapse to
the full winner set. This is a congruence law, not an assumed closure rule. -/
theorem atom_collapse_to_full [Nonempty Role] (θ : Congruence Role) (three : Fin 3 ↪ Role)
    (owner : Role) (A : WinnerSet Role) (hA : A ≠ singleton owner) (h : θ.r (singleton owner) A) :
    θ.r (singleton owner) full := by
  classical
  obtain ⟨other,hother,_⟩ := exists_role_outside_pair three owner owner
  have hfull : full (Role := Role) ≠ singleton owner := by
    intro he
    have hm : other ∈ (full (Role := Role)).val := trivial
    rw [he] at hm
    exact hother hm
  have hh := θ.choice owner h (θ.refl full)
  have hl : WinnerSet.choice owner (singleton owner) full = singleton owner := by simp [WinnerSet.choice]
  have hr : WinnerSet.choice owner A full = full := by
    simp only [WinnerSet.choice, ite_eq_right (not_or.mpr ⟨hA,hfull⟩)]
    apply Subtype.ext
    exact Set.union_univ _
  rw [hl,hr] at hh
  exact hh

/-- Finiteness and union compatibility give every congruence class an
actual greatest member belonging to that class. -/
theorem exists_classMaximum [Finite Role] (θ : Congruence Role) (three : Fin 3 ↪ Role)
    (A : WinnerSet Role) : ∃ B, θ.r A B ∧ ∀ C, θ.r A C → C ≤ B := by
  have : Finite (WinnerSet Role) := inferInstance
  obtain ⟨B,hB,hmax⟩ := (Set.toFinite {B | θ.r A B}).exists_maximal ⟨A,θ.refl A⟩
  refine ⟨B,hB,?_⟩
  intro C hC
  have hBU : θ.r B (B.union C) := by
    have hBC : θ.r B C := θ.trans (θ.symm hB) hC
    have hh := θ.union three (θ.refl B) hBC
    simpa only [union_self] using hh
  have hAU : θ.r A (B.union C) := θ.trans hB hBU
  have hUB : B.union C ≤ B := hmax hAU Set.subset_union_left
  exact Set.Subset.trans Set.subset_union_right hUB

end Congruence

end KFOL.WinnerSet
