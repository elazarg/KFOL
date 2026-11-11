module

public import KFOL.Definitions.CoreCrown
public import KFOL.Algebra.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate

/-! # Disjoint cyclic exceptional regions -/

@[expose] public section
namespace KFOL.Core.Crown
open WinnerSet
universe u v
variable {Role : Type u} {Var : Type v}

theorem cylinder_unique_c {b c : Role} (hbc : b ≠ c) {next : Equiv.Perm Var}
    {i : Var} {values : Var → WinnerSet Role} (h : Cylinder b c next i values)
    {j : Var} (hj : values j = singleton c) : j = i := by
  classical
  by_contra hji
  by_cases hjn : j = next i
  · exact h.2.2.1 (hjn ▸ hj)
  · have he := h.2.2.2 j hji hjn
    exact hbc (WinnerSet.singleton_inj.mp (he.symm.trans hj))

theorem cylinder_unique {b c : Role} (hbc : b ≠ c) {next : Equiv.Perm Var}
    {i j : Var} {values : Var → WinnerSet Role}
    (hi : Cylinder b c next i values) (hj : Cylinder b c next j values) : i = j :=
  (cylinder_unique_c hbc hi hj.1).symm

/-- All but at most one deletion patch agrees with the common operation. -/
theorem operation_agreement [Nonempty Var] (b c : Role)
    (next : Equiv.Perm Var) (values : Var → WinnerSet Role) :
    ∃ bad : Var, ∀ h : Var, h ≠ bad →
      operation b c next {i | i ≠ h} values = operation b c next Set.univ values := by
  classical
  by_cases hc : ∃ i, Cylinder b c next i values
  · obtain ⟨i, hi⟩ := hc
    refine ⟨i, fun h hhi => ?_⟩
    have hm : ∃ j ∈ {j | j ≠ h}, Cylinder b c next j values := ⟨i, Ne.symm hhi, hi⟩
    have hall : ∃ j ∈ (Set.univ : Set Var), Cylinder b c next j values :=
      ⟨i, Set.mem_univ _, hi⟩
    exact (ite_eq_left hm).trans (ite_eq_left hall).symm
  · refine ⟨Classical.arbitrary Var, fun h _ => ?_⟩
    have hm : ¬∃ i ∈ {i | i ≠ h}, Cylinder b c next i values :=
      fun ⟨i, _, hi⟩ => hc ⟨i, hi⟩
    have hall : ¬∃ i ∈ (Set.univ : Set Var), Cylinder b c next i values :=
      fun ⟨i, _, hi⟩ => hc ⟨i, hi⟩
    exact (ite_eq_right hm).trans (ite_eq_right hall).symm

theorem negative_cylinder (three : Fin 3 ↪ Role) (next : Equiv.Perm Var)
    (i : Var) (hnext : next i ≠ i) :
    Cylinder (three 1) (three 2) next i (negative three next i) := by
  classical
  refine ⟨by simp [negative], ?_, ?_, ?_⟩
  · simp [negative, hnext, singleton_inj]
  · simp [negative, hnext, singleton_inj]
  · intro j hji hjn
    simp [negative, hji, hjn]

theorem operation_negative [Nonempty Var] (three : Fin 3 ↪ Role) (next : Equiv.Perm Var)
    (i : Var) (hnext : next i ≠ i) :
    operation (three 1) (three 2) next Set.univ (negative three next i) =
      (singleton (three 1)).union (singleton (three 2)) := by
  classical
  exact ite_eq_left ⟨i, Set.mem_univ _, negative_cylinder three next i hnext⟩

/-- A cross-edge row is outside every cylinder unless the successor has a
one- or two-cycle at its distinguished input. -/
theorem positive_no_cylinder (three : Fin 3 ↪ Role) (next : Equiv.Perm Var)
    (i : Var) (hnext : next i ≠ i) (htwo : next (next i) ≠ i) :
    ¬∃ j, Cylinder (three 1) (three 2) next j (positive three next i) := by
  classical
  have h01 : three 0 ≠ three 1 := three.injective.ne (by decide)
  have h02 : three 0 ≠ three 2 := three.injective.ne (by decide)
  have h12 : three 1 ≠ three 2 := three.injective.ne (by decide)
  rintro ⟨j, hj⟩
  have he : j = next i := by
    by_cases hji : j = i
    · subst j
      exact (h02 (singleton_inj.mp (by simpa [positive] using hj.1))).elim
    · by_contra hjn
      have hb : positive three next i j = singleton (three 1) := by
        simp [positive, hji, hjn]
      exact h12 (singleton_inj.mp (hb.symm.trans hj.1))
  subst j
  have hne : next (next i) ≠ next i := next.injective.ne hnext
  have hb : positive three next i (next (next i)) = singleton (three 1) := by
    simp [positive, htwo, hne]
  exact hj.2.1 hb

end KFOL.Core.Crown
