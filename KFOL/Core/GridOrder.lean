module

public import KFOL.Core.GridIdeal

/-! # The lower tuple, reflection, and its ideal in the generated grid -/

@[expose] public section

namespace KFOL.Core.Grid

universe u

open FirstOrder

variable {Role : Type u} [DecidableEq Role]

attribute [local instance] Native.structureOf Equational.coreStructure structureOf

/-- The all-lower tuple is one of the declared source generators. -/
def lower {r s : ℕ} (three : Fin 3 ↪ Role) : span (r := r) (s := s) three :=
  ⟨source three none, Language.Substructure.subset_closure ⟨none, rfl⟩⟩

@[simp] theorem lower_apply {r s : ℕ} (three : Fin 3 ↪ Role) (c : Coordinate r s) :
    ((lower three).val c).val = Native.lower := rfl

@[simp] theorem span_operation_apply {r s : ℕ} (three : Fin 3 ↪ Role) (owner : Role)
    (x y : span (r := r) (s := s) three) (c : Coordinate r s) :
    ((Core.operation owner x y).val c).val = Native.choice owner (x.val c).val (y.val c).val := rfl

theorem span_join_apply {r s : ℕ} (three : Fin 3 ↪ Role)
    (x y : span (r := r) (s := s) three) (c : Coordinate r s) :
    ((Core.join three x y).val c).val = Native.join (x.val c).val (y.val c).val := by
  exact join_apply three x.val y.val c

/-- The derived join order sees precisely the occurrence of upper markers. -/
theorem below_lower_iff {r s : ℕ} (three : Fin 3 ↪ Role)
    (x : span (r := r) (s := s) three) :
    Core.join three x (lower three) = lower three ↔
      ∀ c : Coordinate r s, (x.val c).val ≠ Native.upper := by
  have hn (v : Native Role) : Native.join v Native.lower = Native.lower ↔ v ≠ Native.upper := by
    cases v <;> simp [Native.join]
  constructor
  · intro h c
    have he := congrArg (fun y : span three => (y.val c).val) h
    rw [span_join_apply, lower_apply] at he
    exact (hn _).mp he
  · intro h
    apply Subtype.ext
    funext c
    apply Subtype.ext
    rw [span_join_apply, lower_apply]
    exact (hn _).mpr (h c)

/-- Reflection follows in every coordinate: lower operated with upper
is always upper, for every role including roles outside the three chosen ones. -/
theorem lower_reflecting {r s : ℕ} (three : Fin 3 ↪ Role) (owner : Role)
    (x : span (r := r) (s := s) three)
    (hx : Core.join three (Core.operation owner (lower three) x) (lower three) = lower three) :
    Core.join three x (lower three) = lower three := by
  apply (below_lower_iff three x).mpr
  have hh := (below_lower_iff three _).mp hx
  intro c hc
  apply hh c
  rw [span_operation_apply, lower_apply, hc]
  exact (Native.choice_eq_upper owner _ _).mpr ⟨Or.inr rfl, by simp, by simp⟩

/-- Every actual element of the lower ideal has one of the three explicit
coordinate patterns. This uses the full generated subalgebra, not a finite
term sample or an assumed certificate of closure. -/
theorem lower_ideal_pattern {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role)
    (x : span (r := r) (s := s) three)
    (hx : Core.join three x (lower three) = lower three) :
    ∃ kind : Option Bool, ∀ c : Coordinate r s, (x.val c).val = pattern three kind c := by
  obtain ⟨t,ht⟩ := exists_source_term three x
  have hu := (below_lower_iff three x).mp hx
  have hterm (c : Coordinate r s) : t.realize (rawValue three c) = (x.val c).val := by
    rw [← realize_apply, ht]
  obtain ⟨kind,hkind⟩ := pattern_of_no_upper hr hs three t (fun c => by rw [hterm]; exact hu c)
  exact ⟨kind, fun c => (hterm c).symm.trans (hkind c)⟩

end KFOL.Core.Grid
