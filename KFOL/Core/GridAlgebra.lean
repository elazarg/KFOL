module

public import KFOL.Core.GridPatterns

/-! # The complete finite three-element lower ideal of the grid algebra -/

@[expose] public section

namespace KFOL.Core.Grid

universe u

open FirstOrder

variable {Role : Type u} [DecidableEq Role]

attribute [local instance] Native.structureOf Equational.coreStructure structureOf

/-- Evaluate a core term at the declared columns, retaining its proof of
membership in the generated source algebra. -/
def value {r s : ℕ} (three : Fin 3 ↪ Role)
    (t : Equational.Term (Equational.CoreSymbol Role) (Option (Variable r s))) : span (r := r) (s := s) three :=
  ⟨t.realize (source three), t.realize_mem _ (fun v => Language.Substructure.subset_closure ⟨v,rfl⟩)⟩

@[simp] theorem value_apply {r s : ℕ} (three : Fin 3 ↪ Role)
    (t : Equational.Term (Equational.CoreSymbol Role) (Option (Variable r s))) (c : Coordinate r s) :
    ((value three t).val c).val = t.realize (rawValue three c) := realize_apply three t c

def T {r s : ℕ} (hr : 2 ≤ r) (three : Fin 3 ↪ Role) : span (r := r) (s := s) three :=
  value three (tTerm three ⟨0,by omega⟩)

def S {r s : ℕ} (hs : 2 ≤ s) (three : Fin 3 ↪ Role) : span (r := r) (s := s) three :=
  value three (sTerm three ⟨0,by omega⟩)

@[simp] theorem T_apply {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role)
    (c : Coordinate r s) : ((T hr three).val c).val = pattern three (some false) c :=
  (value_apply three _ c).trans (tTerm_pattern hr hs three _ c)

@[simp] theorem S_apply {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role)
    (c : Coordinate r s) : ((S hs three).val c).val = pattern three (some true) c :=
  (value_apply three _ c).trans (sTerm_pattern hr hs three _ c)

theorem T_ne_lower {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role) :
    T (s := s) hr three ≠ lower three := by
  let i : Fin r := ⟨0,by omega⟩
  let p : {p : Fin r × Fin r // p.1 ≠ p.2} := ⟨(i,other hr i),Ne.symm (other_ne hr i)⟩
  intro h
  have he := congrArg (fun x : span three => (x.val (.inl (p,none))).val) h
  simp only [T_apply hr hs, lower_apply, pattern] at he
  cases he

theorem S_ne_lower {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role) :
    S (r := r) hs three ≠ lower three := by
  let j : Fin s := ⟨0,by omega⟩
  let p : {p : Fin s × Fin s // p.1 ≠ p.2} := ⟨(j,other hs j),Ne.symm (other_ne hs j)⟩
  intro h
  have he := congrArg (fun x : span three => (x.val (.inr (.inl (p,none)))).val) h
  simp only [S_apply hr hs, lower_apply, pattern] at he
  cases he

/-- The grid's lower ideal consists of exactly these three actual elements. -/
theorem lower_ideal_exact {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role)
    (x : span (r := r) (s := s) three) :
    Core.join three x (lower three) = lower three ↔
      x = T hr three ∨ x = S hs three ∨ x = lower three := by
  constructor
  · intro hx
    obtain ⟨kind,hkind⟩ := lower_ideal_pattern hr hs three x hx
    cases kind with
    | none =>
      refine Or.inr (Or.inr ?_)
      apply Subtype.ext
      funext c
      apply Subtype.ext
      exact (hkind c).trans rfl
    | some b => cases b with
      | false =>
        refine Or.inl ?_
        apply Subtype.ext
        funext c
        apply Subtype.ext
        exact (hkind c).trans (T_apply hr hs three c).symm
      | true =>
        refine Or.inr (Or.inl ?_)
        apply Subtype.ext
        funext c
        apply Subtype.ext
        exact (hkind c).trans (S_apply hr hs three c).symm
  · rintro (rfl | rfl | rfl)
    all_goals apply (below_lower_iff three _).mpr
    · intro c
      rw [T_apply hr hs]
      rcases c with _ | (_ | _) <;> simp [pattern]
    · intro c
      rw [S_apply hr hs]
      rcases c with _ | (_ | _) <;> simp [pattern]
    · intro c; simp

/-- These are the exact typed products needed by the upper-clone cover. -/
theorem lower_operation_T {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role)
    (owner : Role) :
    Core.operation owner (lower three) (T (s := s) hr three) =
      if owner = three 0 then T hr three else lower three := by
  apply Subtype.ext
  funext c
  apply Subtype.ext
  simp only [span_operation_apply, lower_apply, T_apply hr hs]
  by_cases ho : owner = three 0
  · subst owner
    rw [ite_eq_left rfl, T_apply hr hs]
    rcases c with _ | (_ | _) <;> simp [pattern, Native.choice, Native.join]
  · rw [ite_eq_right ho, lower_apply]
    rcases c with _ | (_ | _) <;> simp [pattern, Native.choice, Native.join, Ne.symm ho]

theorem lower_operation_S {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role)
    (owner : Role) :
    Core.operation owner (lower three) (S (r := r) hs three) =
      if owner = three 1 then S hs three else lower three := by
  apply Subtype.ext
  funext c
  apply Subtype.ext
  simp only [span_operation_apply, lower_apply, S_apply hr hs]
  by_cases ho : owner = three 1
  · subst owner
    rw [ite_eq_left rfl, S_apply hr hs]
    rcases c with _ | (_ | _) <;> simp [pattern, Native.choice, Native.join]
  · rw [ite_eq_right ho, lower_apply]
    rcases c with _ | (_ | _) <;> simp [pattern, Native.choice, Native.join, Ne.symm ho]

theorem T_join_S {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role) :
    Core.join three (T hr three) (S hs three) = lower three := by
  apply Subtype.ext
  funext c
  apply Subtype.ext
  rw [span_join_apply, T_apply hr hs, S_apply hr hs, lower_apply]
  rcases c with _ | (_ | _) <;> simp [pattern, Native.join]

theorem T_ne_S {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role) :
    T hr three ≠ S hs three := by
  intro h
  have he := T_join_S hr hs three
  rw [← h, join_idem (span_inVariety three)] at he
  exact T_ne_lower hr hs three he

end KFOL.Core.Grid
