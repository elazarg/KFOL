module

public import KFOL.Core.GridAlgebra
public import KFOL.Core.GridCrossing
public import KFOL.Core.UpperClone

/-! # The explicit padded crossing counterexample in the rigid upper clone -/

@[expose] public section

namespace KFOL.Core.Grid

universe u v

open FirstOrder

variable {Role : Type u} [DecidableEq Role]

attribute [local instance] Native.structureOf Equational.coreStructure structureOf

section Congruence

variable {M : Type v} [(Equational.language (Equational.CoreSymbol Role)).Structure M]

omit [DecidableEq Role] in
theorem fTerm_realize_congr {r s : ℕ} (three : Fin 3 ↪ Role) (i : Fin r)
    (v w : Option (Variable r s) → M) (h : ∀ x, v (some x) = w (some x)) :
    (fTerm three i).realize v = (fTerm three i).realize w := by
  apply fold_realize_congr
  · exact h (row i)
  · intro term hmem
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hmem
    exact h (cell i j)

omit [DecidableEq Role] in
theorem gTerm_realize_congr {r s : ℕ} (three : Fin 3 ↪ Role) (j : Fin s)
    (v w : Option (Variable r s) → M) (h : ∀ x, v (some x) = w (some x)) :
    (gTerm three j).realize v = (gTerm three j).realize w := by
  apply fold_realize_congr
  · exact h (col j)
  · intro term hmem
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hmem
    exact h (cell i j)

omit [DecidableEq Role] in
theorem tTerm_realize_congr {r s : ℕ} (three : Fin 3 ↪ Role) (i : Fin r)
    (v w : Option (Variable r s) → M) (h : ∀ x, v (some x) = w (some x)) :
    (tTerm three i).realize v = (tTerm three i).realize w := by
  apply fold_realize_congr
  · exact fTerm_realize_congr three i v w h
  · intro term hmem
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hmem
    exact fTerm_realize_congr three j v w h

omit [DecidableEq Role] in
theorem sTerm_realize_congr {r s : ℕ} (three : Fin 3 ↪ Role) (j : Fin s)
    (v w : Option (Variable r s) → M) (h : ∀ x, v (some x) = w (some x)) :
    (sTerm three j).realize v = (sTerm three j).realize w := by
  apply fold_realize_congr
  · exact gTerm_realize_congr three j v w h
  · intro term hmem
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hmem
    exact gTerm_realize_congr three i v w h

end Congruence

def column {r s : ℕ} (three : Fin 3 ↪ Role) (x : Option (Variable r s)) : span (r := r) (s := s) three :=
  value three (.var x)

theorem realize_columns {r s : ℕ} (three : Fin 3 ↪ Role)
    (t : Equational.Term (Equational.CoreSymbol Role) (Option (Variable r s))) :
    t.realize (column three) = value three t := by
  apply Subtype.ext
  exact (Language.HomClass.realize_term (span three).subtype.toHom).symm

/-- The crossing assignment puts the new clone point at u and retains the
actual source columns at every padded row, column and cell variable. -/
def cloneValuation {r s : ℕ} (three : Fin 3 ↪ Role) :
    Option (Variable r s) → Option (span (r := r) (s := s) three)
  | none => none
  | some x => some (column three (some x))

theorem clone_tTerm {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role) (i : Fin r) :
    letI := upperStructure (Role := Role) (lower (r := r) (s := s) three)
    (tTerm three i).realize (cloneValuation (r := r) (s := s) three) = some (T (s := s) hr three) := by
  let _ := upperStructure (Role := Role) (lower (r := r) (s := s) three)
  rw [tTerm_realize_congr three i (cloneValuation (r := r) (s := s) three) (fun x => some (column three x)) (fun _ => rfl)]
  have he := Language.HomClass.realize_term (upperInclusion (lower (r := r) (s := s) three)) (t := tTerm three i) (v := column (r := r) (s := s) three)
  simp only [Function.comp_def, upperInclusion_apply] at he
  rw [he, realize_columns]
  apply congrArg some
  apply Subtype.ext
  funext c
  apply Subtype.ext
  rw [value_apply, tTerm_pattern hr hs, T_apply hr hs]

theorem clone_sTerm {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role) (j : Fin s) :
    letI := upperStructure (Role := Role) (lower (r := r) (s := s) three)
    (sTerm three j).realize (cloneValuation (r := r) (s := s) three) = some (S (r := r) hs three) := by
  let _ := upperStructure (Role := Role) (lower (r := r) (s := s) three)
  rw [sTerm_realize_congr three j (cloneValuation (r := r) (s := s) three) (fun x => some (column three x)) (fun _ => rfl)]
  have he := Language.HomClass.realize_term (upperInclusion (lower (r := r) (s := s) three)) (t := sTerm three j) (v := column (r := r) (s := s) three)
  simp only [Function.comp_def, upperInclusion_apply] at he
  rw [he, realize_columns]
  apply congrArg some
  apply Subtype.ext
  funext c
  apply Subtype.ext
  rw [value_apply, sTerm_pattern hr hs, S_apply hr hs]

/-- Exact failure of the same derived-join equation that holds in the
full native algebra. The witness uses the actual finite generated grid. -/
theorem crossing_fails {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role)
    (i : Fin r) (j : Fin s) :
    letI := upperStructure (Role := Role) (lower (r := r) (s := s) three)
    (crossingIdentity three i j).1.realize (cloneValuation (r := r) (s := s) three) ≠
      (crossingIdentity three i j).2.realize (cloneValuation (r := r) (s := s) three) := by
  let _ := upperStructure (Role := Role) (lower (r := r) (s := s) three)
  have hT := lower_operation_T hr hs three (three 0)
  have hS := lower_operation_S hr hs three (three 1)
  rw [ite_eq_left rfl] at hT hS
  have heT : upperChoice (lower three) (three 0) (none : Option (span (r := r) (s := s) three)) (some (T hr three)) =
      some (T (s := s) hr three) := by
    simp only [upperChoice, hT, ite_eq_right (T_ne_lower hr hs three)]
  have heS : upperChoice (lower three) (three 1) (none : Option (span (r := r) (s := s) three)) (some (S hs three)) =
      some (S (r := r) hs three) := by
    simp only [upperChoice, hS, ite_eq_right (S_ne_lower hr hs three)]
  simp only [crossingIdentity, realize_union, realize_choice, Language.Term.realize_var,
    cloneValuation, clone_tTerm hr hs, clone_sTerm hr hs]
  simp only [operation_upper, heT, heS]
  rw [upper_join_some, T_join_S hr hs, upper_join_none_lower (span_inVariety three)]
  simp

end KFOL.Core.Grid
