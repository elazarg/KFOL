module

public import KFOL.Core.GridAlgebra

/-! # Boolean block maps on arbitrary elements of the generated grid -/

@[expose] public section

namespace KFOL.Core.Grid

universe u

variable {Role : Type u} [DecidableEq Role]

attribute [local instance] Native.structureOf Equational.coreStructure structureOf

/-- A representative F-row with its atomic block at the given index. -/
def alphaCoordinate {r s : ℕ} (hr : 2 ≤ r) (i : Fin r) : Coordinate r s :=
  .inl (⟨(other hr i,i),other_ne hr i⟩,none)
def betaCoordinate {r s : ℕ} (hs : 2 ≤ s) (j : Fin s) : Coordinate r s :=
  .inr (.inl (⟨(other hs j,j),other_ne hs j⟩,none))

/-- The alpha-block and beta-block bits of arbitrary generated elements. -/
def A {r s : ℕ} (hr : 2 ≤ r) (three : Fin 3 ↪ Role) (i : Fin r)
    (x : span (r := r) (s := s) three) : Bool :=
  decide ((x.val (alphaCoordinate hr i)).val = Native.atom (three 0))
def B {r s : ℕ} (hs : 2 ≤ s) (three : Fin 3 ↪ Role) (j : Fin s)
    (x : span (r := r) (s := s) three) : Bool :=
  decide ((x.val (betaCoordinate hs j)).val = Native.atom (three 1))

theorem A_value {r s : ℕ} (hr : 2 ≤ r) (three : Fin 3 ↪ Role) (i : Fin r)
    (t : Equational.Term (Equational.CoreSymbol Role) (Option (Variable r s))) :
    A hr three i (value three t) = profile (three 0) (fProfile i) t := by
  apply Bool.eq_iff_iff.mpr
  simp only [A, decide_eq_true_eq, value_apply, realize_eq_atom_iff_profile]
  have hv : (fun x => decide (rawValue three (alphaCoordinate hr i) x = Native.atom (three 0))) =
      fProfile (s := s) i := by
    funext x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      apply decide_eq_true
      exact (fRow_atom three ⟨(other hr i,i),other_ne hr i⟩ none x).mp (of_decide_eq_true hx)
    · intro hx
      apply decide_eq_true
      exact (fRow_atom three ⟨(other hr i,i),other_ne hr i⟩ none x).mpr (of_decide_eq_true hx)
  rw [hv]

theorem B_value {r s : ℕ} (hs : 2 ≤ s) (three : Fin 3 ↪ Role) (j : Fin s)
    (t : Equational.Term (Equational.CoreSymbol Role) (Option (Variable r s))) :
    B hs three j (value three t) = profile (three 1) (gProfile j) t := by
  apply Bool.eq_iff_iff.mpr
  simp only [B, decide_eq_true_eq, value_apply, realize_eq_atom_iff_profile]
  have hv : (fun x => decide (rawValue three (betaCoordinate hs j) x = Native.atom (three 1))) =
      gProfile (r := r) j := by
    funext x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      apply decide_eq_true
      exact (gRow_atom three ⟨(other hs j,j),other_ne hs j⟩ none x).mp (of_decide_eq_true hx)
    · intro hx
      apply decide_eq_true
      exact (gRow_atom three ⟨(other hs j,j),other_ne hs j⟩ none x).mpr (of_decide_eq_true hx)
  rw [hv]

@[simp] theorem A_operation {r s : ℕ} (hr : 2 ≤ r) (three : Fin 3 ↪ Role) (i : Fin r)
    (owner : Role) (x y : span (r := r) (s := s) three) :
    A hr three i (Core.operation owner x y) =
      if owner = three 0 then A hr three i x || A hr three i y else A hr three i x && A hr three i y := by
  apply Bool.eq_iff_iff.mpr
  simp only [A, decide_eq_true_eq, span_operation_apply, Native.choice_eq_atom]
  split <;> simp_all

@[simp] theorem B_operation {r s : ℕ} (hs : 2 ≤ s) (three : Fin 3 ↪ Role) (j : Fin s)
    (owner : Role) (x y : span (r := r) (s := s) three) :
    B hs three j (Core.operation owner x y) =
      if owner = three 1 then B hs three j x || B hs three j y else B hs three j x && B hs three j y := by
  apply Bool.eq_iff_iff.mpr
  simp only [B, decide_eq_true_eq, span_operation_apply, Native.choice_eq_atom]
  split <;> simp_all

@[simp] theorem A_lower {r s : ℕ} (hr : 2 ≤ r) (three : Fin 3 ↪ Role) (i : Fin r) :
    A (s := s) hr three i (lower three) = false := by simp [A]
@[simp] theorem B_lower {r s : ℕ} (hs : 2 ≤ s) (three : Fin 3 ↪ Role) (j : Fin s) :
    B (r := r) hs three j (lower three) = false := by simp [B]
@[simp] theorem A_T {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role) (i : Fin r) :
    A hr three i (T (s := s) hr three) = true := by simp [A, T_apply hr hs, alphaCoordinate, pattern]
@[simp] theorem B_T {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role) (j : Fin s) :
    B hs three j (T hr three) = false := by simp [B, T_apply hr hs, betaCoordinate, pattern]
@[simp] theorem A_S {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role) (i : Fin r) :
    A hr three i (S hs three) = false := by simp [A, S_apply hr hs, alphaCoordinate, pattern]
@[simp] theorem B_S {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role) (j : Fin s) :
    B hs three j (S (r := r) hs three) = true := by simp [B, S_apply hr hs, betaCoordinate, pattern]

/-- Annotation coordinates contain only lower, upper and the third atom,
for arbitrary elements of the generated algebra. -/
theorem annotation_no_other_atom {r s : ℕ} (three : Fin 3 ↪ Role)
    (x : span (r := r) (s := s) three) (i : Fin r) (j : Fin s)
    (owner : Role) (ho : owner ≠ three 2) :
    (x.val (.inr (.inr (i,j)))).val ≠ Native.atom owner := by
  obtain ⟨t,ht⟩ := exists_source_term three x
  have hv : (value three t) = x := Subtype.ext ht
  rw [← hv, value_apply]
  exact no_atom_of_valuation owner _ (fun v => raw_annotation_no_other_atom three i j v owner ho) t

/-- Crossing block bits force the marker at their annotation coordinate,
even when the element is a complicated term in the original generators. -/
theorem annotation_upper_of_AB {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role)
    (x : span (r := r) (s := s) three) (i : Fin r) (j : Fin s)
    (hA : A hr three i x = true) (hB : B hs three j x = true) :
    (x.val (.inr (.inr (i,j)))).val = Native.upper := by
  obtain ⟨t,ht⟩ := exists_source_term three x
  have hv : (value three t) = x := Subtype.ext ht
  rw [← hv, A_value] at hA
  rw [← hv, B_value] at hB
  rw [← hv, value_apply]
  exact upper_of_crossing three t i j hA hB

omit [DecidableEq Role] in
theorem raw_annotation_no_gamma_on_foreign_fBlock {r s : ℕ} (three : Fin 3 ↪ Role)
    (k i : Fin r) (hki : k ≠ i) (j : Fin s) (v : Option (Variable r s)) (hv : v ∈ fBlock k) :
    rawValue three (.inr (.inr (i,j))) v ≠ Native.atom (three 2) := by
  obtain ⟨a,rfl⟩ := exists_fMarker k v hv
  cases a <;> simp [rawValue, fMarker, row, col, cell, hki]

omit [DecidableEq Role] in
theorem raw_annotation_no_gamma_on_foreign_gBlock {r s : ℕ} (three : Fin 3 ↪ Role)
    (l j : Fin s) (hlj : l ≠ j) (i : Fin r) (v : Option (Variable r s)) (hv : v ∈ gBlock l) :
    rawValue three (.inr (.inr (i,j))) v ≠ Native.atom (three 2) := by
  obtain ⟨a,rfl⟩ := exists_gMarker l v hv
  cases a <;> simp [rawValue, gMarker, row, col, cell, hlj]

/-- A foreign alpha block rules out gamma at the chosen annotation row. -/
theorem annotation_no_gamma_of_A {r s : ℕ} (hr : 2 ≤ r) (three : Fin 3 ↪ Role)
    (x : span (r := r) (s := s) three) (k i : Fin r) (hki : k ≠ i) (j : Fin s)
    (hA : A hr three k x = true) :
    (x.val (.inr (.inr (i,j)))).val ≠ Native.atom (three 2) := by
  obtain ⟨t,ht⟩ := exists_source_term three x
  have hv : (value three t) = x := Subtype.ext ht
  rw [← hv, A_value] at hA
  rw [← hv, value_apply]
  exact no_atom_of_positive_profile (three 0) (three 2) (three.injective.ne (by decide))
    (fProfile k) _ (fun v hv => raw_annotation_no_gamma_on_foreign_fBlock three k i hki j v
      (of_decide_eq_true hv)) t hA

theorem annotation_no_gamma_of_B {r s : ℕ} (hs : 2 ≤ s) (three : Fin 3 ↪ Role)
    (x : span (r := r) (s := s) three) (l j : Fin s) (hlj : l ≠ j) (i : Fin r)
    (hB : B hs three l x = true) :
    (x.val (.inr (.inr (i,j)))).val ≠ Native.atom (three 2) := by
  obtain ⟨t,ht⟩ := exists_source_term three x
  have hv : (value three t) = x := Subtype.ext ht
  rw [← hv, B_value] at hB
  rw [← hv, value_apply]
  exact no_atom_of_positive_profile (three 1) (three 2) (three.injective.ne (by decide))
    (gProfile l) _ (fun v hv => raw_annotation_no_gamma_on_foreign_gBlock three l j hlj i v
      (of_decide_eq_true hv)) t hB

end KFOL.Core.Grid
