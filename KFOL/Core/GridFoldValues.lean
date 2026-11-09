module

public import KFOL.Core.GridTerms
public import KFOL.Core.GridOrder

/-! # Evaluation of the padded folds in the explicit source table -/

@[expose] public section

namespace KFOL.Core.Grid

universe u

variable {Role : Type u} [DecidableEq Role]

attribute [local instance] Native.structureOf

theorem fTerm_upper {r s : ℕ} (three : Fin 3 ↪ Role) (i : Fin r)
    (v : Option (Variable r s) → Native Role) :
    (fTerm three i).realize v = Native.upper ↔
      (∃ x ∈ fBlock i, v x = Native.upper) ∧ ∀ x ∈ fBlock i, v x ≠ Native.atom (three 2) := by
  rw [fTerm, realize_fold_upper]
  simp only [FirstOrder.Language.Term.realize_var, List.forall_mem_map, List.mem_finRange,
    forall_const]
  constructor
  · rintro ⟨hmarker,hrow,hcells⟩
    refine ⟨?_,?_⟩
    · rcases hmarker with h | ⟨term,hmem,h⟩
      · exact ⟨some (row i), by simp, h⟩
      · obtain ⟨j,_,rfl⟩ := List.mem_map.mp hmem
        exact ⟨some (cell i j), by simp, h⟩
    · intro x hx
      obtain ⟨a,rfl⟩ := exists_fMarker i x hx
      cases a with
      | none => exact hrow
      | some j => exact hcells j
  · rintro ⟨⟨x,hx,hmarker⟩,hav⟩
    refine ⟨?_,hav _ (by simp),fun j => hav _ (by simp)⟩
    obtain ⟨a,rfl⟩ := exists_fMarker i x hx
    cases a with
    | none => exact Or.inl hmarker
    | some j => exact Or.inr ⟨.var (some (cell i j)),
        List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩,hmarker⟩

theorem gTerm_upper {r s : ℕ} (three : Fin 3 ↪ Role) (j : Fin s)
    (v : Option (Variable r s) → Native Role) :
    (gTerm three j).realize v = Native.upper ↔
      (∃ x ∈ gBlock j, v x = Native.upper) ∧ ∀ x ∈ gBlock j, v x ≠ Native.atom (three 2) := by
  rw [gTerm, realize_fold_upper]
  simp only [FirstOrder.Language.Term.realize_var, List.forall_mem_map, List.mem_finRange,
    forall_const]
  constructor
  · rintro ⟨hmarker,hcol,hcells⟩
    refine ⟨?_,?_⟩
    · rcases hmarker with h | ⟨term,hmem,h⟩
      · exact ⟨some (col j), by simp, h⟩
      · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hmem
        exact ⟨some (cell i j), by simp, h⟩
    · intro x hx
      obtain ⟨a,rfl⟩ := exists_gMarker j x hx
      cases a with
      | none => exact hcol
      | some i => exact hcells i
  · rintro ⟨⟨x,hx,hmarker⟩,hav⟩
    refine ⟨?_,hav _ (by simp),fun i => hav _ (by simp)⟩
    obtain ⟨a,rfl⟩ := exists_gMarker j x hx
    cases a with
    | none => exact Or.inl hmarker
    | some i => exact Or.inr ⟨.var (some (cell i j)),
        List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩,hmarker⟩

omit [DecidableEq Role] in
theorem raw_gRow_upper {r s : ℕ} (three : Fin 3 ↪ Role)
    (p : {p : Fin s × Fin s // p.1 ≠ p.2}) (a : Option (Fin r))
    (v : Option (Variable r s)) :
    rawValue three (.inr (.inl (p,a))) v = Native.upper ↔ v = some (gMarker p.val.1 a) := by
  cases v with
  | none => simp [rawValue]
  | some v => simp only [rawValue]; split_ifs <;> simp_all

omit [DecidableEq Role] in
theorem raw_fRow_upper {r s : ℕ} (three : Fin 3 ↪ Role)
    (p : {p : Fin r × Fin r // p.1 ≠ p.2}) (a : Option (Fin s))
    (v : Option (Variable r s)) :
    rawValue three (.inl (p,a)) v = Native.upper ↔ v = some (fMarker p.val.1 a) := by
  cases v with
  | none => simp [rawValue]
  | some v => simp only [rawValue]; split_ifs <;> simp_all

omit [DecidableEq Role] in
theorem raw_annotation_upper {r s : ℕ} (three : Fin 3 ↪ Role)
    (i : Fin r) (j : Fin s) (v : Option (Variable r s)) :
    rawValue three (.inr (.inr (i,j))) v = Native.upper ↔ v = some (cell i j) := by
  cases v with
  | none => simp [rawValue]
  | some v => simp only [rawValue]; split_ifs <;> simp_all

/-- The private row variable absorbs every cell marker of a G-row in its
padded h-fold. No such fold can remain upper. -/
theorem fTerm_no_upper_gRow {r s : ℕ} (three : Fin 3 ↪ Role) (i : Fin r)
    (p : {p : Fin s × Fin s // p.1 ≠ p.2}) (a : Option (Fin r)) :
    (fTerm three i).realize (rawValue three (.inr (.inl (p,a)))) ≠ Native.upper := by
  intro he
  obtain ⟨⟨x,hx,hmarker⟩,hav⟩ := (fTerm_upper three i _).mp he
  have hx' := (raw_gRow_upper three p a x).mp hmarker
  subst x
  cases a with
  | none => simp [gMarker] at hx
  | some k =>
    have hk : k = i := by simpa [gMarker] using hx
    subst k
    apply hav (some (row i)) (by simp)
    simp [rawValue, gMarker, row, col, cell, gBlock]

theorem gTerm_no_upper_fRow {r s : ℕ} (three : Fin 3 ↪ Role) (j : Fin s)
    (p : {p : Fin r × Fin r // p.1 ≠ p.2}) (a : Option (Fin s)) :
    (gTerm three j).realize (rawValue three (.inl (p,a))) ≠ Native.upper := by
  intro he
  obtain ⟨⟨x,hx,hmarker⟩,hav⟩ := (gTerm_upper three j _).mp he
  have hx' := (raw_fRow_upper three p a x).mp hmarker
  subst x
  cases a with
  | none => simp [fMarker] at hx
  | some k =>
    have hk : k = j := by simpa [fMarker] using hx
    subst k
    apply hav (some (col j)) (by simp)
    simp [rawValue, fMarker, row, col, cell, fBlock]

theorem fTerm_no_upper_annotation {r s : ℕ} (three : Fin 3 ↪ Role) (k i : Fin r) (j : Fin s) :
    (fTerm three k).realize (rawValue three (.inr (.inr (i,j)))) ≠ Native.upper := by
  intro he
  obtain ⟨⟨x,hx,hmarker⟩,hav⟩ := (fTerm_upper three k _).mp he
  have hx' := (raw_annotation_upper three i j x).mp hmarker
  subst x
  have hik : i = k := by simpa using hx
  subst k
  apply hav (some (row i)) (by simp)
  simp [rawValue, row, col, cell]

theorem gTerm_no_upper_annotation {r s : ℕ} (three : Fin 3 ↪ Role) (l j : Fin s) (i : Fin r) :
    (gTerm three l).realize (rawValue three (.inr (.inr (i,j)))) ≠ Native.upper := by
  intro he
  obtain ⟨⟨x,hx,hmarker⟩,hav⟩ := (gTerm_upper three l _).mp he
  have hx' := (raw_annotation_upper three i j x).mp hmarker
  subst x
  have hjl : j = l := by simpa using hx
  subst l
  apply hav (some (col j)) (by simp)
  simp [rawValue, row, col, cell]

end KFOL.Core.Grid
