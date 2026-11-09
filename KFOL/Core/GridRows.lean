module

public import KFOL.Core.GridData
public import KFOL.Core.Protected

/-! # The source table's row profiles and protected paths -/

@[expose] public section

namespace KFOL.Core.Grid

universe u

open FirstOrder

variable {Role : Type u} [DecidableEq Role]

attribute [local instance] Equational.coreStructure Native.structureOf structureOf

@[simp] theorem none_mem_fBlock {r s : ℕ} (i : Fin r) :
    (none : Option (Variable r s)) ∉ fBlock i := by simp [fBlock]
@[simp] theorem none_mem_gBlock {r s : ℕ} (j : Fin s) :
    (none : Option (Variable r s)) ∉ gBlock j := by simp [gBlock]
@[simp] theorem cell_mem_fBlock {r s : ℕ} (i k : Fin r) (j : Fin s) :
    some (cell i j) ∈ fBlock k ↔ i = k := by simp [fBlock, cell, row, eq_comm]
@[simp] theorem row_mem_fBlock {r s : ℕ} (i k : Fin r) :
    some (row (s := s) i) ∈ fBlock k ↔ i = k := by simp [fBlock, cell, row]
@[simp] theorem col_mem_fBlock {r s : ℕ} (i : Fin r) (j : Fin s) :
    some (col j) ∉ fBlock i := by simp [fBlock, cell, row, col]
@[simp] theorem cell_mem_gBlock {r s : ℕ} (i : Fin r) (j l : Fin s) :
    some (cell i j) ∈ gBlock l ↔ j = l := by simp [gBlock, cell, col, eq_comm]
@[simp] theorem col_mem_gBlock {r s : ℕ} (j l : Fin s) :
    some (col (r := r) j) ∈ gBlock l ↔ j = l := by simp [gBlock, cell, col]
@[simp] theorem row_mem_gBlock {r s : ℕ} (i : Fin r) (j : Fin s) :
    some (row i) ∉ gBlock j := by simp [gBlock, cell, row, col]

@[simp] theorem fMarker_mem_fBlock {r s : ℕ} (i : Fin r) (a : Option (Fin s)) :
    some (fMarker i a) ∈ fBlock i := by cases a <;> simp [fMarker]
@[simp] theorem gMarker_mem_gBlock {r s : ℕ} (j : Fin s) (a : Option (Fin r)) :
    some (gMarker j a) ∈ gBlock j := by cases a <;> simp [gMarker]

theorem exists_fMarker {r s : ℕ} (i : Fin r) (v : Option (Variable r s))
    (hv : v ∈ fBlock i) : ∃ a, v = some (fMarker i a) := by
  rcases Finset.mem_insert.mp hv with h | h
  · exact ⟨none, h⟩
  · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp h
    exact ⟨some j, rfl⟩
theorem exists_gMarker {r s : ℕ} (j : Fin s) (v : Option (Variable r s))
    (hv : v ∈ gBlock j) : ∃ a, v = some (gMarker j a) := by
  rcases Finset.mem_insert.mp hv with h | h
  · exact ⟨none, h⟩
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
    exact ⟨some i, rfl⟩

theorem fBlocks_disjoint {r s : ℕ} {i k : Fin r} (hik : i ≠ k)
    {v : Option (Variable r s)} (hi : v ∈ fBlock i) : v ∉ fBlock k := by
  obtain ⟨a, rfl⟩ := exists_fMarker i v hi
  cases a <;> simpa [fMarker] using hik

theorem gBlocks_disjoint {r s : ℕ} {j l : Fin s} (hjl : j ≠ l)
    {v : Option (Variable r s)} (hj : v ∈ gBlock j) : v ∉ gBlock l := by
  obtain ⟨a, rfl⟩ := exists_gMarker j v hj
  cases a <;> simpa [gMarker] using hjl

omit [DecidableEq Role] in
/-- The alpha inputs of every F-row are exactly its alpha block. -/
theorem fRow_atom {r s : ℕ} (three : Fin 3 ↪ Role)
    (p : {p : Fin r × Fin r // p.1 ≠ p.2}) (a : Option (Fin s))
    (v : Option (Variable r s)) :
    rawValue three (.inl (p, a)) v = Native.atom (three 0) ↔ v ∈ fBlock p.val.2 := by
  have h20 := three.injective.ne (show (2 : Fin 3) ≠ 0 by decide)
  have hmarker := fBlocks_disjoint p.property (fMarker_mem_fBlock p.val.1 a)
  cases v with
  | none => simp [rawValue]
  | some v =>
    simp only [rawValue]
    split_ifs with he hm hg
    · have he := Option.some.inj he
      subst v
      simp_all
    · simp_all
    · simp_all
    · simp_all

omit [DecidableEq Role] in
/-- The beta inputs of every G-row are exactly its beta block. -/
theorem gRow_atom {r s : ℕ} (three : Fin 3 ↪ Role)
    (p : {p : Fin s × Fin s // p.1 ≠ p.2}) (a : Option (Fin r))
    (v : Option (Variable r s)) :
    rawValue three (.inr (.inl (p, a))) v = Native.atom (three 1) ↔ v ∈ gBlock p.val.2 := by
  have h21 := three.injective.ne (show (2 : Fin 3) ≠ 1 by decide)
  have hmarker := gBlocks_disjoint p.property (gMarker_mem_gBlock p.val.1 a)
  cases v with
  | none => simp [rawValue]
  | some v =>
    simp only [rawValue]
    split_ifs with he hm hg
    · have he := Option.some.inj he
      subst v
      simp_all
    · simp_all
    · simp_all
    · simp_all

/-- Coordinate evaluation of terms over the actual source generators. -/
theorem realize_apply {r s : ℕ} (three : Fin 3 ↪ Role)
    (t : Equational.Term (Equational.CoreSymbol Role) (Option (Variable r s)))
    (c : Coordinate r s) :
    ((t.realize (source three)) c).val = t.realize (rawValue three c) := by
  induction t using induction_choice with
  | var => rfl
  | choice owner a b ha hb => simp only [realize_choice, operation_apply, ha, hb]; rfl

/-- Every member of the generated source algebra has a term over exactly
its declared source columns, including the lower column. -/
theorem exists_source_term {r s : ℕ} (three : Fin 3 ↪ Role)
    (x : span (r := r) (s := s) three) :
    ∃ t : Equational.Term (Equational.CoreSymbol Role) (Option (Variable r s)),
      t.realize (source three) = x.val := by
  refine Language.Substructure.closure_induction
    (p := fun y => ∃ t : Equational.Term (Equational.CoreSymbol Role) (Option (Variable r s)),
      t.realize (source three) = y) x.property ?_ ?_
  · intro y hy
    obtain ⟨v, rfl⟩ := hy
    exact ⟨.var v, rfl⟩
  · intro n f args ih
    cases f with
    | choice owner =>
      obtain ⟨a, ha⟩ := ih 0
      obtain ⟨b, hb⟩ := ih 1
      refine ⟨choiceTerm owner a b, ?_⟩
      rw [realize_choice, ha, hb, funMap_choice owner args]

end KFOL.Core.Grid
