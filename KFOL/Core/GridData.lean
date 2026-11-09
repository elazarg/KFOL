module

public import KFOL.Core.TypedCover
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Pi

/-! # The explicit finite padded-rectangle source algebra -/

@[expose] public section

namespace KFOL.Core.Grid

universe u

open FirstOrder

variable {Role : Type u} [DecidableEq Role]

attribute [local instance] Equational.coreStructure Native.structureOf

/-- Cells, private row variables and private column variables. -/
abbrev Variable (r s : ℕ) := (Fin r × Fin s) ⊕ (Fin r ⊕ Fin s)

def cell {r s : ℕ} (i : Fin r) (j : Fin s) : Variable r s := .inl (i, j)
def row {r s : ℕ} (i : Fin r) : Variable r s := .inr (.inl i)
def col {r s : ℕ} (j : Fin s) : Variable r s := .inr (.inr j)

def fBlock {r s : ℕ} (i : Fin r) : Finset (Option (Variable r s)) :=
  insert (some (row i)) (Finset.univ.image (fun j => some (cell i j)))

def gBlock {r s : ℕ} (j : Fin s) : Finset (Option (Variable r s)) :=
  insert (some (col j)) (Finset.univ.image (fun i => some (cell i j)))

/-- Ordered unequal blocks, with one selected marker variable in the first. -/
abbrev FRow (r s : ℕ) := {p : Fin r × Fin r // p.1 ≠ p.2} × Option (Fin s)
abbrev GRow (r s : ℕ) := {p : Fin s × Fin s // p.1 ≠ p.2} × Option (Fin r)
abbrev Coordinate (r s : ℕ) := FRow r s ⊕ (GRow r s ⊕ (Fin r × Fin s))

def fMarker {r s : ℕ} (i : Fin r) : Option (Fin s) → Variable r s
  | none => row i
  | some j => cell i j

def gMarker {r s : ℕ} (j : Fin s) : Option (Fin r) → Variable r s
  | none => col j
  | some i => cell i j

/-- One row of the paper's explicit native table. `none` is the separately
adjoined lower-marker generator e and has the lower value in every row. -/
def rawValue {r s : ℕ} (three : Fin 3 ↪ Role) (c : Coordinate r s)
    (v : Option (Variable r s)) : Native Role :=
  match v with
  | none => .lower
  | some _ => match c with
    | .inl (p, a) =>
      if v = some (fMarker p.val.1 a) then .upper
      else if v ∈ fBlock p.val.2 then .atom (three 0)
      else if (match a with | none => false | some j => decide (v = some (col j))) then .atom (three 2)
      else .lower
    | .inr (.inl (p, a)) =>
      if v = some (gMarker p.val.1 a) then .upper
      else if v ∈ gBlock p.val.2 then .atom (three 1)
      else if (match a with | none => false | some i => decide (v = some (row i))) then .atom (three 2)
      else .lower
    | .inr (.inr (i, j)) =>
      if v = some (cell i j) then .upper
      else if v = some (row i) ∨ v = some (col j) then .atom (three 2)
      else .lower

/-- Each coordinate omits an actual role atom, ensuring proper native
factors. The source never uses a full native counteralgebra as a factor. -/
def missing {r s : ℕ} (three : Fin 3 ↪ Role) : Coordinate r s → Role
  | .inl _ => three 1
  | .inr _ => three 0

omit [DecidableEq Role] in
theorem rawValue_ne_missing {r s : ℕ} (three : Fin 3 ↪ Role) (c : Coordinate r s)
    (v : Option (Variable r s)) : rawValue three c v ≠ Native.atom (missing three c) := by
  have h01 := three.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have h20 := three.injective.ne (show (2 : Fin 3) ≠ 0 by decide)
  have h21 := three.injective.ne (show (2 : Fin 3) ≠ 1 by decide)
  cases v with
  | none => simp [rawValue]
  | some v =>
    rcases c with ⟨p, a⟩ | (⟨p, a⟩ | ⟨i, j⟩)
    all_goals simp only [rawValue, missing]
    all_goals split_ifs <;> simp_all

abbrev Factor {r s : ℕ} (three : Fin 3 ↪ Role) (c : Coordinate r s) :=
  Native.omission (some (missing three c))

abbrev Carrier (r s : ℕ) (three : Fin 3 ↪ Role) := ∀ c : Coordinate r s, Factor three c

@[instance_reducible] def structureOf {r s : ℕ} (three : Fin 3 ↪ Role) :
    (Equational.language (Equational.CoreSymbol Role)).Structure (Carrier r s three) :=
  Equational.productStructure (fun c : Coordinate r s => Factor three c)

attribute [local instance] structureOf

/-- The actual source columns, including the constant lower tuple. -/
def source {r s : ℕ} (three : Fin 3 ↪ Role) (v : Option (Variable r s)) : Carrier r s three :=
  fun c => ⟨rawValue three c v, rawValue_ne_missing three c v⟩

def span {r s : ℕ} (three : Fin 3 ↪ Role) :
    (Equational.language (Equational.CoreSymbol Role)).Substructure (Carrier r s three) :=
  Language.Substructure.closure _ (Set.range (source (r := r) (s := s) three))

instance span_nonempty {r s : ℕ} (three : Fin 3 ↪ Role) : Nonempty (span (r := r) (s := s) three) :=
  ⟨⟨source three none, Language.Substructure.subset_closure ⟨none, rfl⟩⟩⟩

/-- Finiteness follows from finite proper factors and finite coordinates,
without enumerating generated closures or term functions. -/
instance span_finite [Finite Role] {r s : ℕ} (three : Fin 3 ↪ Role) :
    Finite (span (r := r) (s := s) three) := by
  have : Finite (Native Role) := Finite.of_equiv (Option (Option Role)) Native.equivOption.symm
  infer_instance

theorem span_inVariety {r s : ℕ} (three : Fin 3 ↪ Role) :
    Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) (span (r := r) (s := s) three) := by
  have hp := Equational.InVariety.product
    (σ := Equational.CoreSymbol Role) (fun c : Coordinate r s => Factor three c)
    (fun c => Native.omission_inVariety three (some (missing three c)))
  exact hp.substructure (span three)

@[simp] theorem operation_apply {r s : ℕ} (three : Fin 3 ↪ Role) (owner : Role)
    (x y : Carrier r s three) (c : Coordinate r s) :
    (Core.operation owner x y c).val = Native.choice owner (x c).val (y c).val := rfl

theorem join_apply {r s : ℕ} (three : Fin 3 ↪ Role) (x y : Carrier r s three) (c : Coordinate r s) :
    (Core.join three x y c).val = Native.join (x c).val (y c).val := by
  simp only [Core.join, operation_apply]
  exact Native.three_choice_join _ _ _ (three.injective.ne (by decide))
    (three.injective.ne (by decide)) (three.injective.ne (by decide)) _ _

end KFOL.Core.Grid
