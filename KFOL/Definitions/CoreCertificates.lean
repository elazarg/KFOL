module

public import KFOL.Definitions.Public
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Basic

/-! # Finite owner-elimination certificates

Clauses have at most one positive membership premise. A certificate is a
finite family of clauses together with an order for each owner. The Boolean
checks below refer only to that family, its clauses and their membership
atoms; their soundness is proved separately in `Core.OwnerElimination`.
-/

@[expose] public section

namespace KFOL.Core.OwnerElimination

universe u v
abbrev Atom (Row : Type u) (Role : Type v) := Row × Role

structure Clause (Row : Type u) (Role : Type v) where
  premise : Option (Atom Row Role)
  head : Finset (Atom Row Role)
  deriving DecidableEq

variable {Row : Type u} {Role : Type v}

namespace Clause

def Premise (C : Clause Row Role) (x : Row → WinnerSet Role) : Prop :=
  match C.premise with
  | none => True
  | some p => p.2 ∈ (x p.1).val

def Head (C : Clause Row Role) (x : Row → WinnerSet Role) : Prop :=
  ∃ p ∈ C.head, p.2 ∈ (x p.1).val

def Holds (C : Clause Row Role) (x : Row → WinnerSet Role) : Prop :=
  C.Premise x → C.Head x

/-- Clause truth on a raw tuple of sets, allowing empty coordinates. -/
def HoldsSets (C : Clause Row Role) (x : Row → Set Role) : Prop :=
  (match C.premise with
    | none => True
    | some p => p.2 ∈ x p.1) → ∃ p ∈ C.head, p.2 ∈ x p.1

def Subsumes (D C : Clause Row Role) : Prop :=
  (D.premise = none ∨ D.premise = C.premise) ∧ D.head ⊆ C.head

variable [DecidableEq Row] [DecidableEq Role]

instance (D C : Clause Row Role) : Decidable (D.Subsumes C) := by
  unfold Subsumes
  infer_instance

def tautology (C : Clause Row Role) : Bool :=
  match C.premise with
  | none => false
  | some p => decide (p ∈ C.head)

end Clause

variable [DecidableEq Row] [DecidableEq Role]

def supports (F : Finset (Clause Row Role)) (C : Clause Row Role) : Bool :=
  C.tautology || decide (∃ D ∈ F, D.Subsumes C)

def Satisfies (F : Finset (Clause Row Role)) (x : Row → WinnerSet Role) : Prop :=
  ∀ C ∈ F, C.Holds x

/-- Every clause in the family holds on the raw set tuple. -/
def SatisfiesSets (F : Finset (Clause Row Role)) (x : Row → Set Role) : Prop :=
  ∀ C ∈ F, C.HoldsSets x

def Absent (S : Finset (Atom Row Role)) (x : Row → WinnerSet Role) : Prop :=
  ∀ p ∈ S, p.2 ∉ (x p.1).val

/-- Closure under owned choice applied independently in every row. -/
def ChoiceClosed (R : (Row → WinnerSet Role) → Prop) : Prop :=
  ∀ r x y, R x → R y → R (fun i => WinnerSet.choice r (x i) (y i))

variable [Fintype Role]

def initial (C : Clause Row Role) (r : Role) : Finset (Atom Row Role) :=
  C.head.filter (fun p => p.2 = r)

def offOwner (i : Row) (r : Role) : Finset (Atom Row Role) :=
  (Finset.univ.erase r).image (fun s => (i, s))

def blockHead (S : Finset (Atom Row Role)) (i : Row) (r : Role) : Finset (Atom Row Role) :=
  S ∪ offOwner i r

def checkBlocker (F : Finset (Clause Row Role)) (C : Clause Row Role)
    (r : Role) (S : Finset (Atom Row Role)) (i : Row) : Bool :=
  match C.premise with
  | none => supports F ⟨none, blockHead S i r⟩
  | some p => if p.2 = r then supports F ⟨none, blockHead S i r⟩
    else decide (∀ s ∈ Finset.univ.erase r,
      supports F ⟨some (p.1, s), blockHead S i r⟩ = true)

def checkSteps (F : Finset (Clause Row Role)) (C : Clause Row Role)
    (r : Role) (S : Finset (Atom Row Role)) : List (Atom Row Role) → Bool
  | [] => supports F ⟨C.premise, S⟩
  | i :: rest => decide (i ∈ C.head ∧ i ∉ S ∧ i.2 ≠ r) &&
      checkBlocker F C r S i.1 && checkSteps F C r (insert i S) rest

def checkFamily (F : Finset (Clause Row Role))
    (orders : Clause Row Role → Role → List (Atom Row Role)) : Bool :=
  decide (∀ C ∈ F, ∀ r : Role, checkSteps F C r (initial C r) (orders C r) = true)

/-- A finite family proves the clause by owner-elimination orders and holds
on every supplied input column. Auxiliary clauses are allowed. -/
def Certifies {Var : Type*} (columns : Var → Row → WinnerSet Role)
    (C : Clause Row Role) : Prop :=
  ∃ (F : Finset (Clause Row Role))
    (orders : Clause Row Role → Role → List (Atom Row Role)),
    C ∈ F ∧ checkFamily F orders = true ∧ ∀ j, Satisfies F (columns j)

end KFOL.Core.OwnerElimination
