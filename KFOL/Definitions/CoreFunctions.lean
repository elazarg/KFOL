module

public import KFOL.Definitions.CoreBasis
public import KFOL.Definitions.FiniteHorn
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset

/-! # Intrinsic singleton profiles and finite atomic-cut recognition

The predicates below are specified independently of terms. A Boolean input
marks the variables assigned one owner's singleton. The atomic-cut system
uses bound vectors, input columns, and finite Horn rules, independently of
term realization.
-/

@[expose] public section

namespace KFOL.Core

universe u v

/-- Monotonicity, unanimity, and a common variable in every selection of
winning coalitions, one per owner. No term representation is assumed. -/
structure AdmissibleProfiles {Role : Type u} {Var : Type v}
    (F : Role → (Var → Bool) → Bool) : Prop where
  mono : ∀ r v w, (∀ x, v x = true → w x = true) → F r v = true → F r w = true
  top : ∀ r, F r (fun _ => true) = true
  common_source : ∀ v : Role → Var → Bool,
    (∀ r, F r (v r) = true) → ∃ x, ∀ r, v r x = true

namespace Cuts

/-- At a row, retain its requested bound, allow every role, or require one atom. -/
inductive Bound (Role : Type u) where
  | target
  | top
  | atom (r : Role)
  deriving DecidableEq, Fintype

/-- A bound at every sampled valuation. -/
abbrev State (Role : Type u) (Row : Type v) := Row → Bound Role

/-- Inspect a bound without referring to a term or a realization. -/
def region {Role : Type u} {Row : Type v} (U : Row → WinnerSet Role)
    (B : State Role Row) (i : Row) : Set Role :=
  match B i with
  | .target => (U i).val
  | .top => Set.univ
  | .atom r => {r}

/-- The three permitted ways to bound the children of an owned root. -/
def Cut {Role : Type u} {Row : Type v} (U : Row → WinnerSet Role) (r : Role)
    (B L R : State Role Row) : Prop :=
  ∀ i, (L i = B i ∧ R i = B i) ∨
    (r ∈ region U B i ∧ L i = .atom r ∧ R i = .top) ∨
    (r ∈ region U B i ∧ L i = .top ∧ R i = .atom r)

/-- A possible winner of an owned choice between two atomic inputs. -/
def AtomStep {Role : Type u} (owner a b c : Role) : Prop :=
  ((a = owner ∨ b = owner) ∧ c = owner) ∨
    (a ≠ owner ∧ b ≠ owner ∧ (c = a ∨ c = b))

/-- A bounded operation can retain a designated winner at a designated row. -/
structure Fact (Role : Type u) (Row : Type v) where
  bounds : State Role Row
  row : Row
  winner : Role

/-- Coordinate representation used only for finite enumeration of facts. -/
def Fact.equivProd {Role : Type u} {Row : Type v} :
    Fact Role Row ≃ State Role Row × Row × Role where
  toFun f := (f.bounds, f.row, f.winner)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance {Role : Type u} {Row : Type v} [Fintype Role] [Fintype Row] :
    Fintype (Fact Role Row) := by
  classical
  exact Fintype.ofEquiv _ Fact.equivProd.symm

/-- The finite Horn system determined by the input columns and requested
regions. Its seeds and rules contain no term syntax or evaluator. -/
def system {Role : Type u} {Row : Type v} {Var : Type*}
    (values : Row → Var → WinnerSet Role) (U : Row → WinnerSet Role) :
    FiniteHorn.System (Fact Role Row) where
  seed f := ∃ x, (∀ i, (values i x).val ⊆ region U f.bounds i) ∧
    f.winner ∈ (values f.row x).val
  rule p q f := p.row = f.row ∧ q.row = f.row ∧
    ∃ owner, Cut U owner f.bounds p.bounds q.bounds ∧
      AtomStep owner p.winner q.winner f.winner

/-- The table is recognized when every requested membership has been derived
at its target bound after the specified finite number of rounds. -/
noncomputable def Recognizes {Role : Type u} {Row : Type v} {Var : Type*}
    [Fintype Role] [Fintype Row] (values : Row → Var → WinnerSet Role)
    (U : Row → WinnerSet Role) : Prop :=
  ∀ i r, r ∈ (U i).val →
    (⟨fun _ => .target, i, r⟩ : Fact Role Row) ∈ FiniteHorn.saturate (system values U)

end Cuts

/-- Apply the cut criterion to the entire table of an operation. -/
noncomputable def CutRecognizes {Role : Type u} {Var : Type v}
    [Fintype Role] [Fintype Var] (f : (Var → WinnerSet Role) → WinnerSet Role) : Prop := by
  classical
  letI := Fintype.ofFinite (WinnerSet Role)
  exact Cuts.Recognizes (fun valuation x => valuation x) f

end KFOL.Core
