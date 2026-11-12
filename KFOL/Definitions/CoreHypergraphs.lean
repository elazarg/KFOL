module

public import KFOL.Definitions.CoreCertificates
public import Mathlib.Data.Fintype.Powerset

/-! # Closed colored-hypergraph schemas

The vertices are row/owner pairs. Each optional premise indexes a clutter
of clause heads. Admissibility consists of boundary incidences and a closed
cut condition, with no orders, generated relation, or term quantifier.
-/

@[expose] public section
namespace KFOL.Core.Hypergraphs
open OwnerElimination
universe u v
variable (Row : Type u) (Role : Type v)

structure Diagram where
  heads : Option (Atom Row Role) → Finset (Finset (Atom Row Role))
  antichain : ∀ p H, H ∈ heads p → ∀ J, J ∈ heads p → H ⊆ J → H = J

variable {Row Role}

/-- A head is supported precisely when it contains an edge of its clutter. -/
def Diagram.Supports (D : Diagram Row Role) (p : Option (Atom Row Role))
    (S : Finset (Atom Row Role)) : Prop := ∃ H ∈ D.heads p, H ⊆ S

/-- The clauses encoded by the indexed clutters, on possibly empty row sets. -/
def Diagram.Models (D : Diagram Row Role) (x : Row → Set Role) : Prop :=
  ∀ p H, H ∈ D.heads p → (Clause.mk p H).HoldsSets x

variable [DecidableEq Row] [DecidableEq Role] [Fintype Role]

/-- Row nonemptiness, pure-clause weakening, and tautological implications. -/
def Diagram.Boundary (D : Diagram Row Role) : Prop :=
  (∀ i, D.Supports none (Finset.univ.image (fun r : Role => (i,r)))) ∧
  (∀ p S, D.Supports none S → D.Supports (some p) S) ∧
  (∀ p S, p ∈ S → D.Supports (some p) S)

/-- The literal incidence conditions that exclude an owner singleton. -/
def Diagram.Blocker (D : Diagram Row Role) (p : Option (Atom Row Role))
    (r : Role) (S : Finset (Atom Row Role)) (i : Row) : Prop :=
  match p with
  | none => D.Supports none (blockHead S i r)
  | some a => if a.2 = r then D.Supports none (blockHead S i r)
    else ∀ s, s ≠ r → D.Supports (some (a.1,s)) (blockHead S i r)

/-- Every proper owner-initial cut exposes a head vertex with supported blockers. -/
def Diagram.NoTrap (D : Diagram Row Role) : Prop :=
  ∀ p H, H ∈ D.heads p → ∀ r S,
    H.filter (fun a => a.2 = r) ⊆ S → S ⊂ H →
      ∃ a ∈ H, a ∉ S ∧ D.Blocker p r S a.1

/-- Two closed set conditions specifying the complete relation schema. -/
def Diagram.Admissible (D : Diagram Row Role) : Prop := D.Boundary ∧ D.NoTrap

end KFOL.Core.Hypergraphs
