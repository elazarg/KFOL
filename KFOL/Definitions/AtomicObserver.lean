module

public import KFOL.Definitions.Public
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Logic.Relation

/-! # Atomic observer tables and their canonical directed graph

An interval L ⊆ U records c at L, a at U \ L, and b elsewhere.
Zero observations add reversed interval edges to the inclusion order.
-/

@[expose] public section
namespace KFOL.Core.AtomicObserver

universe u v
variable {Role : Type u} {Var : Type v}

/-- The atomic input represented by a pair of endpoint sets. -/
noncomputable def values (three : Fin 3 ↪ Role) (L U : Finset Var) :
    Var → WinnerSet Role := by
  classical
  exact fun j => WinnerSet.singleton
    (if j ∈ L then three 2 else if j ∈ U then three 0 else three 1)

/-- Inclusion edges, together with reversed zero intervals. -/
def Edge (h : Finset Var → Finset Var → Prop) (S T : Finset Var) : Prop :=
  S ⊆ T ∨ (T ⊆ S ∧ ¬h T S)

/-- Reachability in the graph determined by the table itself. -/
def Reach (h : Finset Var → Finset Var → Prop) : Finset Var → Finset Var → Prop :=
  Relation.ReflTransGen (Edge h)

/-- Unanimity and separation of every positive interval by the canonical graph. -/
def Admissible [Fintype Var] (h : Finset Var → Finset Var → Prop) : Prop :=
  h ∅ Finset.univ ∧ ∀ L U, L ⊆ U → h L U → ¬Reach h U L

end KFOL.Core.AtomicObserver
