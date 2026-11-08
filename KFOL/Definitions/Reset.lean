module

public import KFOL.Definitions.Equational

/-! # Reset values, signature, selection and canonical guard tables

Reset uses the shared nonempty winner-set carrier and mathlib's generic term
syntax. The guard table is the minimal part of a finite structural collection;
validity is still defined independently by algebraic evaluation.
-/

@[expose] public section

namespace KFOL

universe u v w

/-- An atomic right operand discards the left; an ambiguous one keeps both. -/
noncomputable def WinnerSet.reset {Role : Type u} (A B : WinnerSet Role) : WinnerSet Role := by
  classical
  exact if B.Ambiguous then A.union B else B

namespace Reset

/-- Reset is one binary operation, without constants or extra owned operations. -/
inductive Symbol : ℕ → Type
  | reset : Symbol 2

/-- Reset terms reuse the relation-free mathlib term type. -/
abbrev Term (Var : Type v) := Equational.Term Symbol Var

/-- Interpret the single binary symbol by an explicitly supplied operation. -/
@[instance_reducible] def structureOf {M : Type u} (op : M → M → M) :
    (Equational.language Symbol).Structure M where
  funMap f args := match f with
    | .reset => op (args 0) (args 1)
  RelMap r := nomatch r

/-- The fixed separating chain Z={a}, U={a,b}, T={a,b,c}. -/
def chainValue {Role : Type u} (three : Fin 3 ↪ Role) (i : Fin 3) : WinnerSet Role :=
  if i = 0 then WinnerSet.singleton (three 0)
  else if i = 1 then (WinnerSet.singleton (three 0)).union (WinnerSet.singleton (three 1))
  else (WinnerSet.singleton (three 2)).union
    ((WinnerSet.singleton (three 0)).union (WinnerSet.singleton (three 1)))

namespace Term

variable {Var : Type v} {Role : Type u}

/-- Ergonomic binary constructor on the generic syntax. -/
def step (s t : Term Var) : Term Var :=
  .func .reset (fun i => if i = 0 then s else t)

/-- The rightmost variable, independently of evaluation and selection. -/
def root : Term Var → Var
  | .var x => x
  | .func .reset args => root (args 1)

/-- A position is selected according to the ambiguity statuses of inputs. -/
def Selected : Term Var → Set Var → Var → Prop
  | .var i, _, j => j = i
  | .func .reset args, B, j =>
    Selected (args 1) B j ∨ (root (args 1) ∈ B ∧ Selected (args 0) B j)

/-- Evaluation uses mathlib realization with the shared reset operation. -/
noncomputable def eval (t : Term Var) (v : Var → WinnerSet Role) : WinnerSet Role :=
  let _ := structureOf (WinnerSet.reset (Role := Role))
  t.realize v

/-- Raw prerequisites collected from the syntax, before antichain minimization. -/
def guards [DecidableEq Var] : Term Var → Var → Finset (Finset Var)
  | .var i, j => if j = i then {∅} else ∅
  | .func .reset args, j =>
    guards (args 1) j ∪ (guards (args 0) j).image (insert (root (args 1)))

/-- Delete every prerequisite having a strictly smaller prerequisite. -/
def minimize [DecidableEq Var] (G : Finset (Finset Var)) : Finset (Finset Var) :=
  G.filter (fun A => ∀ B ∈ G, B ⊆ A → A ⊆ B)

/-- The canonical table for one output position. Unused positions have no guards. -/
def table [DecidableEq Var] (t : Term Var) (j : Var) : Finset (Finset Var) :=
  minimize (t.guards j)

/-- Finite guard composition: outer prerequisites refer to inner roots; inner
prerequisites supply the final output position. Minimize after taking unions. -/
def composedGuards {Var' : Type w} [DecidableEq Var] [DecidableEq Var']
    (t : Term Var) (s : Var → Term Var') (j : Var') : Finset (Finset Var') :=
  t.varFinset.biUnion (fun i => (t.table i).biUnion (fun A =>
    ((s i).table j).image (fun C => A.image (fun k => (s k).root) ∪ C)))

end Term
end Reset
end KFOL
