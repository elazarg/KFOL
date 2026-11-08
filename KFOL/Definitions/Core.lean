module

public import KFOL.Definitions.Public
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Data.Fintype.Defs

/-!
# The intrinsic core and permutation elimination

The core is a fragment of the same term syntax and uses the same evaluator.
Input occurrences retain their variable and the accumulated role permutation;
list entries distinguish repeated syntactic occurrences.
-/

@[expose] public section

namespace KFOL.Term

universe u v

variable {Role : Type u} {Var : Type v}

/-- Whether any winner leaf occurs, including below a role switch. -/
def HasWinner : Term Role Var → Prop
  | .winner _ => True
  | .var _ => False
  | .choice _ s t => s.HasWinner ∨ t.HasWinner
  | .rename _ t => t.HasWinner

/-- The input leaves with their accumulated permutations, in traversal order.
Multiplication acts by `(p * q) a = p (q a)`. -/
def inputOccurrences : Term Role Var → List (Var × Equiv.Perm Role)
  | .winner _ => []
  | .var x => [(x, 1)]
  | .choice _ s t => s.inputOccurrences ++ t.inputOccurrences
  | .rename p t => t.inputOccurrences.map (fun (x, q) => (x, p * q))

/-- The constant-free, switch-free owned-choice fragment. -/
def IsCore : Term Role Var → Prop
  | .winner _ => False
  | .var _ => True
  | .choice _ s t => s.IsCore ∧ t.IsCore
  | .rename _ _ => False

/-- Push accumulated permutations to owners, discard them at input leaves,
and remove internal switches. Correctness requires identity accumulated action
at those leaves, as proved in `Algebra/Idempotent.lean`. -/
def pushRenames (p : Equiv.Perm Role) : Term Role Var → Term Role Var
  | .winner r => .winner (p r)
  | .var x => .var x
  | .choice r s t => .choice (p r) (s.pushRenames p) (t.pushRenames p)
  | .rename q t => t.pushRenames (p * q)

/-- Checked extraction for finite role types. A winner leaf or nonidentity
accumulated action at any input returns `none`; successful subtrees are joined
with the transported owner. This checks occurrences without constructing their
list, and uses pointwise finite tests of permutations. -/
def extractCore? [Fintype Role] [DecidableEq Role] (p : Equiv.Perm Role) :
    Term Role Var → Option (Term Role Var)
  | .winner _ => none
  | .var x => if ∀ r, p r = r then some (.var x) else none
  | .choice r s t => match s.extractCore? p, t.extractCore? p with
    | some s', some t' => some (.choice (p r) s' t')
    | _, _ => none
  | .rename q t => t.extractCore? (p * q)

/-- Number of constructor occurrences in the syntax tree. -/
def size : Term Role Var → ℕ
  | .winner _ => 1
  | .var _ => 1
  | .choice _ s t => s.size + t.size + 1
  | .rename _ t => t.size + 1

end KFOL.Term
