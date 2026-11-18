module

public import KFOL.Definitions.CoreFunctions
public import KFOL.Definitions.ProfileBounds
public import Mathlib.Data.Finset.Lattice.Fold

/-! # Expressions composed of greatest singleton-profile completions

A gate has positive finite arity. Its singleton outputs are specified by
admissible Boolean profiles, and every ambiguous output takes the union of
all its inputs. Binary unions are free when counting layers of these gates.
-/

@[expose] public section
namespace KFOL.Core.CompletionDepth
universe u v

/-- A greatest profile completion on all of its input ports. A gate acting on
a smaller support uses just those ports. -/
structure Gate (Role : Type u) (n : ℕ) where
  eval : (Fin (n + 1) → WinnerSet Role) → WinnerSet Role
  profiles : Role → (Fin (n + 1) → Bool) → Bool
  admissible : AdmissibleProfiles profiles
  singleton_iff : ∀ values r, eval values = WinnerSet.singleton r ↔
    profiles r (ProfileBounds.atomicBits r values) = true
  union_of_ambiguous : ∀ values, (eval values).Ambiguous →
    (eval values).val = ⋃ j, (values j).val

/-- A composition tree with arbitrary finite completion gates and free unions. -/
inductive Expr (Role : Type u) (Var : Type v) where
  | var (j : Var)
  | union (left right : Expr Role Var)
  | gate {n : ℕ} (g : Gate Role n) (args : Fin (n + 1) → Expr Role Var)

namespace Expr
variable {Role : Type u} {Var : Type v}

/-- Evaluate all the inputs of a gate at the same valuation. -/
def eval : Expr Role Var → (Var → WinnerSet Role) → WinnerSet Role
  | .var j, v => v j
  | .union left right, v => (left.eval v).union (right.eval v)
  | .gate g args, v => g.eval fun j => (args j).eval v

/-- The maximum number of completion gates along any root-to-leaf path. -/
def depth : Expr Role Var → ℕ
  | .var _ => 0
  | .union left right => max left.depth right.depth
  | .gate _ args => (Finset.univ.sup fun j => (args j).depth) + 1

end Expr

/-- A requirement on the induced winner operation is feasible at depth at
most d. It may specify a positive source probe and omissions at other probes. -/
def FeasibleAtDepth {Role : Type u} {Var : Type v} (d : ℕ)
    (P : ((Var → WinnerSet Role) → WinnerSet Role) → Prop) : Prop :=
  ∃ e : Expr Role Var, e.depth ≤ d ∧ P e.eval


/-- A constant cofactor has a fixed singleton status. A live cofactor
has a residual expression and a mask of singleton statuses it preserves. -/
inductive Residual (Role : Type u) (Var : Type v) where
  | dead (atom : Option Role)
  | live (expr : Expr Role Var) (mask : Role → Bool)

namespace Residual
variable {Role : Type u} {Var : Type v}

def depth : Residual Role Var → ℕ
  | .dead _ => 0
  | .live e _ => e.depth

/-- The residual retains only winners of the original operation. Every
winner it omits belongs to a fixed input. The mask records exactly which
of its singleton outputs are also singleton outputs of the original. -/
def Represents (B : Set Role) (f : (Var → WinnerSet Role) → WinnerSet Role) :
    Residual Role Var → Prop
  | .dead a => ∃ c : WinnerSet Role, c.val ⊆ B ∧
      (∀ r, c = WinnerSet.singleton r ↔ a = some r) ∧ ∀ v, f v = c
  | .live e M => ∀ v, (e.eval v).val ⊆ (f v).val ∧
      (f v).val ⊆ (e.eval v).val ∪ B ∧
      ∀ r, f v = WinnerSet.singleton r ↔ M r = true ∧ e.eval v = WinnerSet.singleton r

end Residual

/-- The fresh input takes precedence at either designated singleton. At all
other menus, its winners are added to the original output. -/
noncomputable def suspension {Role : Type u} {Var : Type v} (b c : Role) (f : (Var → WinnerSet Role) → WinnerSet Role)
    (values : Var ⊕ Unit → WinnerSet Role) : WinnerSet Role := by
  classical
  let y := values (.inr ())
  exact if y = WinnerSet.singleton b ∨ y = WinnerSet.singleton c then y
    else (f (fun j => values (.inl j))).union y

end KFOL.Core.CompletionDepth
