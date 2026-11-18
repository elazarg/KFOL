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

end KFOL.Core.CompletionDepth
