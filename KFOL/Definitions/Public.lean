module

public import Mathlib.Data.Set.Image
public import Mathlib.Logic.Equiv.Defs

/-!
# The public owned-choice algebra

The carrier consists of nonempty winner sets. Owned choice absorbs an operand
equal to the owner's singleton and otherwise takes union. Terms allow winner
constants, input variables, owned choices and internal role permutations.

This module defines algebraic evaluation only. Strategies and equilibrium are
interpreted separately; in particular no equilibrium predicate is used here.
-/

@[expose] public section

namespace KFOL

universe u v w

/-- A possible-winner value. Empty winner sets are excluded by the carrier. -/
abbrev WinnerSet (Role : Type u) := {S : Set Role // S.Nonempty}

namespace WinnerSet

variable {Role : Type u}

/-- A uniquely determined winner. -/
def singleton (r : Role) : WinnerSet Role := ⟨{r}, r, rfl⟩

/-- Union of possible winners. -/
def union (A B : WinnerSet Role) : WinnerSet Role :=
  ⟨A.val ∪ B.val, A.property.mono Set.subset_union_left⟩

/-- Owned choice: either owner's singleton absorbs, otherwise keep both sets. -/
noncomputable def choice (r : Role) (A B : WinnerSet Role) : WinnerSet Role :=
  if A = singleton r ∨ B = singleton r then singleton r else union A B

/-- Apply the same role permutation to every possible winner. -/
def rename (p : Equiv.Perm Role) (A : WinnerSet Role) : WinnerSet Role :=
  ⟨p '' A.val, by obtain ⟨a, ha⟩ := A.property; exact ⟨p a, a, ha, rfl⟩⟩

end WinnerSet

/-- The full public signature, including constants and internal role switches.
Variables denote independently evaluated copies at their different occurrences. -/
inductive Term (Role : Type u) (Var : Type v) where
  | winner (r : Role)
  | var (x : Var)
  | choice (r : Role) (left right : Term Role Var)
  | rename (p : Equiv.Perm Role) (t : Term Role Var)

namespace Term

variable {Role : Type u} {Var : Type v} {Var' : Type w}

/-- Evaluate a full-signature term in the nonempty winner-set algebra. -/
noncomputable def eval (valuation : Var → WinnerSet Role) : Term Role Var → WinnerSet Role
  | .winner r => WinnerSet.singleton r
  | .var x => valuation x
  | .choice r s t => WinnerSet.choice r (s.eval valuation) (t.eval valuation)
  | .rename p t => WinnerSet.rename p (t.eval valuation)

/-- Substitute an independent copy of the assigned term at every variable leaf. -/
def subst (replacement : Var → Term Role Var') : Term Role Var → Term Role Var'
  | .winner r => .winner r
  | .var x => replacement x
  | .choice r s t => .choice r (s.subst replacement) (t.subst replacement)
  | .rename p t => .rename p (t.subst replacement)

end Term

end KFOL
