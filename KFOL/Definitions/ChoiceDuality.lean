module

public import KFOL.Algebra.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Set.Lattice.Indexed

/-! # Literal full-powerset choice and its complement dual

The empty set is an identity for `own`, unlike the annihilating-zero
extension used for equilibrium-free continuations. Both operations are
defined on all sets; proper sets carry the complement of winner semantics.
-/

@[expose] public section
namespace KFOL.ChoiceDuality
universe u v
variable {Role : Type u} {Var : Type v}

noncomputable def own (r : Role) (S T : Set Role) : Set Role :=
  if S = {r} ∨ T = {r} then {r} else S ∪ T

noncomputable def dual (r : Role) (S T : Set Role) : Set Role :=
  (own r Sᶜ Tᶜ)ᶜ

/-- Only singleton constants, variables, and the two choice families. -/
inductive Term (Role : Type u) (Var : Type v) where
  | winner (r : Role)
  | var (x : Var)
  | own (r : Role) (s t : Term Role Var)
  | dual (r : Role) (s t : Term Role Var)

noncomputable def Term.eval (values : Var → Set Role) : Term Role Var → Set Role
  | .winner r => {r}
  | .var x => values x
  | .own r s t => ChoiceDuality.own r (s.eval values) (t.eval values)
  | .dual r s t => ChoiceDuality.dual r (s.eval values) (t.eval values)

def Expressible (f : (Var → Set Role) → Set Role) : Prop :=
  ∃ t : Term Role Var, ∀ values, t.eval values = f values

end KFOL.ChoiceDuality
