module

public import KFOL.Definitions.Atomic
public import KFOL.Definitions.Congruences
public import KFOL.Definitions.Owner
public import KFOL.Definitions.TestDomains

/-! # Semantic vocabulary for the winner algebras

These definitions express equality of operations, diagonal idempotency and
polynomial observations directly in the independent evaluators. They do not
mention theorems, algorithms, normal forms or equational derivability.
-/

@[expose] public section
namespace KFOL
universe u v

/-- Two full-signature terms define the same operation. -/
def Term.Equivalent {Role : Type u} {Var : Type v} (s t : Term Role Var) : Prop :=
  ∀ valuation : Var → WinnerSet Role, s.eval valuation = t.eval valuation

/-- A term operation fixes every constant diagonal input. -/
def Term.Idempotent {Role : Type u} {Var : Type v} (t : Term Role Var) : Prop :=
  ∀ A : WinnerSet Role, t.eval (fun _ => A) = A

/-- A unary polynomial may contain arbitrarily many occurrences of its input
and independently fixed nonempty parameters. Only public operations are used. -/
def WinnerSet.ObservationallyEquivalent {Role : Type u} (k : Role)
    (A B : WinnerSet Role) : Prop :=
  ∀ (n : ℕ) (t : Term Role (Option (Fin n))), t.IsPublic →
    ∀ parameters : Fin n → WinnerSet Role,
      (k ∈ (t.eval (fun x => x.elim A parameters)).val ↔
        k ∈ (t.eval (fun x => x.elim B parameters)).val)

/-- Two reset terms define the same operation on the given role carrier. -/
def Reset.Term.Equivalent (Role : Type u) {Var : Type v} (s t : Reset.Term Var) : Prop :=
  ∀ valuation : Var → WinnerSet Role, s.eval valuation = t.eval valuation

/-- Two guarded-owner terms define the same operation. -/
def Owner.Term.Equivalent {Role : Type u} {Var : Type v}
    (s t : Owner.Term Role Var) : Prop :=
  ∀ valuation : Var → WinnerSet Role, s.eval valuation = t.eval valuation

/-- The layered order read directly from a player view. An observed other
owner atom is top; the remaining atoms lie below impossible, then possible. -/
def PlayerView.Below {Role : Type u} {k : Role} (owner : Role) (p q : PlayerView k) : Prop :=
  match p,q with
  | .possible,.possible => True
  | .possible,.impossible => False
  | .possible,.other j => j.val = owner
  | .impossible,.possible | .impossible,.impossible => True
  | .impossible,.other j => j.val = owner
  | .other i,.possible | .other i,.impossible => i.val ≠ owner
  | .other i,.other j => i = j ∨ j.val = owner

/-- Give the distinguished source the third chain value, other requested
ambiguous positions the middle value, and all remaining positions the atom.
Only the distinguished source carries the marker role. -/
def Reset.markerValuation {Role : Type u} {Var : Type v} [DecidableEq Var]
    (three : Fin 3 ↪ Role) (j : Var) (A : Finset Var) (i : Var) : WinnerSet Role :=
  chainValue three (if i = j then 2 else if i ∈ A then 1 else 0)

end KFOL
