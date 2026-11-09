module

public import KFOL.Definitions.Reset

/-! # Reset with owner-labelled guarded choice

The signature reuses mathlib terms and the shared nonempty winner-set carrier.
Guard lists describe finite conjunctions; repeated tests are harmless, while
separate variable occurrences still produce separate guards.
-/

@[expose] public section

namespace KFOL

universe u v

/-- The guarded operation from the paper: combine the side inputs by owned
choice, then reset against the root input. -/
noncomputable def WinnerSet.guardedChoice {Role : Type u} (r : Role)
    (root left right : WinnerSet Role) : WinnerSet Role :=
  (WinnerSet.choice r left right).reset root

namespace Owner

inductive Symbol (Role : Type u) : ℕ → Type u
  | reset : Symbol Role 2
  | guarded (r : Role) : Symbol Role 3

abbrev Term (Role : Type u) (Var : Type v) := Equational.Term (Symbol Role) Var

/-- Interpret exactly the two families of operations in the owner signature. -/
@[instance_reducible] noncomputable def structureOf {Role : Type u} :
    (Equational.language (Symbol Role)).Structure (WinnerSet Role) where
  funMap f args := match f with
    | .reset => (args 0).reset (args 1)
    | .guarded r => WinnerSet.guardedChoice r (args 0) (args 1) (args 2)
  RelMap r := nomatch r

namespace Term

variable {Role : Type u} {Var : Type v}

def step (s t : Term Role Var) : Term Role Var :=
  .func .reset (fun i => if i = 0 then s else t)

def guarded (r : Role) (x y z : Term Role Var) : Term Role Var :=
  .func (.guarded r) (fun i => if i = 0 then x else if i = 1 then y else z)

def root : Term Role Var → Var
  | .var j => j
  | .func .reset args => root (args 1)
  | .func (.guarded _) args => root (args 0)

noncomputable def eval (t : Term Role Var) (v : Var → WinnerSet Role) : WinnerSet Role :=
  let _ := structureOf (Role := Role)
  t.realize v

/-- A syntactic restriction on the owner labels, independent of evaluation. -/
def OwnersIn (P : Role → Prop) : Term Role Var → Prop
  | .var _ => True
  | .func .reset args => OwnersIn P (args 0) ∧ OwnersIn P (args 1)
  | .func (.guarded r) args => P r ∧ OwnersIn P (args 0) ∧
      OwnersIn P (args 1) ∧ OwnersIn P (args 2)

def leafCount : Term Role Var → ℕ
  | .var _ => 1
  | .func .reset args => leafCount (args 0) + leafCount (args 1)
  | .func (.guarded _) args => leafCount (args 0) + leafCount (args 1) + leafCount (args 2)

end Term

/-- A source together with ambiguous and non-owner-atom tests. The two lists
represent conjunctions, with no semantic dependence on their order. -/
structure Guard (Var : Type v) where
  source : Var
  many : List Var := []
  outside : List Var := []
  deriving DecidableEq

def Guard.Holds {Var : Type v} (M N V : Var → Prop) (g : Guard Var) : Prop :=
  (∀ j ∈ g.many, M j) ∧ (∀ j ∈ g.outside, N j) ∧ V g.source

def Guard.addMany {Var : Type v} (j : Var) (g : Guard Var) : Guard Var :=
  { g with many := j :: g.many }

def Guard.addOutside {Var : Type v} (j : Var) (g : Guard Var) : Guard Var :=
  { g with outside := j :: g.outside }

def Eval {Var : Type v} (guards : List (Guard Var)) (M N V : Var → Prop) : Prop :=
  ∃ g ∈ guards, g.Holds M N V

/-- A weaker guard dominates a stronger one exactly by the displayed
source and prerequisite containments in the paper. -/
def Guard.Dominates {Var : Type v} (weak strong : Guard Var) : Prop :=
  weak.source = strong.source ∧
  (∀ j ∈ weak.many, j ∈ strong.many) ∧
  (∀ j ∈ weak.outside, j ∈ strong.many ∨ j ∈ strong.outside ∨ j = strong.source)

def Covers {Var : Type v} (left right : List (Guard Var)) : Prop :=
  ∀ g ∈ left, ∃ h ∈ right, h.Dominates g

/-- One raw guard per original variable occurrence. Tests inspect roots of
subterms, without distributing their own guard lists. -/
def Term.guards {Role : Type u} {Var : Type v} [DecidableEq Role]
    (observer : Role) : Term Role Var → List (Guard Var)
  | .var j => [⟨j, [], []⟩]
  | .func .reset args => guards observer (args 1) ++
      (guards observer (args 0)).map (Guard.addMany (root (args 1)))
  | .func (.guarded r) args =>
      let children := guards observer (args 1) ++ guards observer (args 2)
      let eligible := if r = observer then children else
        (children.map (Guard.addOutside (root (args 1)))).map (Guard.addOutside (root (args 2)))
      guards observer (args 0) ++ eligible.map (Guard.addMany (root (args 0)))

def Guard.forget {Var : Type v} (g : Guard Var) : Guard Var := { g with outside := [] }

def dominatesB {Var : Type v} [DecidableEq Var] (weak strong : Guard Var) : Bool :=
  decide (weak.source = strong.source) &&
  weak.many.all (fun j => decide (j ∈ strong.many)) &&
  weak.outside.all (fun j => decide (j ∈ strong.many ∨ j ∈ strong.outside ∨ j = strong.source))

def coversB {Var : Type v} [DecidableEq Var] (left right : List (Guard Var)) : Bool :=
  left.all (fun g => right.any (fun h => dominatesB h g))

def Term.equationB {Role : Type u} {Var : Type v} [DecidableEq Role] [DecidableEq Var]
    (observer : Role) (left right : Term Role Var) : Bool :=
  coversB (left.guards observer) (right.guards observer) &&
    coversB (right.guards observer) (left.guards observer)

/-- The minimal three-role valuation associated with a failed guard test.
Every value is an atom or a pair, including the source's marker value. -/
def minimalVal {Role : Type u} {Var : Type v} [DecidableEq Var]
    (observer other background : Role) (g : Guard Var) (j : Var) : WinnerSet Role :=
  if j = g.source then
    if j ∈ g.many then (WinnerSet.singleton observer).union (WinnerSet.singleton other)
      else WinnerSet.singleton observer
  else if j ∈ g.many then (WinnerSet.singleton other).union (WinnerSet.singleton background)
  else if j ∈ g.outside then WinnerSet.singleton background else WinnerSet.singleton other

/-- The fixed four-element owner algebra. Its winning state represents the
observer's presence, independently of the root's atomic/ambiguous distinction. -/
inductive Four where
  | owner | other | ambiguous | winning
  deriving DecidableEq, Repr

namespace Four

instance : Fintype Four where
  elems := {.owner, .other, .ambiguous, .winning}
  complete := by intro x; cases x <;> simp

def reset (x y : Four) : Four :=
  if y = .ambiguous ∧ x = .winning then .winning else y

def guarded (x y z : Four) : Four :=
  if x = .ambiguous then
    if y ≠ .owner ∧ z ≠ .owner ∧ (y = .winning ∨ z = .winning) then .winning else .ambiguous
  else x

/-- Observer projection onto the four-state algebra. -/
noncomputable def project {Role : Type u} (owner observer : Role) (A : WinnerSet Role) : Four := by
  classical
  exact if observer ∈ A.val then .winning else
    if A = WinnerSet.singleton owner then .owner else
      if A.Ambiguous then .ambiguous else .other

/-- The concrete four winner sets displayed in the paper. -/
def embed {Role : Type u} (owner observer background : Role) : Four → WinnerSet Role
  | .owner => WinnerSet.singleton owner
  | .other => WinnerSet.singleton background
  | .ambiguous => (WinnerSet.singleton owner).union (WinnerSet.singleton background)
  | .winning => ((WinnerSet.singleton owner).union (WinnerSet.singleton background)).union
      (WinnerSet.singleton observer)

end Four

/-- All owner labels act by the fixed guarded operation on Four; equality
transport is restricted to terms using the chosen concrete owner. -/
@[instance_reducible] def fourStructure {Role : Type u} :
    (Equational.language (Symbol Role)).Structure Four where
  funMap f args := match f with
    | .reset => Four.reset (args 0) (args 1)
    | .guarded _ => Four.guarded (args 0) (args 1) (args 2)
  RelMap r := nomatch r

def Term.evalFour {Role : Type u} {Var : Type v} (t : Term Role Var) (v : Var → Four) : Four :=
  let _ := fourStructure (Role := Role)
  t.realize v

end Owner
end KFOL
