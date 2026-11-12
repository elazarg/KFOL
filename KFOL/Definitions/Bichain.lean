module

public import KFOL.Definitions.Views
public import Mathlib.Data.Fintype.Basic

/-! # The four-element bichain and its union expansion

The meet order is b < possible < neutral < c; the join order swaps the two
middle values. Union records the observing player's possible membership.
-/

@[expose] public section
namespace KFOL.Bichain

/-- The two stable endpoints and the marked/unmarked middle values. -/
inductive Value where
  | b
  | c
  | possible
  | neutral
  deriving DecidableEq

instance : Fintype Value where
  elems := {.b, .c, .possible, .neutral}
  complete x := by cases x <;> simp

namespace Value

/-- Meet in the order b < possible < neutral < c. -/
def inf : Value → Value → Value
  | .b, _ | _, .b => .b
  | .c, x | x, .c => x
  | .possible, _ | _, .possible => .possible
  | .neutral, .neutral => .neutral

/-- Join in the order b < neutral < possible < c. -/
def sup : Value → Value → Value
  | .c, _ | _, .c => .c
  | .b, x | x, .b => x
  | .possible, _ | _, .possible => .possible
  | .neutral, .neutral => .neutral

/-- The observer's union: possible dominates and distinct endpoints merge. -/
def union : Value → Value → Value
  | .possible, _ | _, .possible => .possible
  | .b, .b => .b
  | .c, .c => .c
  | _, _ => .neutral

/-- Embed the two Boolean values as the stable endpoints b and c. -/
def ofBool : Bool → Value | false => .b | true => .c

/-- Boolean threshold cut above b: true at c and both middle values.
This is a cut indicator, rather than an interval endpoint. -/
def lower (x : Value) : Bool := x != .b

/-- Boolean threshold cut at c: true only at c.
This is a cut indicator, rather than an interval endpoint. -/
def upper (x : Value) : Bool := x == .c

/-- The information order induced by observer union. -/
def Resolves (x y : Value) : Prop := union x y = y

/-- Resolve the unmarked middle value to the endpoint b, fixing all other values. -/
def resolveNeutral : Value → Value | .neutral => .b | x => x

/-- The standard three-variable lattice expression, interpreted in the bichain. -/
def median (x y z : Value) : Value := sup (sup (inf x y) (inf x z)) (inf y z)

/-- Fix b and collapse every other value to possible. -/
def collapseB (x : Value) : Value := inf x .possible

/-- Fix c and collapse every other value to possible. -/
def collapseC (x : Value) : Value := sup x .possible

/-- A projection envelope: b,c,possible at the distinguished input are fixed;
at neutral it tests only the second input's possible value. -/
def envelope (x z : Value) : Value := inf x (sup x z)

/-- The observer-zero view on three roles, where a=0,b=1,c=2. -/
def toView : Value → KFOL.PlayerView (0 : Fin 3)
  | .b => .other ⟨1, by decide⟩
  | .c => .other ⟨2, by decide⟩
  | .possible => .possible
  | .neutral => .impossible

/-- Recover the four-state name from the observer-zero view. -/
def ofView : KFOL.PlayerView (0 : Fin 3) → Value
  | .possible => .possible
  | .impossible => .neutral
  | .other r => if r.val = 1 then .b else .c

/-- The four values are exactly the independently defined observer-zero views. -/
def viewEquiv : Value ≃ KFOL.PlayerView (0 : Fin 3) where
  toFun := toView
  invFun := ofView
  left_inv x := by cases x <;> rfl
  right_inv x := by
    cases x with
    | possible => rfl
    | impossible => rfl
    | other r =>
      obtain ⟨r, hr⟩ := r
      have hc : r = 0 ∨ r = 1 ∨ r = 2 :=
        (by decide +kernel : ∀ r : Fin 3, r = 0 ∨ r = 1 ∨ r = 2) r
      rcases hc with h | h | h <;> subst r
      · exact False.elim (hr rfl)
      · rfl
      · rfl

end Value

/-- Constant-free terms in the two bichain operations and observer union. -/
inductive Term (Var : Type*) where
  | var (j : Var)
  | inf (s t : Term Var)
  | sup (s t : Term Var)
  | union (s t : Term Var)

namespace Term

variable {Var Var' : Type*}

/-- Evaluation of a term, with independent copies at repeated input occurrences. -/
def eval (v : Var → Value) : Term Var → Value
  | .var j => v j
  | .inf s t => Value.inf (s.eval v) (t.eval v)
  | .sup s t => Value.sup (s.eval v) (t.eval v)
  | .union s t => Value.union (s.eval v) (t.eval v)

/-- The original two-operation language. -/
def IsPure : Term Var → Prop
  | .var _ => True
  | .inf s t | .sup s t => s.IsPure ∧ t.IsPure
  | .union _ _ => False

/-- Replace variable names, retaining every occurrence. -/
def map (f : Var → Var') : Term Var → Term Var'
  | .var j => .var (f j)
  | .inf s t => .inf (s.map f) (t.map f)
  | .sup s t => .sup (s.map f) (t.map f)
  | .union s t => .union (s.map f) (t.map f)

/-- The bichain expression used to eliminate a union at a neutral parameter. -/
def median (s t u : Term Var) : Term Var := .sup (.sup (.inf s t) (.inf s u)) (.inf t u)

/-- Replace every union by median at a fresh distinguished input. -/
def neutralLift : Term Var → Term (Option Var)
  | .var j => .var (some j)
  | .inf s t => .inf s.neutralLift t.neutralLift
  | .sup s t => .sup s.neutralLift t.neutralLift
  | .union s t => median s.neutralLift t.neutralLift (.var none)

/-- Embed a full operation into the Boolean-projection fiber at a fresh input. -/
def fiberLift (t : Term Var) : Term (Option Var) :=
  .inf (.var none) (.sup (.var none) t.neutralLift)

/-- The Boolean restriction is the distinguished projection. -/
def IsBooleanProjection (t : Term (Option Var)) : Prop :=
  ∀ v : Option Var → Bool, t.eval (fun j => Value.ofBool (v j)) = Value.ofBool (v none)

/-- The possible-value trace of an optional term; absence denotes the zero trace. -/
def hasPossible (t : Option (Term Var)) (v : Var → Value) : Prop :=
  match t with
  | none => False
  | some s => s.eval v = .possible

instance (t : Option (Term Var)) (v : Var → Value) : Decidable (hasPossible t v) := by
  cases t <;> simp only [hasPossible] <;> infer_instance

/-- Lift a full term into the pure projection fiber, representing zero by the
 distinguished variable itself. -/
def optionalLift : Option (Term Var) → Term (Option Var)
  | none => .var none
  | some t => t.fiberLift

end Term
end KFOL.Bichain
