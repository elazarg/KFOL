module

public import KFOL.Definitions.Bichain
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Bool.Basic

/-! # Canonical extensions of Boolean functions to the bichain

The definition records essential marked variables on the input's Boolean cube.
It is independent of terms and of the separating-source condition.
-/

@[expose] public section
namespace KFOL.Bichain

universe u
variable {Var : Type u}

/-- The Boolean cube between two coordinatewise bounds. -/
def InCube (lower upper v : Var → Bool) : Prop := lower ≤ v ∧ v ≤ upper

/-- A coordinate is essential when the cube contains a pivotal edge in it. -/
def Essential [DecidableEq Var] (f : (Var → Bool) → Bool)
    (lower upper : Var → Bool) (j : Var) : Prop :=
  ∃ v : Var → Bool, InCube lower upper v ∧ v j = false ∧
    InCube lower upper (Function.update v j true) ∧
    f v = false ∧ f (Function.update v j true) = true

instance [Fintype Var] [DecidableEq Var] (f : (Var → Bool) → Bool)
    (lower upper : Var → Bool) (j : Var) : Decidable (Essential f lower upper j) :=
  by unfold Essential InCube; infer_instance

/-- Coordinates fixed to the true endpoint by a bichain valuation. -/
def cubeLower (v : Var → Value) : Var → Bool := fun j => v j == .c

/-- Coordinates that are not fixed to the false endpoint. -/
def cubeUpper (v : Var → Value) : Var → Bool := fun j => v j != .b

/-- Stable outputs are the cube endpoints; otherwise possible records precisely
an essential coordinate marked possible in the input. -/
def canonicalExtension [Fintype Var] [DecidableEq Var]
    (f : (Var → Bool) → Bool) (v : Var → Value) : Value :=
  if f (cubeLower v) then .c else
    if f (cubeUpper v) then
      if ∃ j, v j = .possible ∧ Essential f (cubeLower v) (cubeUpper v) j
        then .possible else .neutral
    else .b

/-- A single marked coordinate in a Boolean cube; the hypotheses making the
specified coordinate free are used by theorems, rather than by this definition. -/
def markedCube [DecidableEq Var] (lower upper : Var → Bool) (j : Var) : Var → Value :=
  fun i => if i = j then .possible else
    if lower i then .c else if upper i then .neutral else .b

/-- Existence of an actual term, including observer union, for the independently
defined canonical extension. -/
def HasCanonicalRealizer [Fintype Var] [DecidableEq Var]
    (f : (Var → Bool) → Bool) : Prop :=
  ∃ t : Term Var, ∀ v, t.eval v = canonicalExtension f v

/-- Every positive/negative pair has one separating coordinate that remains
essential throughout all cubes whose upper bound contains the positive input
and whose lower bound lies below the negative input. -/
def StableSeparatingSource [DecidableEq Var] (f : (Var → Bool) → Bool) : Prop :=
  ∀ A B, f A = true → f B = false → ∃ j, A j = true ∧ B j = false ∧
    ∀ lower upper, lower ≤ upper → lower ≤ B → A ≤ upper →
      Essential f lower upper j

/-- Fix one Boolean coordinate while retaining the original ambient variable set. -/
def booleanCofactor {Var : Type*} [DecidableEq Var]
    (f : (Var → Bool) → Bool) (j : Var) (bit : Bool) : (Var → Bool) → Bool :=
  fun v => f (Function.update v j bit)

namespace Term

/-- The finite set of input names, keeping occurrence multiplicity in the term. -/
def vars [DecidableEq Var] : Term Var → Finset Var
  | .var j => {j}
  | .inf s t | .sup s t | .union s t => s.vars ∪ t.vars

/-- Pure terms with disjoint child supports at every node. -/
def IsReadOnce [DecidableEq Var] : Term Var → Prop
  | .var _ => True
  | .inf s t | .sup s t => s.IsReadOnce ∧ t.IsReadOnce ∧ Disjoint s.vars t.vars
  | .union _ _ => False

end Term

end KFOL.Bichain
