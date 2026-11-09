module

public import KFOL.Definitions.Encoding
public import KFOL.Definitions.Owner

/-! # Native reset/union syntax and the CNF equation reduction

The syntax and validity use mathlib terms and the shared winner-set model.
The source CNF is the elementary list-of-lists representation; machine library
encodings and complexity classes enter only in the complexity branch.
-/

@[expose] public section

namespace KFOL.ResetUnion

universe u v

inductive Symbol : ℕ → Type
  | reset : Symbol 2
  | union : Symbol 2

abbrev Term (Var : Type v) := Equational.Term Symbol Var

@[instance_reducible] noncomputable def structureOf {Role : Type u} :
    (Equational.language Symbol).Structure (WinnerSet Role) where
  funMap f args := match f with
    | .reset => (args 0).reset (args 1)
    | .union => (args 0).union (args 1)
  RelMap r := nomatch r

namespace Term

variable {Var : Type v} {Role : Type u}

def reset (s t : Term Var) : Term Var :=
  .func .reset (fun i => if i = 0 then s else t)

def union (s t : Term Var) : Term Var :=
  .func .union (fun i => if i = 0 then s else t)

noncomputable def eval (t : Term Var) (valuation : Var → WinnerSet Role) : WinnerSet Role :=
  let _ := structureOf (Role := Role)
  t.realize valuation

def size : Term Var → ℕ
  | .var _ => 1
  | .func .reset args => 1 + size (args 0) + size (args 1)
  | .func .union args => 1 + size (args 0) + size (args 1)

/-- Right-associated reset, with one copy of the continuation. -/
def rightComb (terms : List (Term Var)) (base : Term Var) : Term Var := terms.foldr reset base

/-- Left-associated successive ambiguity tests. -/
def leftComb (base : Term Var) (terms : List (Term Var)) : Term Var := terms.foldl reset base

/-- Left-associated native unions, including a supplied nonempty base. -/
def unionFold (base : Term Var) (terms : List (Term Var)) : Term Var := terms.foldl union base

end Term

abbrev Equation := Term ℕ × Term ℕ

/-- Independent equational validity on the actual nonempty winner-set model. -/
def Valid (Role : Type u) (equation : Equation) : Prop :=
  ∀ valuation : ℕ → WinnerSet Role, equation.1.eval valuation = equation.2.eval valuation

namespace Code

open KFOL.Words

/-- Prefix codes frame binary variable names once. Binary nodes use a
reset/union tag without framing or duplicating either recursive subtree. -/
def encode : Term ℕ → List Bool
  | .var j => false :: delimit (BinaryNatCode.encode j)
  | .func .reset args => true :: false :: (encode (args 0) ++ encode (args 1))
  | .func .union args => true :: true :: (encode (args 0) ++ encode (args 1))

/-- A size-clocked independent parser for one complete prefix subtree. -/
def parse : ℕ → List Bool → Option (Term ℕ × List Bool)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, false :: word => do
      let (name, rest) ← unpair? word
      let j ← BinaryNatCode.decode? name
      return (.var j, rest)
  | _ + 1, true :: [] => none
  | fuel + 1, true :: operation :: word => do
      let (left, rest) ← parse fuel word
      let (right, rest) ← parse fuel rest
      return ((if operation then Term.union left right else Term.reset left right), rest)

def decode (word : List Bool) : Option (Term ℕ) := do
  let (term, rest) ← parse word.length word
  if rest.isEmpty then some term else none

def encodeEquation (equation : Equation) : List Bool := pair (encode equation.1) (encode equation.2)

def decodeEquation (word : List Bool) : Option Equation := do
  let (left, right) ← unpair? word
  let s ← decode left
  let t ← decode right
  return (s, t)

end Code

/-- The full binary language rejects malformed equation codes. -/
def Language (Role : Type u) : Set (List Bool) :=
  {word | ∃ equation : Equation, Code.encodeEquation equation = word ∧ Valid Role equation}

end KFOL.ResetUnion

namespace KFOL.Reductions

abbrev Literal := ℕ × Bool
abbrev Clause := List Literal
abbrev CNF := List Clause

/-- True polarity is positive. Empty clauses are false, and an empty formula
is true, independently of the reduction syntax. -/
def Satisfiable (formula : CNF) : Prop :=
  ∃ assignment : ℕ → Bool, ∀ clause ∈ formula, ∃ literal ∈ clause,
    assignment literal.1 = literal.2

namespace ResetUnion

open KFOL.ResetUnion

/-- The dummy Boolean variable guarantees one consistency branch. It need
not occur in a clause and does not change satisfiability. Numeric maxima
never control the construction. -/
def support (formula : CNF) : List ℕ := (0 :: formula.flatten.map Prod.fst).dedup

/-- Anchor inputs are 0,1,2; literal inputs are disjoint odd/even names. -/
def literalName (literal : Literal) : ℕ :=
  if literal.2 then 2 * literal.1 + 3 else 2 * literal.1 + 4

def literalTerm (literal : Literal) : KFOL.ResetUnion.Term ℕ := .var (literalName literal)

def baseline (formula : CNF) : KFOL.ResetUnion.Term ℕ :=
  KFOL.ResetUnion.Term.rightComb
    (((support formula).flatMap (fun j => [literalTerm (j, true), literalTerm (j, false)])) ++ [.var 0])
    (.var 1)

def branch (j : ℕ) : KFOL.ResetUnion.Term ℕ :=
  KFOL.ResetUnion.Term.reset (KFOL.ResetUnion.Term.reset (.var 2) (KFOL.ResetUnion.Term.union (literalTerm (j, true)) (.var 0)))
    (KFOL.ResetUnion.Term.union (literalTerm (j, false)) (.var 0))

def right (formula : CNF) : KFOL.ResetUnion.Term ℕ :=
  KFOL.ResetUnion.Term.rightComb ((support formula).map branch) (baseline formula)

def clauseGuard (clause : Clause) : KFOL.ResetUnion.Term ℕ :=
  KFOL.ResetUnion.Term.unionFold (.var 0) (clause.map literalTerm)

def left (formula : CNF) : KFOL.ResetUnion.Term ℕ :=
  KFOL.ResetUnion.Term.leftComb (.var 2) (formula.map clauseGuard)

/-- The actual tree equation from the report. Repeated subterms are separate
copies; the output has no constants, owner names or role switches. -/
def equation (formula : CNF) : Equation :=
  (KFOL.ResetUnion.Term.reset (left formula) (right formula), right formula)

end ResetUnion
end KFOL.Reductions

namespace KFOL.GuardedPair

universe u v

/-- Only two ternary guarded owners. In particular reset is not a symbol. -/
inductive Symbol : ℕ → Type where
  | guarded : Bool → Symbol 3

abbrev Term (Var : Type v) := Equational.Term Symbol Var

@[instance_reducible] noncomputable def structureOf {Role : Type u} (a b : Role) :
    (Equational.language Symbol).Structure (WinnerSet Role) where
  funMap symbol args := match symbol with
    | .guarded sign => WinnerSet.guardedChoice (if sign then a else b) (args 0) (args 1) (args 2)
  RelMap rel := nomatch rel

namespace Term

variable {Var : Type v} {Role : Type u}

def guarded (sign : Bool) (x y z : Term Var) : Term Var :=
  .func (.guarded sign) (fun i => if i = 0 then x else if i = 1 then y else z)

/-- The genuine native expansion duplicates only its left operand. -/
def reset (s t : Term Var) : Term Var := guarded true t s s

noncomputable def eval (a b : Role) (t : Term Var) (valuation : Var → WinnerSet Role) : WinnerSet Role :=
  let _ := structureOf a b
  t.realize valuation

def size : Term Var → ℕ
  | .var _ => 1
  | .func (.guarded _) args => 1 + size (args 0) + size (args 1) + size (args 2)

def rightComb (terms : List (Term Var)) (base : Term Var) : Term Var := terms.foldr reset base

end Term
end KFOL.GuardedPair

namespace KFOL.Reductions.GuardedPair

universe u

/-- Variable labels are translated sparsely, never enumerated to a maximum. -/
def booleanName (i : ℕ) : ℕ := i + 2

def clause : Clause → KFOL.GuardedPair.Term ℕ
  | [] => .var 1
  | literal :: rest => KFOL.GuardedPair.Term.guarded literal.2 (.var 0) (.var (booleanName literal.1)) (clause rest)

def baseline (formula : CNF) : KFOL.GuardedPair.Term ℕ :=
  KFOL.GuardedPair.Term.rightComb ((ResetUnion.support formula).map (fun i => .var (booleanName i))) (.var 0)

def right (formula : CNF) : KFOL.GuardedPair.Term ℕ := KFOL.GuardedPair.Term.rightComb (formula.map clause) (baseline formula)

def equation (formula : CNF) : KFOL.GuardedPair.Term ℕ × KFOL.GuardedPair.Term ℕ := (KFOL.GuardedPair.Term.reset (.var 1) (right formula), right formula)

noncomputable def satisfyingValuation {Role : Type u} (a b d : Role) (assignment : ℕ → Bool) : ℕ → WinnerSet Role
  | 0 => (WinnerSet.singleton a).union (WinnerSet.singleton b)
  | 1 => WinnerSet.singleton d
  | i + 2 => WinnerSet.singleton (if assignment i then a else b)

end KFOL.Reductions.GuardedPair
