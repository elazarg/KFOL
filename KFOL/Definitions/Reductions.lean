module

public import KFOL.Definitions.Encoding

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
