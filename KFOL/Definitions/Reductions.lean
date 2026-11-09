module

public import KFOL.Definitions.Encoding
public import KFOL.Definitions.Owner
public import KFOL.Definitions.Circuits

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

/-! ## Original native hard raw binary pairs -/

namespace KFOL.Reductions.RawPair

universe u v

variable {Role : Type u} {Var : Type v}

noncomputable def choiceFold (a : Role) (xs : List (WinnerSet Role)) (base : WinnerSet Role) : WinnerSet Role :=
  xs.foldr (WinnerSet.choice a) base

noncomputable def unions (xs : List (WinnerSet Role)) (base : WinnerSet Role) : WinnerSet Role :=
  xs.foldr WinnerSet.union base

end KFOL.Reductions.RawPair

namespace KFOL.RawPair

universe u v

variable {Role : Type u} {Var : Type v}

inductive Symbol : ℕ → Type where
  | binary : Bool → Symbol 2

abbrev Term (Var : Type v) := Equational.Term Symbol Var

@[instance_reducible] noncomputable def structureOf {Role : Type u}
    (first second : WinnerSet Role → WinnerSet Role → WinnerSet Role) :
    (Equational.language Symbol).Structure (WinnerSet Role) where
  funMap symbol args := match symbol with
    | .binary sign => (if sign then first else second) (args 0) (args 1)
  RelMap rel := nomatch rel

namespace Term

variable {Var : Type v} {Role : Type u}

def node (sign : Bool) (s t : Term Var) : Term Var :=
  .func (.binary sign) (fun i => if i = 0 then s else t)

noncomputable def eval (first second : WinnerSet Role → WinnerSet Role → WinnerSet Role)
    (t : Term Var) (v : Var → WinnerSet Role) : WinnerSet Role :=
  let _ := structureOf first second
  t.realize v

def size : Term Var → ℕ
  | .var _ => 1
  | .func (.binary _) args => 1 + size (args 0) + size (args 1)

def fold (sign : Bool) (terms : List (Term Var)) (base : Term Var) : Term Var :=
  terms.foldr (node sign) base

end Term
end KFOL.RawPair

namespace KFOL.Reductions.RawPair

universe u v

variable {Role : Type u} {Var : Type v}

noncomputable def outerOp {Role : Type u} : Option Role → WinnerSet Role → WinnerSet Role → WinnerSet Role
  | none => WinnerSet.union
  | some b => WinnerSet.choice b

def literalTerm (literal : Literal) : KFOL.RawPair.Term ℕ := .var (ResetUnion.literalName literal)

def rails (formula : CNF) : List (KFOL.RawPair.Term ℕ) :=
  (ResetUnion.support formula).flatMap (fun i => [literalTerm (i, true), literalTerm (i, false)])

def baseline (formula : CNF) : KFOL.RawPair.Term ℕ :=
  KFOL.RawPair.Term.fold false (rails formula) (literalTerm (0, true))

def branch (i : ℕ) : KFOL.RawPair.Term ℕ :=
  KFOL.RawPair.Term.node true (.var 0)
    (KFOL.RawPair.Term.node true (literalTerm (i, true)) (literalTerm (i, false)))

def right (formula : CNF) : KFOL.RawPair.Term ℕ :=
  KFOL.RawPair.Term.fold false ((ResetUnion.support formula).map branch) (baseline formula)

def clause : Clause → KFOL.RawPair.Term ℕ
  | [] => .var 0
  | literal :: rest => KFOL.RawPair.Term.fold false (rest.map literalTerm) (literalTerm literal)

def left (formula : CNF) : KFOL.RawPair.Term ℕ :=
  KFOL.RawPair.Term.fold true (formula.map clause) (.var 0)

def coreEquation (formula : CNF) : KFOL.RawPair.Term ℕ × KFOL.RawPair.Term ℕ :=
  (KFOL.RawPair.Term.node false (left formula) (right formula), right formula)

/-- The exceptional empty cases are part of the actual reduction program. -/
def equation (formula : CNF) : KFOL.RawPair.Term ℕ × KFOL.RawPair.Term ℕ :=
  if formula.any List.isEmpty then (.var 0, .var 0)
  else coreEquation formula

end KFOL.Reductions.RawPair

namespace KFOL.Reductions.RawPair

universe u v

variable {Role : Type u} {Var : Type v}

noncomputable def satisfyingValuation {Role : Type u} (a marker c : Role) (assignment : ℕ → Bool) :
    ℕ → WinnerSet Role :=
  Function.extend ResetUnion.literalName
    (fun literal => WinnerSet.singleton (if assignment literal.1 = literal.2 then c else a))
    (fun _ => WinnerSet.singleton marker)

end KFOL.Reductions.RawPair

namespace KFOL.Reductions.RawPair

universe u v

variable {Role : Type u} {Var : Type v}

/-- The empty conjunction maps to a fixed invalid equation for two owners. -/
def twoOwnerEquation (formula : CNF) : KFOL.RawPair.Term ℕ × KFOL.RawPair.Term ℕ :=
  if formula.isEmpty then (.var 0, .var 1) else equation formula

end KFOL.Reductions.RawPair

namespace KFOL.Reductions.ResetChoice

universe u v

variable {Role : Type u} {Var : Type v}

/-- No macro expansion: every source binary node remains one target node. -/
def translate {Var : Type v} : KFOL.ResetUnion.Term Var → KFOL.RawPair.Term Var
  | .var j => .var j
  | .func .reset args => KFOL.RawPair.Term.node true (translate (args 0)) (translate (args 1))
  | .func .union args => KFOL.RawPair.Term.node false (translate (args 0)) (translate (args 1))

/-- Empty clauses map to a fixed valid native equation; the empty conjunction
is already invalid under the core construction's explicit SAT valuation. -/
def equation (formula : CNF) : KFOL.RawPair.Term ℕ × KFOL.RawPair.Term ℕ :=
  if formula.any List.isEmpty then (.var 0, .var 0)
  else (translate (ResetUnion.equation formula).1, translate (ResetUnion.equation formula).2)

end KFOL.Reductions.ResetChoice


namespace KFOL.Reductions.Colouring

universe u v

/-- Exactly n ordinary vertex variables, disjoint from root0 and marker1. -/
def vertexName (n : ℕ) (i : Fin n) : Fin (n + 2) := ⟨i.val + 2, by omega⟩

def edges (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap (fun i => ((List.finRange n).filter (fun j => i.val < j.val)).map (i, ·))

def baseline (n : ℕ) : KFOL.ResetUnion.Term (Fin (n + 2)) :=
  KFOL.ResetUnion.Term.rightComb ((List.finRange n).map (fun i => .var (vertexName n i))) (.var 0)

def right (n : ℕ) : KFOL.ResetUnion.Term (Fin (n + 2)) :=
  KFOL.ResetUnion.Term.rightComb ((List.finRange n).map
    (fun i => KFOL.ResetUnion.Term.reset (.var 1) (.var (vertexName n i)))) (baseline n)

def left (n : ℕ) : KFOL.ResetUnion.Term (Fin (n + 2)) :=
  KFOL.ResetUnion.Term.leftComb (.var 1) ((edges n).map
    (fun edge => KFOL.ResetUnion.Term.union (.var (vertexName n edge.1)) (.var (vertexName n edge.2))))

def equation (n : ℕ) : Equational.Identity KFOL.ResetUnion.Symbol :=
  ⟨n + 2, KFOL.ResetUnion.Term.reset (left n) (right n), right n⟩

/-- All n vertex inputs are distinct atoms; the marker is the one unused
role. The root pair uses only the first two vertex roles. -/
noncomputable def successorValuation (n : ℕ) (hn : 2 ≤ n) :
    Fin (n + 2) → WinnerSet (Fin (n + 1)) :=
  Function.extend (vertexName n) (fun i => WinnerSet.singleton i.castSucc)
    (fun j => if j = 0 then
      (WinnerSet.singleton ⟨0, by omega⟩).union (WinnerSet.singleton ⟨1, by omega⟩)
      else WinnerSet.singleton (Fin.last n))

/-- Inclusion of roles sends a winner set to its nonempty image. -/
def embedWinnerSet {Role : Type u} {Role' : Type v} (f : Role ↪ Role')
    (A : WinnerSet Role) : WinnerSet Role' := ⟨f '' A.val, A.property.image f⟩

end KFOL.Reductions.Colouring

/-! Arbitrary finite raw subsignatures. -/

namespace KFOL.Raw

universe u v

/- The raw operations are independent of any chosen presentation. -/
inductive Operation (Role : Type u) where
  | choice : Role → Operation Role
  | union : Operation Role
  | reset : Operation Role
  deriving DecidableEq

namespace Operation

noncomputable def eval {Role : Type u} : Operation Role → WinnerSet Role → WinnerSet Role → WinnerSet Role
  | .choice r => WinnerSet.choice r
  | .union => WinnerSet.union
  | .reset => WinnerSet.reset

end Operation

/- A term can use precisely the selected native binary operations. -/
inductive Symbol {Role : Type u} (selected : Finset (Operation Role)) : ℕ → Type u
  | binary : {operation // operation ∈ selected} → Symbol selected 2

abbrev Term {Role : Type u} (selected : Finset (Operation Role)) (Var : Type v) := Equational.Term (Symbol selected) Var

@[instance_reducible] noncomputable def structureOf {Role : Type u} (selected : Finset (Operation Role)) :
    (Equational.language (Symbol selected)).Structure (WinnerSet Role) where
  funMap symbol args := match symbol with
    | .binary operation => operation.val.eval (args 0) (args 1)
  RelMap rel := nomatch rel

namespace Term

variable {Role : Type u} {Var : Type v} {selected : Finset (Operation Role)}

def node (operation : {operation // operation ∈ selected}) (s t : Term selected Var) : Term selected Var :=
  .func (.binary operation) (fun i => if i = 0 then s else t)

noncomputable def eval (t : Term selected Var) (valuation : Var → WinnerSet Role) : WinnerSet Role :=
  let _ := structureOf selected
  t.realize valuation

def size : Term selected Var → ℕ
  | .var _ => 1
  | .func (.binary _) args => 1 + size (args 0) + size (args 1)

/- Node-for-node injection. The tag map chooses two actual selected
operations; no recursive argument is duplicated or deleted. -/
def ofRawPair (operations : Bool → {operation // operation ∈ selected}) : RawPair.Term Var → Term selected Var
  | .var j => .var j
  | .func (.binary sign) args => .func (.binary (operations sign)) (fun i => ofRawPair operations (args i))

end Term
end KFOL.Raw

namespace KFOL.Raw

universe u v

namespace Term

variable {Role : Type u} {Var : Type v} {selected : Finset (Operation Role)}

def support [DecidableEq Var] : Term selected Var → Finset Var
  | .var j => {j}
  | .func (.binary _) args => support (args 0) ∪ support (args 1)

end Term
end KFOL.Raw

namespace KFOL.Raw

universe u v

namespace Term

variable {Role : Type u} {Var : Type v} {selected : Finset (Operation Role)}

end Term

/- Every signature with at least two operations contains one of the four
hard pairs, independently of the chosen finite operation numbering. -/
end KFOL.Raw

namespace KFOL.Raw

universe u v

namespace Term

variable {Role : Type u} {Var : Type v} {selected : Finset (Operation Role)}

def pairOperations (first second : Operation Role) (hf : first ∈ selected) (hs : second ∈ selected) :
    Bool → {operation // operation ∈ selected}
  | true => ⟨first, hf⟩
  | false => ⟨second, hs⟩

def ofResetUnion (hreset : Operation.reset ∈ selected) (hunion : Operation.union ∈ selected) :
    ResetUnion.Term Var → Term selected Var
  | .var j => .var j
  | .func .reset args => .func (.binary ⟨.reset, hreset⟩) (fun i => ofResetUnion hreset hunion (args i))
  | .func .union args => .func (.binary ⟨.union, hunion⟩) (fun i => ofResetUnion hreset hunion (args i))

def toReset (hselected : selected = {.reset}) : Term selected Var → Reset.Term Var
  | .var j => .var j
  | .func (.binary _) args => .func .reset (fun i => toReset hselected (args i))

end Term

/- Validity of native selected terms keeps all valuation quantifiers. -/
def Valid {Role : Type u} (selected : Finset (Operation Role))
    (equation : Term selected ℕ × Term selected ℕ) : Prop :=
  ∀ valuation : ℕ → WinnerSet Role, equation.1.eval valuation = equation.2.eval valuation

namespace Reduction

variable {Role : Type u} (selected : Finset (Operation Role))

def resetUnion (hr : Operation.reset ∈ selected) (hu : Operation.union ∈ selected) (formula : Reductions.CNF) :
    Term selected ℕ × Term selected ℕ :=
  let e := Reductions.ResetUnion.equation formula
  (Term.ofResetUnion hr hu e.1, Term.ofResetUnion hr hu e.2)

def choiceUnion (a : Role) (ha : Operation.choice a ∈ selected) (hu : Operation.union ∈ selected)
    (formula : Reductions.CNF) : Term selected ℕ × Term selected ℕ :=
  let operations := Term.pairOperations (.choice a) .union ha hu
  let e := Reductions.RawPair.equation formula
  (Term.ofRawPair operations e.1, Term.ofRawPair operations e.2)

def twoChoices (a b : Role) (ha : Operation.choice a ∈ selected) (hb : Operation.choice b ∈ selected)
    (formula : Reductions.CNF) : Term selected ℕ × Term selected ℕ :=
  let operations := Term.pairOperations (.choice a) (.choice b) ha hb
  let e := Reductions.RawPair.twoOwnerEquation formula
  (Term.ofRawPair operations e.1, Term.ofRawPair operations e.2)

def resetChoice (a : Role) (ha : Operation.choice a ∈ selected) (hr : Operation.reset ∈ selected)
    (formula : Reductions.CNF) : Term selected ℕ × Term selected ℕ :=
  let operations := Term.pairOperations .reset (.choice a) hr ha
  let e := Reductions.ResetChoice.equation formula
  (Term.ofRawPair operations e.1, Term.ofRawPair operations e.2)

end Reduction
end KFOL.Raw

namespace KFOL.Raw

universe u v

variable {Role : Type u} {Var : Type v} {selected : Finset (Operation Role)}

def operationEquiv (selected : Finset (Operation Role)) :
    ((n : ℕ) × Symbol selected n) ≃ {operation // operation ∈ selected} where
  toFun operation := match operation with | ⟨_, .binary op⟩ => op
  invFun operation := ⟨2, .binary operation⟩
  left_inv operation := by rcases operation with ⟨n, symbol⟩; cases symbol; rfl
  right_inv _ := rfl

noncomputable instance operationFintype (selected : Finset (Operation Role)) :
    Fintype ((n : ℕ) × Symbol selected n) := Fintype.ofEquiv _ (operationEquiv selected).symm

end KFOL.Raw

namespace KFOL.Raw

universe u

/- The reduction selected from an arbitrary nontrivial raw signature uses
only its actual operations and introduces no abstraction hypothesis. -/
end KFOL.Raw

namespace KFOL.Raw

/-- The complete original binary equation language of a fixed selected raw
signature. Membership requires an exact decoding and independent validity. -/
noncomputable def Language {Role : Type} (selected : Finset (Operation Role)) : Set (List Bool) :=
  {word | ∃ equation : Term selected ℕ × Term selected ℕ,
    FiniteTermCode.encodeEquation (Symbol selected) equation = word ∧ Valid selected equation}

end KFOL.Raw

/-! Sparse-input reset DAG CNF reduction. -/

namespace KFOL.Circuit.ResetCNF

open KFOL.Reductions

def inputNames (formula : CNF) : List ℕ :=
  0 :: 1 :: (ResetUnion.support formula).flatMap
    (fun i => [ResetUnion.literalName (i, true), ResetUnion.literalName (i, false)])

def literalRef (formula : CNF) (literal : Literal) : ℕ := (inputNames formula).idxOf (ResetUnion.literalName literal)

def pairs (formula : CNF) : List (ℕ × ℕ) :=
  (ResetUnion.support formula).map (fun i => (literalRef formula (i, true), literalRef formula (i, false)))

def railRefs (formula : CNF) : List ℕ := (pairs formula).flatMap (fun p => [p.1, p.2])

def clauseRefs (formula : CNF) : List (List ℕ) := formula.map (fun C => C.map (literalRef formula))

def inputs (formula : CNF) : List (Gate Reset.Symbol ℕ) := (inputNames formula).map Gate.input

def baselineBuild (formula : CNF) : BuildResult Reset.Symbol ℕ := buildRightComb (railRefs formula) 0 (inputs formula)

def rightBuild (formula : CNF) : BuildResult Reset.Symbol ℕ :=
  buildConsistency (pairs formula) 1 (baselineBuild formula).output (baselineBuild formula).gates

def leftBuild (formula : CNF) : BuildResult Reset.Symbol ℕ :=
  buildCNF (clauseRefs formula) 1 0 (rightBuild formula).gates

def equation (formula : CNF) : Equation Reset.Symbol ℕ :=
  let left := emit (leftBuild formula).gates (Gate.reset (leftBuild formula).output (rightBuild formula).output)
  ⟨left.gates, left.output, (rightBuild formula).output⟩

def inputValue {M : Type*} (valuation : ℕ → M) (formula : CNF) (ref : ℕ) : M :=
  ((inputNames formula).map valuation).getD ref (valuation 0)

def baselineValue {M : Type*} [(Equational.language Reset.Symbol).Structure M]
    (valuation : ℕ → M) (formula : CNF) : M :=
  ((railRefs formula).map (inputValue valuation formula)).foldr (Reset.operation M) (valuation 0)

def rightValue {M : Type*} [(Equational.language Reset.Symbol).Structure M]
    (valuation : ℕ → M) (formula : CNF) : M :=
  ((pairs formula).map (fun p => Reset.operation M
    (Reset.operation M (valuation 1) (inputValue valuation formula p.1))
    (inputValue valuation formula p.2))).foldr (Reset.operation M) (baselineValue valuation formula)

def leftValue {M : Type*} [(Equational.language Reset.Symbol).Structure M]
    (valuation : ℕ → M) (formula : CNF) : M :=
  ((clauseRefs formula).map (fun clause => clause.map (inputValue valuation formula))).foldl
    (fun prior clause => (clause.map (Reset.operation M prior)).foldr (Reset.operation M) (valuation 0)) (valuation 1)

/- Actual shared-cache evaluation, in every reset-signature algebra and for
EVERY valuation. In particular, sharing never changes the clause recurrence. -/
end KFOL.Circuit.ResetCNF
namespace KFOL.Circuit.ResetCNF

open KFOL.Reductions

universe u

variable {Role : Type u}

noncomputable def clauseValue (root previous : WinnerSet Role) (literals : List (WinnerSet Role)) : WinnerSet Role :=
  (literals.map (WinnerSet.reset previous)).foldr WinnerSet.reset root

end KFOL.Circuit.ResetCNF
namespace KFOL.Circuit.ResetCNF

open KFOL.Reductions

universe u

variable {Role : Type u}

noncomputable def satisfyingStage (assignment : ℕ → Bool) : ℕ → Fin 3 :=
  Function.extend ResetUnion.literalName (fun literal => if assignment literal.1 = literal.2 then 1 else 0)
    (fun j => if j = 0 then 1 else 2)

noncomputable def satisfyingValuation (three : Fin 3 ↪ Role) (assignment : ℕ → Bool) (j : ℕ) : WinnerSet Role :=
  Reset.chainValue three (satisfyingStage assignment j)

end KFOL.Circuit.ResetCNF
namespace KFOL.Circuit

universe u v w

/- H(root,left,left) uses the SAME left ref twice. It does not copy a
previously constructed subgraph or expand its shared continuation. -/
end KFOL.Circuit

namespace KFOL.Circuit

universe u v w


end KFOL.Circuit

namespace KFOL.Circuit

universe u v

end KFOL.Circuit

namespace KFOL.Owner

/-- A selected owner family restricts the original owner-labelled syntax.
The outcome relation is equality, observational implication, or observational
equivalence; it is independent of the decision programs. -/
def Valid {Role : Type} (owners : Finset Role)
    (relation : WinnerSet Role → WinnerSet Role → Prop)
    (equation : Term Role ℕ × Term Role ℕ) : Prop :=
  equation.1.OwnersIn (fun r => r ∈ owners) ∧
  equation.2.OwnersIn (fun r => r ∈ owners) ∧
  ∀ valuation : ℕ → WinnerSet Role, relation (equation.1.eval valuation) (equation.2.eval valuation)

/-- Exact original owner-equation codes, rejecting every syntax that uses an
unselected owner as well as every malformed word. -/
noncomputable def Language {Role : Type}
    [Fintype ((n : ℕ) × Symbol Role n)] (owners : Finset Role)
    (relation : WinnerSet Role → WinnerSet Role → Prop) : Set (List Bool) :=
  {word | ∃ equation : Term Role ℕ × Term Role ℕ,
    FiniteTermCode.encodeEquation (Symbol Role) equation = word ∧ Valid owners relation equation}

end KFOL.Owner
