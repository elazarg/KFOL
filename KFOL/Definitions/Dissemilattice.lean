module

public import KFOL.Definitions.Equational
public import KFOL.Definitions.Public

/-! # The raw one-owner choice/union signature and its seven displayed laws -/

@[expose] public section

namespace KFOL.Dissemilattice

universe u v

/-- Two binary operations, with no absorption laws or constants built in. -/
inductive Symbol : ℕ → Type
  | join : Symbol 2
  | mul : Symbol 2

abbrev Term (Var : Type v) := Equational.Term Symbol Var

/-- The actual join getter in an arbitrary model of this signature. -/
def add {M : Type u} [(Equational.language Symbol).Structure M] (x y : M) : M :=
  FirstOrder.Language.Structure.funMap (L := Equational.language Symbol) .join
    (fun i => if i = 0 then x else y)

/-- The second owned operation; its semilattice order is independent of join. -/
def mul {M : Type u} [(Equational.language Symbol).Structure M] (x y : M) : M :=
  FirstOrder.Language.Structure.funMap (L := Equational.language Symbol) .mul
    (fun i => if i = 0 then x else y)

def joinTerm {Var : Type v} (s t : Term Var) : Term Var :=
  .func .join (fun i => if i = 0 then s else t)
def mulTerm {Var : Type v} (s t : Term Var) : Term Var :=
  .func .mul (fun i => if i = 0 then s else t)

/-- Exactly the seven laws of meet-distributive bisemilattices. The two
operations are semilattices and multiplication distributes over join. -/
structure Laws {M : Type u} (add mul : M → M → M) : Prop where
  add_idem (x : M) : add x x = x
  add_comm (x y : M) : add x y = add y x
  add_assoc (x y z : M) : add (add x y) z = add x (add y z)
  mul_idem (x : M) : mul x x = x
  mul_comm (x y : M) : mul x y = mul y x
  mul_assoc (x y z : M) : mul (mul x y) z = mul x (mul y z)
  mul_add (x y z : M) : mul x (add y z) = add (mul x y) (mul x z)

/-- The literal finite-arity equations, including harmless unused slots in
the unary and binary laws. Actual term variables keep their usual semantics. -/
def basisAxiom (i : Fin 7) : Equational.Identity Symbol :=
  let x : Term (Fin 3) := .var 0
  let y : Term (Fin 3) := .var 1
  let z : Term (Fin 3) := .var 2
  let pair := match i.val with
    | 0 => (joinTerm x x,x)
    | 1 => (joinTerm x y,joinTerm y x)
    | 2 => (joinTerm (joinTerm x y) z,joinTerm x (joinTerm y z))
    | 3 => (mulTerm x x,x)
    | 4 => (mulTerm x y,mulTerm y x)
    | 5 => (mulTerm (mulTerm x y) z,mulTerm x (mulTerm y z))
    | _ => (mulTerm x (joinTerm y z),joinTerm (mulTerm x y) (mulTerm x z))
  ⟨3,pair.1,pair.2⟩

/-- The presented theory is listed independently of semantic validity. -/
def theory : Equational.Theory Symbol := Set.range basisAxiom

/-- Interpret the exact raw one-owner fragment of the existing winner algebra. -/
@[instance_reducible] noncomputable def winnerStructure {Role : Type u} (owner : Role) :
    (Equational.language Symbol).Structure (WinnerSet Role) where
  funMap sym args := match sym with
    | .join => (args 0).union (args 1)
    | .mul => WinnerSet.choice owner (args 0) (args 1)
  RelMap rel := nomatch rel

/-- The three-element generator: join order B<N<P and multiplication order
N<P<B. The two orders are deliberately not identified. -/
inductive Three where
  | b | n | p
  deriving DecidableEq, Repr

namespace Three

def add : Three → Three → Three
  | .p, _ | _, .p => .p
  | .n, _ | _, .n => .n
  | .b, .b => .b

def mul : Three → Three → Three
  | .b, _ | _, .b => .b
  | .p, _ | _, .p => .p
  | .n, .n => .n

@[instance_reducible] def structureOf : (Equational.language Symbol).Structure Three where
  funMap sym args := match sym with
    | .join => add (args 0) (args 1)
    | .mul => mul (args 0) (args 1)
  RelMap rel := nomatch rel

end Three

end KFOL.Dissemilattice
