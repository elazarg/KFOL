module

public import KFOL.Definitions.Dissemilattice
public import KFOL.Definitions.TwoPlayers

/-! # The bounded Kleene signature and its literal finite equational presentation -/

@[expose] public section

namespace KFOL.TwoPlayers.Kleene

universe u v

inductive Symbol : Nat → Type
  | bot : Symbol 0
  | top : Symbol 0
  | neg : Symbol 1
  | join : Symbol 2
  | meet : Symbol 2

abbrev Term (Var : Type v) := Equational.Term Symbol Var

@[instance_reducible] def structureOf {M : Type u} (zero one : M)
    (plus times : M → M → M) (neg : M → M) : (Equational.language Symbol).Structure M where
  funMap f args := match f with
    | .bot => zero
    | .top => one
    | .neg => neg (args 0)
    | .join => plus (args 0) (args 1)
    | .meet => times (args 0) (args 1)
  RelMap r := nomatch r

def botTerm {Var : Type v} : Term Var := .func .bot Fin.elim0
def topTerm {Var : Type v} : Term Var := .func .top Fin.elim0
def negTerm {Var : Type v} (t : Term Var) : Term Var := .func .neg (fun _ => t)
def joinTerm {Var : Type v} (s t : Term Var) : Term Var :=
  .func .join (fun i => if i = 0 then s else t)
def meetTerm {Var : Type v} (s t : Term Var) : Term Var :=
  .func .meet (fun i => if i = 0 then s else t)

/-- Read each operation directly from an arbitrary structure in this signature. -/
def operationZero (M : Type u) [(Equational.language Symbol).Structure M] : M :=
  FirstOrder.Language.Structure.funMap (L := Equational.language Symbol) .bot Fin.elim0

def operationOne (M : Type u) [(Equational.language Symbol).Structure M] : M :=
  FirstOrder.Language.Structure.funMap (L := Equational.language Symbol) .top Fin.elim0

def operationNeg (M : Type u) [(Equational.language Symbol).Structure M] (x : M) : M :=
  FirstOrder.Language.Structure.funMap (L := Equational.language Symbol) .neg (fun _ => x)

def operationJoin (M : Type u) [(Equational.language Symbol).Structure M] (x y : M) : M :=
  FirstOrder.Language.Structure.funMap (L := Equational.language Symbol) .join (fun i => if i = 0 then x else y)

def operationMeet (M : Type u) [(Equational.language Symbol).Structure M] (x y : M) : M :=
  FirstOrder.Language.Structure.funMap (L := Equational.language Symbol) .meet (fun i => if i = 0 then x else y)

/-- Bounded distributive lattice laws together with involution, De Morgan,
and the Kleene inequality, all stated on the raw operations. -/
structure Laws {M : Type u} (zero one : M) (plus times : M → M → M)
    (neg : M → M) : Prop where
  semilattice : Dissemilattice.Laws plus times
  add_mul (x y : M) : plus x (times x y) = x
  mul_add (x y : M) : times x (plus x y) = x
  zero_add (x : M) : plus zero x = x
  one_mul (x : M) : times one x = x
  neg_neg (x : M) : neg (neg x) = x
  neg_mul (x y : M) : neg (times x y) = plus (neg x) (neg y)
  neg_zero : neg zero = one
  kleene (x y : M) : plus (times x (neg x)) (plus y (neg y)) = plus y (neg y)

/-- The fifteen literal equations, with three declared independent variables.
No semantic validity or derivability condition is used in this listing. -/
def basisAxiom (i : Fin 15) : Equational.Identity Symbol :=
  let x : Term (Fin 3) := .var 0
  let y : Term (Fin 3) := .var 1
  let z : Term (Fin 3) := .var 2
  let pair := match i.val with
    | 0 => (joinTerm x x,x)
    | 1 => (joinTerm x y,joinTerm y x)
    | 2 => (joinTerm (joinTerm x y) z,joinTerm x (joinTerm y z))
    | 3 => (meetTerm x x,x)
    | 4 => (meetTerm x y,meetTerm y x)
    | 5 => (meetTerm (meetTerm x y) z,meetTerm x (meetTerm y z))
    | 6 => (meetTerm x (joinTerm y z),joinTerm (meetTerm x y) (meetTerm x z))
    | 7 => (joinTerm x (meetTerm x y),x)
    | 8 => (meetTerm x (joinTerm x y),x)
    | 9 => (joinTerm botTerm x,x)
    | 10 => (meetTerm topTerm x,x)
    | 11 => (negTerm (negTerm x),x)
    | 12 => (negTerm (meetTerm x y),joinTerm (negTerm x) (negTerm y))
    | 13 => (negTerm botTerm,topTerm)
    | _ => (joinTerm (meetTerm x (negTerm x)) (joinTerm y (negTerm y)),joinTerm y (negTerm y))
  ⟨3,pair.1,pair.2⟩

def basis : Equational.Theory Symbol := Set.range basisAxiom

@[instance_reducible] def threeStructure : (Equational.language Symbol).Structure (Fin 3) :=
  structureOf 0 2 max min Fin.rev

/-- The canonical bounded Kleene signature uses the two actual owned choices,
actual winner constants and actual role transposition. -/
@[instance_reducible] noncomputable def winnerStructure {Role : Type u} (e : Fin 2 ≃ Role) :
    (Equational.language Symbol).Structure (WinnerSet Role) := by
  classical
  exact structureOf (WinnerSet.singleton (e 1)) (WinnerSet.singleton (e 0))
    (WinnerSet.choice (e 0)) (WinnerSet.choice (e 1))
    (WinnerSet.rename (Equiv.swap (e 0) (e 1)))

end KFOL.TwoPlayers.Kleene
