module

public import KFOL.Definitions.CoreBasis
public import Mathlib.Data.Fintype.Powerset

/-! # The atomic quotient and its displayed finite-basis laws

`none` is the single ambiguity value and `some r` is the owner atom.
Join and reset remain terms in the original owned-choice signature.
-/

@[expose] public section

namespace KFOL.Core.AtomicBasis

universe u v w

abbrev Carrier (Role : Type u) := Option Role

def choice {Role : Type u} [DecidableEq Role] (r : Role)
    (x y : Carrier Role) : Carrier Role :=
  if x = some r ∨ y = some r then some r else if x = y then x else none

@[instance_reducible] def structureOf (Role : Type u) [DecidableEq Role] :
    (Equational.language (Equational.CoreSymbol Role)).Structure (Carrier Role) where
  funMap f args := match f with
    | .choice r => choice r (args 0) (args 1)
  RelMap r := nomatch r

/-- The original winner quotient, with all nonsingletons identified. -/
noncomputable def collapse {Role : Type u} (A : WinnerSet Role) : Carrier Role := by
  classical
  exact if h : ∃ r, A = WinnerSet.singleton r then some h.choose else none

/-- The two-element owner image: its own operation is OR, the others AND. -/
@[instance_reducible] def booleanStructure {Role : Type u} [DecidableEq Role] (i : Role) :
    (Equational.language (Equational.CoreSymbol Role)).Structure Bool where
  funMap f args := match f with
    | .choice r => if r = i then args 0 || args 1 else args 0 && args 1
  RelMap r := nomatch r

/-- Reset expanded in the core signature, with a specified enumeration. -/
def resetTerm {Role : Type u} {Var : Type v} (three : Fin 3 ↪ Role) (roles : List Role)
    (s t : Equational.Term (Equational.CoreSymbol Role) Var) :
    Equational.Term (Equational.CoreSymbol Role) Var :=
  roles.foldl (fun acc r => choiceTerm r t acc) (unionTerm three s t)

def reset {Role : Type u} {M : Type v}
    [(Equational.language (Equational.CoreSymbol Role)).Structure M]
    (three : Fin 3 ↪ Role) (roles : List Role) (x y : M) : M :=
  roles.foldl (fun acc r => operation r y acc) (join three x y)

/-- The displayed three-variable lifting laws, before atomic collapse. -/
structure LiftingLaws {Role : Type u} {M : Type v}
    (add : M → M → M) (op : Role → M → M → M) : Prop where
  add_idem (x : M) : add x x = x
  add_comm (x y : M) : add x y = add y x
  add_assoc (x y z : M) : add (add x y) z = add x (add y z)
  op_idem (i : Role) (x : M) : op i x x = x
  op_comm (i : Role) (x y : M) : op i x y = op i y x
  op_assoc (i : Role) (x y z : M) : op i (op i x y) z = op i x (op i y z)
  op_add (i : Role) (x y z : M) : op i x (add y z) = add (op i x y) (op i x z)
  cover (i j : Role) (hij : i ≠ j) (x y : M) : add (op i x y) (op j x y) = add x y
  birkhoff (i j : Role) (hij : i ≠ j) (x y : M) : op i x (op j x y) = op j x (op i x y)

/-- An unordered pair of distinct owners; each pair contributes two laws. -/
abbrev OwnerPair (Role : Type u) := {s : Finset Role // s.card = 2}

noncomputable def pairFirst {Role : Type u} (p : OwnerPair Role) : Role := by
  classical
  exact (Finset.card_eq_two.mp p.property).choose

noncomputable def pairSecond {Role : Type u} (p : OwnerPair Role) : Role := by
  classical
  exact (Finset.card_eq_two.mp p.property).choose_spec.choose

/-- Three join laws, four laws per owner, two per owner pair, and reset. -/
abbrev BasisIndex (Role : Type u) := (Fin 3 ⊕ Role × Fin 4) ⊕ (OwnerPair Role × Fin 2 ⊕ Unit)

/-- The literal displayed equations, all in the original core signature. -/
noncomputable def basisAxiom {Role : Type u} (three : Fin 3 ↪ Role) (roles : List Role)
    (index : BasisIndex Role) : Equational.Identity (Equational.CoreSymbol Role) :=
  let x : Equational.Term (Equational.CoreSymbol Role) (Fin 3) := .var 0
  let y : Equational.Term (Equational.CoreSymbol Role) (Fin 3) := .var 1
  let z : Equational.Term (Equational.CoreSymbol Role) (Fin 3) := .var 2
  let plus := unionTerm three
  let pair := match index with
    | .inl (.inl k) => match k.val with
      | 0 => (plus x x, x)
      | 1 => (plus x y, plus y x)
      | _ => (plus (plus x y) z, plus x (plus y z))
    | .inl (.inr (i, k)) => match k.val with
      | 0 => (choiceTerm i x x, x)
      | 1 => (choiceTerm i x y, choiceTerm i y x)
      | 2 => (choiceTerm i (choiceTerm i x y) z, choiceTerm i x (choiceTerm i y z))
      | _ => (choiceTerm i x (plus y z), plus (choiceTerm i x y) (choiceTerm i x z))
    | .inr (.inl (p, k)) =>
      let i := pairFirst p
      let j := pairSecond p
      if k.val = 0 then (plus (choiceTerm i x y) (choiceTerm j x y), plus x y)
      else (choiceTerm i x (choiceTerm j x y), choiceTerm j x (choiceTerm i x y))
    | .inr (.inr _) => (resetTerm three roles x y, y)
  ⟨3, pair.1, pair.2⟩

noncomputable def theory {Role : Type u} (three : Fin 3 ↪ Role) (roles : List Role) :
    Equational.Theory (Equational.CoreSymbol Role) := Set.range (basisAxiom three roles)

/-- Near-unanimity is a semantic property, independent of its construction. -/
def NearUnanimity {Role : Type u} [DecidableEq Role] {n : ℕ}
    (t : Equational.Term (Equational.CoreSymbol Role) (Fin n)) : Prop :=
  letI := structureOf Role
  ∀ (x y : Carrier Role) (j : Fin n),
    t.realize (fun i => if i = j then y else x) = x

/-- The threshold profile accepting at most one false input. -/
noncomputable def almostAll {Var : Type v} (v : Var → Bool) : Bool := by
  classical
  exact decide (∀ i j, v i = false → v j = false → i = j)

end KFOL.Core.AtomicBasis
