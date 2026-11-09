module

public import KFOL.Definitions.Equational

/-! # Native algebras and Boolean profiles for the core basis obstruction

The carrier and operations are given by explicit tables, independently of
variety membership, local generation, or the identities they will separate.
-/

@[expose] public section

namespace KFOL.Core

universe u v

/-- The native algebra has one atom per available role, then a lower and an
upper ambiguity marker. Taking `Role` to be a subtype restricts its atoms. -/
inductive Native (Role : Type u) where
  | atom (r : Role)
  | lower
  | upper
  deriving DecidableEq

namespace Native

variable {Role : Type u}

/-- Join on incomparable atoms below the two ambiguity markers. -/
def join [DecidableEq Role] (x y : Native Role) : Native Role :=
  if x = y then x else if x = .upper ∨ y = .upper then .upper else .lower

/-- Each owner atom absorbs; all other products are native join. -/
def choice [DecidableEq Role] (r : Role) (x y : Native Role) : Native Role :=
  if x = .atom r ∨ y = .atom r then .atom r else join x y

/-- The native algebra has exactly the original owned-choice signature. -/
@[instance_reducible] def structureOf [DecidableEq Role] :
    (Equational.language (Equational.CoreSymbol Role)).Structure (Native Role) where
  funMap f args := match f with
    | .choice r => choice r (args 0) (args 1)
  RelMap r := nomatch r

/-- One omission excludes either an atom or the upper marker. -/
def omitted : Option Role → Native Role
  | none => .upper
  | some r => .atom r

/-- Identify the two native ambiguity markers, keeping every atom. -/
def collapseUpper : Native Role → Native Role
  | .atom r => .atom r
  | .lower | .upper => .lower

/-- Collapse all ambiguity to the lower marker while retaining singletons. -/
noncomputable def atomicQuotient (A : WinnerSet Role) : Native Role := by
  classical
  exact if h : ∃ r, A = WinnerSet.singleton r then .atom h.choose else .lower

/-- The full atomic quotient or one observer quotient, depending on the
omitted native value. This is defined without a homomorphism assumption. -/
noncomputable def quotient (drop : Option Role) (A : WinnerSet Role) : Native Role := by
  classical
  exact match drop with
    | none => atomicQuotient A
    | some r => if r ∈ A.val then .upper else atomicQuotient A

end Native

/-- Read an owned binary operation from the original generic core structure. -/
def operation {Role : Type u} {M : Type v}
    [(Equational.language (Equational.CoreSymbol Role)).Structure M]
    (r : Role) (x y : M) : M :=
  FirstOrder.Language.Structure.funMap (L := Equational.language (Equational.CoreSymbol Role))
    (.choice r) (fun i => if i = 0 then x else y)

/-- The derived neutral join, without extending the core signature. -/
def join {Role : Type u} {M : Type v}
    [(Equational.language (Equational.CoreSymbol Role)).Structure M]
    (three : Fin 3 ↪ Role) (x y : M) : M :=
  operation (three 2) (operation (three 0) x y) (operation (three 1) x y)

/-- The rigid upper clone adds one point. On old values it keeps the
original operations; the new point follows e but survives whenever e does. -/
noncomputable def upperChoice {Role : Type u} {M : Type v}
    [(Equational.language (Equational.CoreSymbol Role)).Structure M]
    (e : M) (r : Role) : Option M → Option M → Option M := by
  classical
  exact fun x y => match x, y with
    | some c, some d => some (operation r c d)
    | none, none => none
    | none, some c | some c, none =>
      if operation r e c = e then none else some (operation r e c)

/-- The upper clone has precisely the original owned-operation signature. -/
@[instance_reducible] noncomputable def upperStructure {Role : Type u} {M : Type v}
    [(Equational.language (Equational.CoreSymbol Role)).Structure M]
    (e : M) : (Equational.language (Equational.CoreSymbol Role)).Structure (Option M) where
  funMap f args := match f with
    | .choice r => upperChoice e r (args 0) (args 1)
  RelMap r := nomatch r

/-- The binary constructor in the generic core signature. -/
def choiceTerm {Role : Type u} {Var : Type v} (r : Role)
    (s t : Equational.Term (Equational.CoreSymbol Role) Var) :
    Equational.Term (Equational.CoreSymbol Role) Var :=
  .func (.choice r) (fun i => if i = 0 then s else t)

/-- The derived union uses three distinct owners, without adding a symbol
or extra variables to the signature. -/
def unionTerm {Role : Type u} {Var : Type v} (three : Fin 3 ↪ Role)
    (s t : Equational.Term (Equational.CoreSymbol Role) Var) :
    Equational.Term (Equational.CoreSymbol Role) Var :=
  choiceTerm (three 2) (choiceTerm (three 0) s t) (choiceTerm (three 1) s t)

/-- Nonempty owner-exhaustion sum. The first owner's summand is repeated as
the fold base; idempotence makes this the ordinary sum when every role is listed. -/
def exhaustionRight {Role : Type u} (three : Fin 3 ↪ Role) (roles : List Role) :
    Equational.Term (Equational.CoreSymbol Role) (Option Role) :=
  roles.foldr (fun r acc => unionTerm three (choiceTerm r (.var none) (.var (some r))) acc)
    (choiceTerm (three 0) (.var none) (.var (some (three 0))))

/-- The core-syntax owner-exhaustion equation with exactly K+1 declared
variables. The operation signature still contains only owned choices. -/
noncomputable def exhaustionIdentity {Role : Type u} [Fintype Role] (three : Fin 3 ↪ Role) :
    Equational.Identity (Equational.CoreSymbol Role) where
  arity := Fintype.card (Option Role)
  lhs := (unionTerm three (.var none)
    (exhaustionRight three (Finset.univ.toList))).relabel (Fintype.equivFin (Option Role))
  rhs := (exhaustionRight three (Finset.univ.toList)).relabel (Fintype.equivFin (Option Role))

/-- Role i reads its own choices as disjunction and all other owners as
conjunction. The input is an arbitrary Boolean valuation. -/
def profile {Role : Type u} [DecidableEq Role] {Var : Type v} (i : Role)
    (valuation : Var → Bool) : Equational.Term (Equational.CoreSymbol Role) Var → Bool
  | .var x => valuation x
  | .func (.choice r) args =>
    if r = i then profile i valuation (args 0) || profile i valuation (args 1)
    else profile i valuation (args 0) && profile i valuation (args 1)

end KFOL.Core
