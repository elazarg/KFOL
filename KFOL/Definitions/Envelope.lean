module

public import KFOL.Definitions.CoreBasis

/-! # A flat permutation envelope of an arbitrary owned-choice algebra

There is one copy of the input algebra per role permutation and a common
absorbing element. Winner constants denote that element. All operations are
specified here independently of the identities the envelope will satisfy.
-/

@[expose] public section
namespace KFOL.Envelope
universe u v w
variable {Role : Type u} {M : Type v} {Var : Type w}

abbrev Carrier (Role : Type u) (M : Type v) := Option (Equiv.Perm Role × M)

open Classical in
/-- In one copy use the corresponding transported owner; different copies
have absorbing product. The extra element `none` absorbs every choice. -/
noncomputable def choice
    [(Equational.language (Equational.CoreSymbol Role)).Structure M]
    (r : Role) : Carrier Role M → Carrier Role M → Carrier Role M
  | some (g, x), some (h, y) =>
      if g = h then some (g, Core.operation (g⁻¹ r) x y) else none
  | _, _ => none

/-- Permutations act freely on the copy labels and fix the absorber. -/
def rename (p : Equiv.Perm Role) : Carrier Role M → Carrier Role M
  | none => none
  | some (g, x) => some (p * g, x)

@[instance_reducible] noncomputable def structureOf
    [(Equational.language (Equational.CoreSymbol Role)).Structure M] :
    (Equational.language (Equational.FullSymbol Role)).Structure (Carrier Role M) where
  funMap f args := match f with
    | .winner _ => none
    | .choice r => choice r (args 0) (args 1)
    | .rename p => rename p (args 0)
  RelMap r := nomatch r

@[instance_reducible] noncomputable def publicStructureOf
    [(Equational.language (Equational.CoreSymbol Role)).Structure M] :
    (Equational.language (Equational.PublicSymbol Role)).Structure (Carrier Role M) where
  funMap f args := match f with
    | .winner _ => none
    | .choice r => choice r (args 0) (args 1)
  RelMap r := nomatch r

/-- Native syntax interpreted in the independently specified envelope. -/
noncomputable def eval
    [(Equational.language (Equational.CoreSymbol Role)).Structure M]
    (valuation : Var → Carrier Role M) : KFOL.Term Role Var → Carrier Role M
  | .winner _ => none
  | .var j => valuation j
  | .choice r s t => choice r (eval valuation s) (eval valuation t)
  | .rename p t => rename p (eval valuation t)

/-- Replace an input by its copy permutation, or a winner constant when it
is the absorber. This is a syntactic substitution in the original language. -/
def decoration (r : Role) (valuation : Var → Carrier Role M) (j : Var) : KFOL.Term Role Var :=
  match valuation j with
  | none => .winner r
  | some (g, _) => .rename g (.var j)

/-- A core shadow with transported owners. The extra variable makes the
construction total even for nullary terms; purity excludes that case when
the shadow is used to reflect an envelope value. -/
def shadow (p : Equiv.Perm Role) : KFOL.Term Role Var →
    Equational.Term (Equational.CoreSymbol Role) (Option Var)
  | .winner _ => .var none
  | .var j => .var (some j)
  | .choice r s t => Core.choiceTerm (p r) (shadow p s) (shadow p t)
  | .rename q t => shadow (p * q) t

/-- Read the payload of an input; absent payloads use the explicit fallback. -/
def values (fallback : M) (valuation : Var → Carrier Role M) : Option Var → M
  | none => fallback
  | some j => match valuation j with
    | none => fallback
    | some (_, x) => x

end KFOL.Envelope
