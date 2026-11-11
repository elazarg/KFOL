module

public import KFOL.Definitions.Views
public import KFOL.Definitions.CoreFunctions
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Order.Minimal

/-! # Sourcewise prime guards for core operations

Passive statuses retain another owner's singleton or neutral ambiguity.
A guard excludes finitely many such singleton statuses. Its meaning and
primality are specified independently of term syntax.
-/

@[expose] public section

namespace KFOL.Core.Sources

universe u v

/-- A non-source input is either another owner's atom or neutral ambiguity. -/
inductive Passive {Role : Type u} (k : Role) where
  | atom (r : {r : Role // r ≠ k})
  | neutral
  deriving DecidableEq

instance {Role : Type u} (k : Role) : PartialOrder (Passive k) where
  le p q := q = .neutral ∨ p = q
  le_refl _ := Or.inr rfl
  le_trans _ _ _ hab hbc := hbc.elim Or.inl (fun h => h ▸ hab)
  le_antisymm _ _ hab hba := hab.elim
    (fun hb => hba.elim (fun ha => ha.trans hb.symm) Eq.symm) id

/-- Coordinate representation for finite enumeration of passive statuses. -/
def Passive.equivOption {Role : Type u} (k : Role) :
    Passive k ≃ Option {r : Role // r ≠ k} where
  toFun
    | .atom r => some r
    | .neutral => none
  invFun
    | some r => .atom r
    | none => .neutral
  left_inv p := by cases p <;> rfl
  right_inv p := by cases p <;> rfl

noncomputable instance {Role : Type u} [Fintype Role] (k : Role) : Fintype (Passive k) := by
  classical
  exact Fintype.ofEquiv _ (Passive.equivOption k).symm

/-- Read only the other-owner singleton tests. Presence of k is erased. -/
noncomputable def passive {Role : Type u} (k : Role) (A : WinnerSet Role) : Passive k :=
  match WinnerSet.view k A with
  | .other r => .atom r
  | .possible | .impossible => .neutral

/-- Canonical non-source values, all omitting the possible winner k. -/
noncomputable def representative {Role : Type u} (three : Fin 3 ↪ Role) (k : Role) :
    Passive k → WinnerSet Role
  | .atom r => WinnerSet.singleton r.val
  | .neutral => PlayerView.representative three k .impossible

/-- Status choices for the positions other than the distinguished source. -/
abbrev Pattern {Role : Type u} (k : Role) {Var : Type v} (j : Var) :=
  {i : Var // i ≠ j} → Passive k

/-- All isolated-source observations needed to determine a core operation. -/
abbrev ProbeIndex (Role : Type u) (Var : Type v) := Σ k : Role, Σ j : Var, Pattern k j

/-- Extract the passive statuses away from one source. -/
noncomputable def pattern {Role : Type u} (k : Role) {Var : Type v} (j : Var)
    (v : Var → WinnerSet Role) : Pattern k j := fun i => passive k (v i.val)

/-- Isolate one source of k; every other input has no possible k. -/
noncomputable def probe {Role : Type u} (three : Fin 3 ↪ Role) (k : Role)
    {Var : Type v} (j : Var) (p : Pattern k j) : Var → WinnerSet Role := by
  classical
  exact fun i => if h : i = j then WinnerSet.singleton k
    else representative three k (p ⟨i, h⟩)

/-- A literal forbids a specified non-source input from being another atom. -/
abbrev Literal {Role : Type u} (k : Role) {Var : Type v} (j : Var) :=
  {i : Var // i ≠ j} × {r : Role // r ≠ k}

abbrev Guard {Role : Type u} (k : Role) {Var : Type v} (j : Var) := Finset (Literal k j)

/-- A guard allows all neutral inputs and the atoms not explicitly excluded. -/
def Enabled {Role : Type u} {k : Role} {Var : Type v} {j : Var}
    (g : Guard k j) (p : Pattern k j) : Prop := ∀ a ∈ g, p a.1 ≠ .atom a.2

/-- Every pattern in the guard's box satisfies the coefficient predicate. -/
def Sound {Role : Type u} {k : Role} {Var : Type v} {j : Var}
    (F : Pattern k j → Prop) (g : Guard k j) : Prop := ∀ p, Enabled g p → F p

/-- All minimal sufficient exclusion guards, rather than a chosen cover. -/
def Prime {Role : Type u} {k : Role} {Var : Type v} {j : Var}
    (F : Pattern k j → Prop) (g : Guard k j) : Prop := Minimal (Sound F) g

/-- Canonical prime guards for the isolated-source coefficient of an operation. -/
noncomputable def normalForm {Role : Type u} [Fintype Role] {Var : Type v} [Fintype Var]
    (three : Fin 3 ↪ Role) (f : (Var → WinnerSet Role) → WinnerSet Role)
    (k : Role) (j : Var) : Finset (Guard k j) := by
  classical
  exact Finset.univ.filter (Prime (fun p => k ∈ (f (probe three k j p)).val))

/-- Interpret a source-guard family directly; arbitrary families need not
produce nonempty values or be jointly realizable by a core term. -/
def meaning {Role : Type u} {Var : Type v}
    (G : ∀ (k : Role) (j : Var), Finset (Guard k j)) (v : Var → WinnerSet Role) : Set Role :=
  {k | ∃ j, k ∈ (v j).val ∧ ∃ g ∈ G k j, Enabled g (pattern k j v)}

/-- The monotone predicate described by a guard family at each source. -/
def coefficients {Role : Type u} {Var : Type v}
    (G : ∀ (k : Role) (j : Var), Finset (Guard k j))
    (k : Role) (j : Var) (p : Pattern k j) : Prop := ∃ g ∈ G k j, Enabled g p

/-- A presentation contains all and only its own prime sufficient guards. -/
def Canonical {Role : Type u} {Var : Type v}
    (G : ∀ (k : Role) (j : Var), Finset (Guard k j)) : Prop :=
  ∀ k j g, g ∈ G k j ↔ Prime (coefficients G k j) g

/-- A true observation imposes no restriction. A false observation forbids
only its observer, without prescribing any other winner. -/
noncomputable def allowance {Role : Type u} {Var : Type v}
    (three : Fin 3 ↪ Role) (F : ∀ (k : Role) (j : Var), Pattern k j → Prop)
    (q : ProbeIndex Role Var) : WinnerSet Role := by
  classical
  exact if F q.1 q.2.1 q.2.2 then ⟨Set.univ, ⟨three 0, Set.mem_univ _⟩⟩
    else representative three q.1 .neutral

/-- Atomic cuts on the source probes, with upper bounds determined only by
negative observations. No completed operation table is supplied. -/
noncomputable def compatibilitySystem {Role : Type u} {Var : Type v}
    (three : Fin 3 ↪ Role) (F : ∀ (k : Role) (j : Var), Pattern k j → Prop) :
    FiniteHorn.System (Cuts.Fact Role (ProbeIndex Role Var)) :=
  Cuts.system (fun q => probe three q.1 q.2.1 q.2.2) (allowance three F)

/-- Delete precisely the source observations that have no joint bounded witness.
This definition uses finite Horn rules and contains no quantifier over terms. -/
noncomputable def interior {Role : Type u} [Fintype Role] {Var : Type v} [Fintype Var]
    (three : Fin 3 ↪ Role) (F : ∀ (k : Role) (j : Var), Pattern k j → Prop)
    (k : Role) (j : Var) (p : Pattern k j) : Prop := by
  classical
  exact (⟨fun _ => .target, ⟨k, j, p⟩, k⟩ : Cuts.Fact Role (ProbeIndex Role Var)) ∈
    FiniteHorn.saturate (compatibilitySystem three F)

/-- There is a positive observation, and each positive observation has a
bounded witness in the one shared finite Horn system. -/
noncomputable def Compatible {Role : Type u} [Fintype Role] {Var : Type v} [Fintype Var]
    (three : Fin 3 ↪ Role) (F : ∀ (k : Role) (j : Var), Pattern k j → Prop) : Prop := by
  classical
  exact (∃ k j p, F k j p) ∧ ∀ k j p, F k j p → interior three F k j p

/-- The intrinsic joint-realizability criterion for canonical source families. -/
noncomputable def Admissible {Role : Type u} [Fintype Role] {Var : Type v} [Fintype Var]
    (three : Fin 3 ↪ Role) (G : ∀ (k : Role) (j : Var), Finset (Guard k j)) : Prop :=
  Canonical G ∧ Compatible three (coefficients G)

end KFOL.Core.Sources
