module

public import KFOL.Definitions.Core
public import Mathlib.ModelTheory.Substructures
public import Mathlib.ModelTheory.Quotients

/-!
# Signatures, identities and equational logic

The generic syntax, realization, homomorphisms, subalgebras and quotients are
mathlib's. A signature records only finitary operations, with no relation
symbols. Structure instances are supplied locally, so different algebras on
one carrier do not install competing global instances.
-/

@[expose] public section

namespace KFOL.Equational

universe u v w w'

/-- The relation-free mathlib language associated with a finitary signature. -/
abbrev language (σ : ℕ → Type u) : FirstOrder.Language.{u, 0} := ⟨σ, fun _ => Empty⟩

/-- Generic terms reuse mathlib's syntax and structural substitution. -/
abbrev Term (σ : ℕ → Type u) (Var : Type v) := (language σ).Term Var

/-- An identity has an explicit finite arity, including arity zero. -/
structure Identity (σ : ℕ → Type u) where
  arity : ℕ
  lhs : Term σ (Fin arity)
  rhs : Term σ (Fin arity)

namespace Identity

variable {σ : ℕ → Type u}

/-- Validity is equality at every valuation, independent of derivation. -/
def Holds (e : Identity σ) (M : Type w) [(language σ).Structure M] : Prop :=
  ∀ valuation : Fin e.arity → M, e.lhs.realize valuation = e.rhs.realize valuation

/-- Count distinct variables on both sides, rather than the declared arity. -/
def support (e : Identity σ) : Finset (Fin e.arity) := e.lhs.varFinset ∪ e.rhs.varFinset

def variableCount (e : Identity σ) : ℕ := e.support.card

end Identity

/-- A theory may contain identities of unbounded arity. -/
abbrev Theory (σ : ℕ → Type u) := Set (Identity σ)

/-- Satisfaction of a theory. This auxiliary predicate also permits empty
structures; nonemptiness is explicit in variety membership and paper models. -/
def Models {σ : ℕ → Type u} (T : Theory σ) (M : Type w) [(language σ).Structure M] : Prop :=
  ∀ e ∈ T, e.Holds M

/-- The entire identity theory of one algebra. -/
def theoryOf (σ : ℕ → Type u) (M : Type w) [(language σ).Structure M] : Theory σ :=
  {e | e.Holds M}

/-- Equational variety membership, with a nonempty target algebra. This is
satisfaction of the generator's identities, not a definition by an HSP certificate. -/
def InVariety (σ : ℕ → Type u) (A : Type w) (B : Type w')
    [(language σ).Structure A] [(language σ).Structure B] : Prop :=
  Nonempty B ∧ ∀ e : Identity σ, e.Holds A → e.Holds B

/-- Equational derivation is defined independently of semantic validity.
The axiom rule instantiates a finite-arity identity at arbitrary terms. -/
inductive Derives {σ : ℕ → Type u} (T : Theory σ) :
    {Var : Type v} → Term σ Var → Term σ Var → Prop
  | of_mem {Var : Type v} (e : Identity σ) (he : e ∈ T)
      (replacement : Fin e.arity → Term σ Var) :
      Derives T (e.lhs.subst replacement) (e.rhs.subst replacement)
  | refl {Var : Type v} (t : Term σ Var) : Derives T t t
  | symm {Var : Type v} {s t : Term σ Var} : Derives T s t → Derives T t s
  | trans {Var : Type v} {s t r : Term σ Var} :
      Derives T s t → Derives T t r → Derives T s r
  | func {Var : Type v} {n : ℕ} (f : σ n) (s t : Fin n → Term σ Var) :
      (∀ i, Derives T (s i) (t i)) → Derives T (.func f s) (.func f t)
  | subst {Var Var' : Type v} {s t : Term σ Var} (h : Derives T s t)
      (replacement : Var → Term σ Var') :
      Derives T (s.subst replacement) (t.subst replacement)

/-- A basis has exactly the identities of the algebra as its derivable
consequences. Soundness and completeness connect this with arbitrary models. -/
def IsBasis {σ : ℕ → Type u} (A : Type w) [(language σ).Structure A] (T : Theory σ) : Prop :=
  ∀ e : Identity σ, e.Holds A ↔ Derives T e.lhs e.rhs

def HasFiniteBasis (σ : ℕ → Type u) (A : Type w) [(language σ).Structure A] : Prop :=
  ∃ T : Theory σ, T.Finite ∧ IsBasis A T

/-- The bound concerns actual supports, including zero-variable identities. -/
def HasVariableBound {σ : ℕ → Type u} (T : Theory σ) (n : ℕ) : Prop :=
  ∀ e ∈ T, e.variableCount ≤ n

/-- Pointwise operations on an arbitrary dependent product. It is a named
structure value, not a global instance on every function type. -/
@[instance_reducible] def productStructure {σ : ℕ → Type u} {Index : Type v} (M : Index → Type w)
    [∀ i, (language σ).Structure (M i)] : (language σ).Structure (∀ i, M i) where
  funMap f args i := FirstOrder.Language.Structure.funMap (L := language σ) f (fun j => args j i)
  RelMap r := nomatch r

/-- The free syntactic algebra, before quotienting by derivability. -/
@[instance_reducible] def termStructure (σ : ℕ → Type u) (Var : Type v) :
    (language σ).Structure (Term σ Var) where
  funMap f args := .func f args
  RelMap r := nomatch r

/-- Derivability as an equivalence relation on the term algebra. -/
def derivationSetoid {σ : ℕ → Type u} (T : Theory σ) (Var : Type v) : Setoid (Term σ Var) where
  r := Derives T
  iseqv := ⟨Derives.refl, Derives.symm, Derives.trans⟩

/-- Function congruence makes the independent derivation relation a congruence
on the term algebra. Mathlib constructs the resulting quotient operations. -/
@[instance_reducible] def termPrestructure {σ : ℕ → Type u} (T : Theory σ) (Var : Type v) :
    (language σ).Prestructure (derivationSetoid T Var) where
  toStructure := termStructure σ Var
  fun_equiv := by
    intro n f x y h
    exact Derives.func f x y h
  rel_equiv := by intro n r; exact nomatch r

/-- Every symbol of the public language, with its actual arity. -/
inductive FullSymbol (Role : Type u) : ℕ → Type u
  | winner (r : Role) : FullSymbol Role 0
  | choice (r : Role) : FullSymbol Role 2
  | rename (p : Equiv.Perm Role) : FullSymbol Role 1

/-- The core signature contains only the owned binary operations. -/
inductive CoreSymbol (Role : Type u) : ℕ → Type u
  | choice (r : Role) : CoreSymbol Role 2

/-- Public choice with named winners, without internal role permutations. -/
inductive PublicSymbol (Role : Type u) : ℕ → Type u
  | winner (r : Role) : PublicSymbol Role 0
  | choice (r : Role) : PublicSymbol Role 2

/-- The original public signature with winner constants and owned choices. -/
@[instance_reducible] noncomputable def publicStructure (Role : Type u) :
    (language (PublicSymbol Role)).Structure (WinnerSet Role) where
  funMap f args := match f with
    | .winner r => WinnerSet.singleton r
    | .choice r => WinnerSet.choice r (args 0) (args 1)
  RelMap r := nomatch r

/-- Canonical interpretation of the full signature; use as a local instance. -/
@[instance_reducible] noncomputable def fullStructure (Role : Type u) :
    (language (FullSymbol Role)).Structure (WinnerSet Role) where
  funMap f args := match f with
    | .winner r => WinnerSet.singleton r
    | .choice r => WinnerSet.choice r (args 0) (args 1)
    | .rename p => WinnerSet.rename p (args 0)
  RelMap r := nomatch r

/-- The independent core reduct of the same carrier. -/
@[instance_reducible] noncomputable def coreStructure (Role : Type u) :
    (language (CoreSymbol Role)).Structure (WinnerSet Role) where
  funMap f args := match f with
    | .choice r => WinnerSet.choice r (args 0) (args 1)
  RelMap r := nomatch r

namespace Full

variable {Role : Type u} {Var : Type v}

/-- Encode the native public syntax as generic equational terms. -/
def encode : KFOL.Term Role Var → Term (FullSymbol Role) Var
  | .winner r => .func (.winner r) Fin.elim0
  | .var x => .var x
  | .choice r s t => .func (.choice r) (fun i => if i = 0 then encode s else encode t)
  | .rename p t => .func (.rename p) (fun _ => encode t)

/-- Decode any term in exactly the full public signature. -/
def decode : Term (FullSymbol Role) Var → KFOL.Term Role Var
  | .var x => .var x
  | .func (.winner r) _ => .winner r
  | .func (.choice r) args => .choice r (decode (args 0)) (decode (args 1))
  | .func (.rename p) args => .rename p (decode (args 0))

end Full

namespace Public

variable {Role : Type u} {Var : Type v}

/-- The no-switch public signature interpreted in native syntax. -/
def decode : Term (PublicSymbol Role) Var → KFOL.Term Role Var
  | .var x => .var x
  | .func (.winner r) _ => .winner r
  | .func (.choice r) args => .choice r (decode (args 0)) (decode (args 1))

/-- Include a constant-free owned-choice term in the public signature. -/
def ofCore : Term (CoreSymbol Role) Var → Term (PublicSymbol Role) Var
  | .var x => .var x
  | .func (.choice r) args => .func (.choice r) (fun i => ofCore (args i))

end Public

namespace Core

variable {Role : Type u} {Var : Type v}

/-- Decode the core signature into the existing native syntax. No constant or
switch constructor can arise from a core term. -/
def decode : Term (CoreSymbol Role) Var → KFOL.Term Role Var
  | .var x => .var x
  | .func (.choice r) args => .choice r (decode (args 0)) (decode (args 1))

/-- Encode a certified native core expression without extending the signature. -/
def encode : (t : KFOL.Term Role Var) → t.IsCore → Term (CoreSymbol Role) Var
  | .winner _, h => False.elim h
  | .var x, _ => .var x
  | .choice r s t, h => .func (.choice r)
      (fun i => if i = 0 then encode s h.1 else encode t h.2)
  | .rename _ _, h => False.elim h

end Core

end KFOL.Equational
