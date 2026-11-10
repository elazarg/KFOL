module

public import KFOL.Definitions.Reductions
public import KFOL.Definitions.Policies
public import KFOL.Definitions.PaperAlgebra
public import KFOL.Complexity.OwnerTermMachines
public import KFOL.Complexity.OwnerSynthesisBridge
public import KFOL.Complexity.PolicyTermMachines
public import KFOL.Complexity.GuardedPairMachines
public import KFOL.Complexity.CircuitGeneratorRecords
public import KFOL.Algorithms.FullTermCode.View
public import KFOL.Algorithms.TermCode
public import Complexity.Computability.Complexity.Reduction

/-! # Mathematical decision problems and their original binary presentations

Languages below are defined by original syntax and universal evaluation, never
by acceptance of a particular algorithm. Malformed words have no witness.
The only computational interface is the existing native polynomial-time class.
-/

@[expose] public section
namespace KFOL.Problems

universe u v
abbrev wordEncoding : List Bool ↪ List Bool := Turing.MultiTapeTM.encBits
abbrev booleanEncoding := Turing.MultiTapeTM.encBool
abbrev pairWordEncoding := Turing.MultiTapeTM.encPair wordEncoding wordEncoding
abbrev partialWordEncoding := Turing.MultiTapeTM.encOption wordEncoding
abbrev PolynomialTime {Input Output : Type} (f : Input → Output)
    (input : Input ↪ List Bool) (output : Output ↪ List Bool) : Prop :=
  Turing.MultiTapeTM.ComputableInPolyTime f input output

/-- Binary membership means that an actual original instance with this exact
code satisfies its independently specified mathematical predicate. The
embedding ensures that distinct original instances have distinct codes. -/
def encodedLanguage {Instance : Type u} (code : Instance ↪ List Bool)
    (valid : Instance → Prop) : Set (List Bool) :=
  {word | ∃ input, code input = word ∧ valid input}

/-- The three public signatures C, A and A^sym, respectively. -/
inductive PublicSignature where
  | core | publicLanguage | symmetric

def PublicSignature.Admissible {Role : Type u} {Var : Type v} :
    PublicSignature → Term Role Var → Prop
  | .core, term => term.IsCore
  | .publicLanguage, term => term.IsPublic
  | .symmetric, _ => True

def fullEquations (signature : PublicSignature) (K : ℕ) :
    Set (Term (Fin K) ℕ × Term (Fin K) ℕ) :=
  {equation | signature.Admissible equation.1 ∧ signature.Admissible equation.2 ∧
    ∀ valuation : ℕ → WinnerSet (Fin K), equation.1.eval valuation = equation.2.eval valuation}

/-- K is a binary header; role switches carry their actual forward arrays. -/
def fullEquationEncoding (K : ℕ) : (Term (Fin K) ℕ × Term (Fin K) ℕ) ↪ List Bool :=
  ⟨fun equation => FullTermCode.encodeEquationInput ⟨K,equation⟩,fun _ _ h => by
    have equal := FullTermCode.encodeEquationInput_injective h
    cases equal
    rfl⟩

def uniformFullLanguage (signature : PublicSignature) : Set (List Bool) :=
  encodedLanguage ⟨FullTermCode.encodeEquationInput,FullTermCode.encodeEquationInput_injective⟩
    (fun input => 3 ≤ input.1 ∧ input.2 ∈ fullEquations signature input.1)

/-- A fixed selected raw signature; only its explicitly selected operations
are in the input alphabet. -/
noncomputable def rawLanguage {Role : Type} (selected : Finset (Raw.Operation Role)) : Set (List Bool) :=
  encodedLanguage
    ⟨FiniteTermCode.encodeEquation (Raw.Symbol selected),FiniteTermCode.encodeEquation_injective⟩
    (fun equation : Raw.Term selected ℕ × Raw.Term selected ℕ =>
      ∀ valuation : ℕ → WinnerSet Role,
        Raw.Term.eval equation.1 valuation = Raw.Term.eval equation.2 valuation)

noncomputable def ownerLanguage {Role : Type} [Fintype Role] (owners : Finset Role)
    (relation : WinnerSet Role → WinnerSet Role → Prop) : Set (List Bool) :=
  encodedLanguage
    ⟨FiniteTermCode.encodeEquation (Owner.Symbol Role),FiniteTermCode.encodeEquation_injective⟩
    (fun equation : Owner.Term Role ℕ × Owner.Term Role ℕ =>
      Owner.Term.OwnersIn (fun owner => owner ∈ owners) equation.1 ∧
      Owner.Term.OwnersIn (fun owner => owner ∈ owners) equation.2 ∧
      ∀ valuation : ℕ → WinnerSet Role,
        relation (Owner.Term.eval equation.1 valuation) (Owner.Term.eval equation.2 valuation))

/-- One owner is interpreted after decoding a fixed Unit-labelled signature,
so this original input format is independent of the ambient role count. -/
noncomputable def oneOwnerLanguage {Role : Type u} (owner : Role) : Set (List Bool) :=
  encodedLanguage
    ⟨FiniteTermCode.encodeEquation (Owner.Symbol Unit),FiniteTermCode.encodeEquation_injective⟩
    (fun equation : Owner.Term Unit ℕ × Owner.Term Unit ℕ =>
      ∀ valuation : ℕ → WinnerSet Role,
        Owner.Term.eval (Owner.Term.withOwner owner equation.1) valuation =
          Owner.Term.eval (Owner.Term.withOwner owner equation.2) valuation)

def policySets {Role : Type u} {Label : Type v} (policies : Label → Finset Role) : Label → Set Role :=
  fun label => (policies label : Set Role)

noncomputable def policyLanguage {Role Label : Type} [Fintype Label]
    (policies : Label → Finset Role) : Set (List Bool) :=
  encodedLanguage
    ⟨FiniteTermCode.encodeEquation (Policies.Symbol Label),FiniteTermCode.encodeEquation_injective⟩
    (fun equation : Policies.Term Label ℕ × Policies.Term Label ℕ =>
      ∀ valuation : ℕ → WinnerSet Role,
        Policies.Term.eval (policySets policies) equation.1 valuation =
          Policies.Term.eval (policySets policies) equation.2 valuation)

noncomputable def guardedLanguage {Role : Type u} (first second : Role) : Set (List Bool) :=
  encodedLanguage
    ⟨FiniteTermCode.encodeEquation GuardedPair.Symbol,FiniteTermCode.encodeEquation_injective⟩
    (fun equation : GuardedPair.Term ℕ × GuardedPair.Term ℕ =>
      ∀ valuation : ℕ → WinnerSet Role,
        GuardedPair.Term.eval first second equation.1 valuation =
          GuardedPair.Term.eval first second equation.2 valuation)

def resetLanguage (Role : Type u) : Set (List Bool) :=
  encodedLanguage ⟨fun equation : Reset.Term ℕ × Reset.Term ℕ =>
    Words.pair (Algorithms.TermCode.encode equation.1) (Algorithms.TermCode.encode equation.2),by
      intro first second equal
      have paired := congrArg Words.unpair? equal
      simp only [Words.unpair?_pair,Option.some.injEq,Prod.mk.injEq] at paired
      exact Prod.ext (Algorithms.TermCode.encode_injective paired.1)
        (Algorithms.TermCode.encode_injective paired.2)⟩
    (fun equation => ∀ valuation : ℕ → WinnerSet Role,
      equation.1.eval valuation = equation.2.eval valuation)

/-- Candidate canonical tables are realizable exactly when some primitive
reset tree has precisely their listed minimal guards. No checker occurs. -/
def ResetTableRealizable (table : Algorithms.GuardDescriptor) : Prop :=
  ∃ term : Reset.Term (Fin table.labels.length), term.table = table.guards

def resetTableLanguage : Set (List Bool) :=
  encodedLanguage ⟨Algorithms.GuardDescriptor.encode,Algorithms.GuardDescriptor.encode_injective⟩
    ResetTableRealizable

/-- Synthesis returns an original primitive tree, with exact canonical table
and the report's O(nM) constructor bound, using the original sparse labels. -/
def ResetSynthesisOutput (table : Algorithms.GuardDescriptor) (word : List Bool) : Prop :=
  ∃ term : Reset.Term (Fin table.labels.length), term.table = table.guards ∧
    term.size ≤ 1+2*table.labels.length*table.records.length ∧
    word = Algorithms.TermCode.encode (term.relabel table.labels.get)

/-- A semantic relation between an encoded candidate table and an encoded
primitive tree realizing exactly that table with the compact size bound. -/
def ResetSynthesis (input output : List Bool) : Prop :=
  ∃ table : Algorithms.GuardDescriptor, table.encode = input ∧ ResetSynthesisOutput table output

/-- Uniform original term input: binary role count and explicit role arrays. -/
def termCode (K : ℕ) (term : Term (Fin K) ℕ) : List Bool :=
  FullTermCode.encodeInput ⟨K,term⟩

/-- Finite owner tables carry their explicit unary position dimension; root
and source labels are binary and each prerequisite is an explicit bitset. -/
abbrev OwnerTableInput := (n : ℕ) × Owner.GuardTable (Fin n)
abbrev OwnerTableOutput (Role : Type) := (n : ℕ) × Owner.Term Role (Fin n)
abbrev ownerTableEncoding := _root_.KFOL.Complexity.OwnerRuntime.inputEncoding
noncomputable abbrev ownerTableOutputEncoding (Role : Type) [Fintype Role] :=
  Turing.MultiTapeTM.encOption (_root_.KFOL.Complexity.OwnerRuntime.outputEncoding (Role := Role))

/-- Recognition includes the supplied table's independent canonicality;
realization means exact root, one-owner syntax and all outsider observations. -/
def OwnerTableRealizable {Role : Type} (owner : Role) (input : OwnerTableInput) : Prop :=
  input.2.Canonical ∧ ∃ term : Owner.Term Role (Fin input.1), input.2.Realizes owner term

def OwnerSynthesisOutput {Role : Type} (owner : Role) (input : OwnerTableInput)
    (output : OwnerTableOutput Role) : Prop :=
  ∃ term : Owner.Term Role (Fin input.1), output = ⟨input.1,term⟩ ∧
    input.2.Realizes owner term ∧ term.size ≤ 1+input.2.entries.length*(10*input.1+7)

/-- A successful core extraction returns an equivalent core, with no increase
in primitive constructor size, in the original binary-K input presentation. -/
def CoreExtractionOutput (K : ℕ) (input : Term (Fin K) ℕ) (word : List Bool) : Prop :=
  ∃ core : Term (Fin K) ℕ, core.IsCore ∧
    core.Equivalent input ∧ core.size ≤ input.size ∧ word = termCode K core

abbrev CoreTerm (K : ℕ) := {term : Term (Fin K) ℕ // term.IsCore}

def fullTermEncoding (K : ℕ) : Term (Fin K) ℕ ↪ List Bool :=
  ⟨fun term => FullTermCode.encode (FullTermCode.view term),fun _ _ h =>
    FullTermCode.view_injective (FullTermCode.encode_injective h)⟩

def coreTermEncoding (K : ℕ) : CoreTerm K ↪ List Bool :=
  ⟨fun term => fullTermEncoding K term.val,fun _ _ h =>
    Subtype.ext ((fullTermEncoding K).injective h)⟩

/-- A primitive shared reset graph is validated independently, then evaluated
with its actual cache references rather than by expanding it to a tree. -/
noncomputable def resetCircuitLanguage (Role : Type u) : Set (List Bool) :=
  let _ := Reset.structureOf (WinnerSet.reset (Role := Role))
  encodedLanguage (Circuit.Code.encoding Reset.Symbol) (fun equation => equation.Holds (WinnerSet Role))

/-- The same exact graph word format on reset's fixed three-element algebra. -/
noncomputable def resetChainCircuitLanguage : Set (List Bool) :=
  let _ := Reset.structureOf (fun i j : Fin 3 => if j = 0 then 0 else max i j)
  encodedLanguage (Circuit.Code.encoding Reset.Symbol) (fun equation => equation.Holds (Fin 3))

end KFOL.Problems
