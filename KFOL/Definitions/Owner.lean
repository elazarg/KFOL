module

public import KFOL.Definitions.Reset

/-! # Reset with owner-labelled guarded choice

The signature reuses mathlib terms and the shared nonempty winner-set carrier.
Guard lists describe finite conjunctions; repeated tests are harmless, while
separate variable occurrences still produce separate guards.
-/

@[expose] public section

namespace KFOL

universe u v

/-- The guarded operation from the paper: combine the side inputs by owned
choice, then reset against the root input. -/
noncomputable def WinnerSet.guardedChoice {Role : Type u} (r : Role)
    (root left right : WinnerSet Role) : WinnerSet Role :=
  (WinnerSet.choice r left right).reset root

namespace Owner

inductive Symbol (Role : Type u) : ℕ → Type u
  | reset : Symbol Role 2
  | guarded (r : Role) : Symbol Role 3

abbrev Term (Role : Type u) (Var : Type v) := Equational.Term (Symbol Role) Var

/-- Interpret exactly the two families of operations in the owner signature. -/
@[instance_reducible] noncomputable def structureOf {Role : Type u} :
    (Equational.language (Symbol Role)).Structure (WinnerSet Role) where
  funMap f args := match f with
    | .reset => (args 0).reset (args 1)
    | .guarded r => WinnerSet.guardedChoice r (args 0) (args 1) (args 2)
  RelMap r := nomatch r

/-- The independently interpreted fixed one-owner signature on winner sets.
Its single ternary symbol is the chosen owner's guarded operation. -/
@[instance_reducible] noncomputable def oneOwnerStructure {Role : Type u} (owner : Role) :
    (Equational.language (Symbol Unit)).Structure (WinnerSet Role) where
  funMap f args := match f with
    | .reset => (args 0).reset (args 1)
    | .guarded _ => WinnerSet.guardedChoice owner (args 0) (args 1) (args 2)
  RelMap r := nomatch r

namespace Term

variable {Role : Type u} {Var : Type v}

def step (s t : Term Role Var) : Term Role Var :=
  .func .reset (fun i => if i = 0 then s else t)

def guarded (r : Role) (x y z : Term Role Var) : Term Role Var :=
  .func (.guarded r) (fun i => if i = 0 then x else if i = 1 then y else z)

def root : Term Role Var → Var
  | .var j => j
  | .func .reset args => root (args 1)
  | .func (.guarded _) args => root (args 0)

noncomputable def eval (t : Term Role Var) (v : Var → WinnerSet Role) : WinnerSet Role :=
  let _ := structureOf (Role := Role)
  t.realize v

/-- A syntactic restriction on the owner labels, independent of evaluation. -/
def OwnersIn (P : Role → Prop) : Term Role Var → Prop
  | .var _ => True
  | .func .reset args => OwnersIn P (args 0) ∧ OwnersIn P (args 1)
  | .func (.guarded r) args => P r ∧ OwnersIn P (args 0) ∧
      OwnersIn P (args 1) ∧ OwnersIn P (args 2)

def leafCount : Term Role Var → ℕ
  | .var _ => 1
  | .func .reset args => leafCount (args 0) + leafCount (args 1)
  | .func (.guarded _) args => leafCount (args 0) + leafCount (args 1) + leafCount (args 2)

end Term

namespace Term

/-- Interpret the one ternary owner label by a chosen role, leaving every
variable occurrence and native reset/H constructor explicit. -/
def withOwner {Role : Type u} {Var : Type v} (owner : Role) : Term Unit Var → Term Role Var
  | .var j => .var j
  | .func .reset args => step (withOwner owner (args 0)) (withOwner owner (args 1))
  | .func (.guarded _) args => guarded owner (withOwner owner (args 0))
      (withOwner owner (args 1)) (withOwner owner (args 2))

end Term

/-- A source together with ambiguous and non-owner-atom tests. The two lists
represent conjunctions, with no semantic dependence on their order. -/
structure Guard (Var : Type v) where
  source : Var
  many : List Var := []
  outside : List Var := []
  deriving DecidableEq

def Guard.Holds {Var : Type v} (M N V : Var → Prop) (g : Guard Var) : Prop :=
  (∀ j ∈ g.many, M j) ∧ (∀ j ∈ g.outside, N j) ∧ V g.source

def Guard.addMany {Var : Type v} (j : Var) (g : Guard Var) : Guard Var :=
  { g with many := j :: g.many }

def Guard.addOutside {Var : Type v} (j : Var) (g : Guard Var) : Guard Var :=
  { g with outside := j :: g.outside }

def Eval {Var : Type v} (guards : List (Guard Var)) (M N V : Var → Prop) : Prop :=
  ∃ g ∈ guards, g.Holds M N V

/-- A weaker guard dominates a stronger one exactly by the displayed
source and prerequisite containments in the paper. -/
def Guard.Dominates {Var : Type v} (weak strong : Guard Var) : Prop :=
  weak.source = strong.source ∧
  (∀ j ∈ weak.many, j ∈ strong.many) ∧
  (∀ j ∈ weak.outside, j ∈ strong.many ∨ j ∈ strong.outside ∨ j = strong.source)

def Covers {Var : Type v} (left right : List (Guard Var)) : Prop :=
  ∀ g ∈ left, ∃ h ∈ right, h.Dominates g

/-- One raw guard per original variable occurrence. Tests inspect roots of
subterms, without distributing their own guard lists. -/
def Term.guards {Role : Type u} {Var : Type v} [DecidableEq Role]
    (observer : Role) : Term Role Var → List (Guard Var)
  | .var j => [⟨j, [], []⟩]
  | .func .reset args => guards observer (args 1) ++
      (guards observer (args 0)).map (Guard.addMany (root (args 1)))
  | .func (.guarded r) args =>
      let children := guards observer (args 1) ++ guards observer (args 2)
      let eligible := if r = observer then children else
        (children.map (Guard.addOutside (root (args 1)))).map (Guard.addOutside (root (args 2)))
      guards observer (args 0) ++ eligible.map (Guard.addMany (root (args 0)))

def Guard.forget {Var : Type v} (g : Guard Var) : Guard Var := { g with outside := [] }

def dominatesB {Var : Type v} [DecidableEq Var] (weak strong : Guard Var) : Bool :=
  decide (weak.source = strong.source) &&
  weak.many.all (fun j => decide (j ∈ strong.many)) &&
  weak.outside.all (fun j => decide (j ∈ strong.many ∨ j ∈ strong.outside ∨ j = strong.source))

def coversB {Var : Type v} [DecidableEq Var] (left right : List (Guard Var)) : Bool :=
  left.all (fun g => right.any (fun h => dominatesB h g))

def Term.equationB {Role : Type u} {Var : Type v} [DecidableEq Role] [DecidableEq Var]
    (observer : Role) (left right : Term Role Var) : Bool :=
  coversB (left.guards observer) (right.guards observer) &&
    coversB (right.guards observer) (left.guards observer)

/-- The minimal three-role valuation associated with a failed guard test.
Every value is an atom or a pair, including the source's marker value. -/
def minimalVal {Role : Type u} {Var : Type v} [DecidableEq Var]
    (observer other background : Role) (g : Guard Var) (j : Var) : WinnerSet Role :=
  if j = g.source then
    if j ∈ g.many then (WinnerSet.singleton observer).union (WinnerSet.singleton other)
      else WinnerSet.singleton observer
  else if j ∈ g.many then (WinnerSet.singleton other).union (WinnerSet.singleton background)
  else if j ∈ g.outside then WinnerSet.singleton background else WinnerSet.singleton other

/-- The fixed four-element owner algebra. Its winning state represents the
observer's presence, independently of the root's atomic/ambiguous distinction. -/
inductive Four where
  | owner | other | ambiguous | winning
  deriving DecidableEq, Repr

namespace Four

instance : Fintype Four where
  elems := {.owner, .other, .ambiguous, .winning}
  complete := by intro x; cases x <;> simp

def reset (x y : Four) : Four :=
  if y = .ambiguous ∧ x = .winning then .winning else y

def guarded (x y z : Four) : Four :=
  if x = .ambiguous then
    if y ≠ .owner ∧ z ≠ .owner ∧ (y = .winning ∨ z = .winning) then .winning else .ambiguous
  else x

/-- Observer projection onto the four-state algebra. -/
noncomputable def project {Role : Type u} (owner observer : Role) (A : WinnerSet Role) : Four := by
  classical
  exact if observer ∈ A.val then .winning else
    if A = WinnerSet.singleton owner then .owner else
      if A.Ambiguous then .ambiguous else .other

/-- The concrete four winner sets displayed in the paper. -/
def embed {Role : Type u} (owner observer background : Role) : Four → WinnerSet Role
  | .owner => WinnerSet.singleton owner
  | .other => WinnerSet.singleton background
  | .ambiguous => (WinnerSet.singleton owner).union (WinnerSet.singleton background)
  | .winning => ((WinnerSet.singleton owner).union (WinnerSet.singleton background)).union
      (WinnerSet.singleton observer)

end Four

/-- All owner labels act by the fixed guarded operation on Four; equality
transport is restricted to terms using the chosen concrete owner. -/
@[instance_reducible] def fourStructure {Role : Type u} :
    (Equational.language (Symbol Role)).Structure Four where
  funMap f args := match f with
    | .reset => Four.reset (args 0) (args 1)
    | .guarded _ => Four.guarded (args 0) (args 1) (args 2)
  RelMap r := nomatch r

def Term.evalFour {Role : Type u} {Var : Type v} (t : Term Role Var) (v : Var → Four) : Four :=
  let _ := fourStructure (Role := Role)
  t.realize v

/-! ## Independent canonical tables and their explicit finite synthesis program -/


/-- A canonical prerequisite pair, with the output supplied by the table index. -/
structure GuardPair (Var : Type v) where
  many : Finset Var
  outside : Finset Var
  deriving DecidableEq

/-- Candidate finite tables, independent of term realizability and saturation. -/
structure GuardTable (Var : Type v) where
  root : Var
  entries : List (Var × GuardPair Var)

namespace GuardTable

variable {Var : Type v} [DecidableEq Var]

/-- Set semantics of the explicitly supplied guard records at one source. -/
def guards (T : GuardTable Var) (j : Var) : Finset (GuardPair Var) :=
  ((T.entries.filter (fun p => p.1 = j)).map Prod.snd).toFinset

/-- A contribution at j is permitted by some candidate guard when these
explicit tests are imposed. Ambiguity implies a non-owner-atom test. -/
def Permitted (T : GuardTable Var) (j : Var) (C D : Finset Var) : Prop :=
  ∃ g ∈ T.guards j, g.many ⊆ C ∧ g.outside ⊆ C ∪ D ∪ {j}

instance decidablePermitted (T : GuardTable Var) (j : Var) (C D : Finset Var) :
    Decidable (T.Permitted j C D) := by unfold Permitted; infer_instance

/-- Exact candidate semantics for arbitrary ambiguity, non-owner and source statuses. -/
def Enabled (T : GuardTable Var) (M N V : Set Var) : Prop :=
  ∃ j, ∃ g ∈ T.guards j, (g.many : Set Var) ⊆ M ∧ (g.outside : Set Var) ⊆ N ∧ j ∈ V

/-- Canonical input conditions, including the independently supplied root. -/
def Canonical (T : GuardTable Var) : Prop :=
  T.entries.Nodup ∧ T.guards T.root = {⟨∅, ∅⟩} ∧
  ∀ j, j ≠ T.root →
    (∀ g ∈ T.guards j, T.root ∈ g.many ∧ j ∉ g.many ∧ Disjoint g.outside (insert j g.many)) ∧
    (∀ g ∈ T.guards j, ∀ h ∈ T.guards j,
      g.many ⊆ h.many → g.outside ⊆ h.many ∪ h.outside ∪ {j} → g = h)

end GuardTable

/-- The accumulated ambiguity and non-owner tests above the current hole. -/
structure SaturationState (Var : Type v) where
  many : Finset Var
  outside : Finset Var
  deriving DecidableEq

namespace SaturationState

variable {Var : Type v} [DecidableEq Var]

def initial (r : Var) : SaturationState Var := ⟨{r}, ∅⟩

/-- Promote w to ambiguity and retain all other added non-owner tests. -/
def update (S : SaturationState Var) (w z : Var) : SaturationState Var :=
  ⟨insert w S.many, (S.outside ∪ {w, z}) \ insert w S.many⟩

/-- Test strengthening: both ambiguity and the combined non-owner status grow. -/
def Below (S R : SaturationState Var) : Prop :=
  S.many ⊆ R.many ∧ S.many ∪ S.outside ⊆ R.many ∪ R.outside

def rank (S : SaturationState Var) : ℕ := S.many.card + (S.many ∪ S.outside).card

end SaturationState

namespace GuardTable

variable {Var : Type v} [DecidableEq Var]

/-- The universe relevant to this one target guard, not an enumeration of subsets. -/
def target (j : Var) (g : GuardPair Var) : Finset Var := g.many ∪ g.outside ∪ {j}

/-- The report's enabled w,z rule; genuine state changes are required. -/
def UpdateAllowed (T : GuardTable Var) (j : Var) (g : GuardPair Var)
    (S : SaturationState Var) (w z : Var) : Prop :=
  w ∈ g.many ∧ z ∈ target j g ∧
    T.Permitted w S.many (S.outside ∪ {w, z}) ∧
    T.Permitted z S.many (S.outside ∪ {w, z}) ∧ S.update w z ≠ S

instance decidableUpdateAllowed (T : GuardTable Var) (j : Var) (g : GuardPair Var)
    (S : SaturationState Var) (w z : Var) : Decidable (T.UpdateAllowed j g S w z) := by
  unfold UpdateAllowed
  infer_instance

/-- Scan an explicit listing of input positions. The dictionary order
chooses a deterministic execution without changing the mathematical rule. -/
def next (T : GuardTable Var) (positions : List Var) (j : Var) (g : GuardPair Var)
    (S : SaturationState Var) : Option (Var × Var) :=
  (positions.product positions).find? (fun p => decide (T.UpdateAllowed j g S p.1 p.2))

/-- A fixed number of scans, recording the exact sequence of chosen frames. -/
def run (T : GuardTable Var) (positions : List Var) (j : Var) (g : GuardPair Var) :
    ℕ → SaturationState Var × List (Var × Var)
  | 0 => (SaturationState.initial T.root, [])
  | k + 1 =>
      let previous := T.run positions j g k
      match T.next positions j g previous.1 with
      | none => previous
      | some p => (previous.1.update p.1 p.2, previous.2 ++ [p])

/-- The two finishing alternatives in the report, at the reached state. -/
def Finish (T : GuardTable Var) (j : Var) (g : GuardPair Var) (S : SaturationState Var) : Prop :=
  T.Permitted j S.many S.outside ∨
    ∃ z ∈ target j g, T.Permitted j S.many (S.outside ∪ {j, z}) ∧
      T.Permitted z S.many (S.outside ∪ {j, z})

instance decidableFinish (T : GuardTable Var) (j : Var) (g : GuardPair Var) (S : SaturationState Var) :
    Decidable (T.Finish j g S) := by unfold Finish; infer_instance

/-- The target guard's executable saturation test, using at most twice the
number of listed input positions as its clock. -/
def accepts (T : GuardTable Var) (positions : List Var) (j : Var) (g : GuardPair Var) : Bool :=
  decide (j = T.root ∨ T.Finish j g (T.run positions j g (2 * positions.length)).1)

end GuardTable
namespace Term

variable {Role : Type u} {Var : Type v}

/-- Primitive signature size, counting each copied variable occurrence. -/
def size : Term Role Var → ℕ
  | .var _ => 1
  | .func .reset args => 1 + size (args 0) + size (args 1)
  | .func (.guarded _) args => 1 + size (args 0) + size (args 1) + size (args 2)

/-- The exact one-hole frames recorded by saturation, with a supplied final
filling. Every frame has exactly one recursive occurrence. -/
def pathBody (owner : Role) (root : Var) : List (Var × Var) → Term Role Var → Term Role Var
  | [], fill => fill
  | (w, z) :: rest, fill => guarded owner (.var root)
      (step (pathBody owner root rest fill) (.var w)) (.var z)

/-- Initial reset frame of the report's root-first path construction. -/
def pathTerm (owner : Role) (root : Var) (frames : List (Var × Var)) (fill : Term Role Var) :
    Term Role Var := step (pathBody owner root frames fill) (.var root)

end Term

namespace GuardTable

variable {Var : Type v} [DecidableEq Var]

/-- Choose the second finishing alternative by an explicit scan. -/
def finishWitness (T : GuardTable Var) (positions : List Var) (j : Var) (g : GuardPair Var)
    (S : SaturationState Var) : Option Var :=
  positions.find? (fun z => decide (z ∈ target j g ∧
    T.Permitted j S.many (S.outside ∪ {j, z}) ∧ T.Permitted z S.many (S.outside ∪ {j, z})))

/-- The report's two actual final fillings, with no assumed certificate. -/
def finishTerm {Role : Type u} (T : GuardTable Var) (owner : Role) (positions : List Var)
    (j : Var) (g : GuardPair Var) (S : SaturationState Var) : Option (Term Role Var) :=
  if T.Permitted j S.many S.outside then some (Term.step (.var j) (.var T.root)) else
    (T.finishWitness positions j g S).map (fun z => Term.guarded owner (.var T.root) (.var j) (.var z))

/-- Construct the target guard's actual path from the run's recorded frames. -/
def guardPath {Role : Type u} (T : GuardTable Var) (owner : Role) (positions : List Var)
    (j : Var) (g : GuardPair Var) : Option (Term Role Var) :=
  if j = T.root then some (.var T.root) else
    let result := T.run positions j g (2 * positions.length)
    (T.finishTerm owner positions j g result.1).map (Term.pathTerm owner T.root result.2)

/-- Input position coverage, independent of numeric names or their maximum. -/
def Listed (T : GuardTable Var) (positions : List Var) : Prop :=
  T.root ∈ positions ∧ ∀ p ∈ T.entries, target p.1 p.2 ⊆ positions.toFinset

instance decidableListed (T : GuardTable Var) (positions : List Var) : Decidable (T.Listed positions) := by
  unfold Listed
  infer_instance

/-- The finite record formulation of canonicality, without universal scanning
of the variable type. -/
def canonicalB (T : GuardTable Var) : Bool :=
  decide (T.entries.Nodup ∧ T.guards T.root = {⟨∅, ∅⟩} ∧
    ∀ p ∈ T.entries, p.1 ≠ T.root →
      (T.root ∈ p.2.many ∧ p.1 ∉ p.2.many ∧ Disjoint p.2.outside (insert p.1 p.2.many)) ∧
      ∀ q ∈ T.entries, q.1 = p.1 → p.2.many ⊆ q.2.many →
        p.2.outside ⊆ q.2.many ∪ q.2.outside ∪ {p.1} → p.2 = q.2)

/-- The actual whole-table finite checker. Canonical input, a complete finite
position dictionary, and every required guard are checked by the program. -/
def check (T : GuardTable Var) (positions : List Var) : Bool :=
  T.canonicalB && decide (T.Listed positions) &&
    T.entries.all (fun p => T.accepts positions p.1 p.2)

end GuardTable

namespace Term

variable {Role : Type u} {Var : Type v}

/-- Join the common-root path terms, with the root projection as empty join. -/
def joinPaths (root : Var) : List (Term Role Var) → Term Role Var
  | [] => .var root
  | t :: rest => step t (joinPaths root rest)

end Term

namespace GuardTable

variable {Var : Type v} [DecidableEq Var]

/-- An independently stated realization of a candidate table: root, signature,
and exact membership semantics for every non-owner observer. -/
def Realizes {Role : Type u} (T : GuardTable Var) (owner : Role) (t : Term Role Var) : Prop :=
  t.root = T.root ∧ t.OwnersIn (fun x => x = owner) ∧
    ∀ observer, observer ≠ owner → ∀ v : Var → WinnerSet Role,
      observer ∈ (t.eval v).val ↔
        T.Enabled {i | (v i).Ambiguous} {i | v i ≠ WinnerSet.singleton owner}
          {i | observer ∈ (v i).val}

/-- Actual term synthesis from the checked table, with no supplied term or
realizability certificate. Every copied occurrence contributes to Term.size. -/
def synthesize {Role : Type u} (T : GuardTable Var) (owner : Role) (positions : List Var) :
    Option (Term Role Var) :=
  if T.check positions then
    (T.entries.mapM (fun p => T.guardPath owner positions p.1 p.2)).map (Term.joinPaths T.root)
  else none

end GuardTable


/-! ## Concrete obstruction to a basis with only three variables -/

namespace BasisObstruction

inductive Carrier where
  | low | middle | high | isolated
  deriving DecidableEq, Repr

instance : Fintype Carrier where
  elems := {.low, .middle, .high, .isolated}
  complete x := by cases x <;> simp

instance : Nonempty Carrier := ⟨.low⟩

def rank : Carrier → ℕ
  | .low => 0 | .middle => 1 | .high => 2 | .isolated => 3

def reset (x y : Carrier) : Carrier :=
  if x = .isolated ∨ y = .isolated then y
  else if rank x ≤ rank y then y else x

def guarded (x y z : Carrier) : Carrier :=
  if x = .isolated then x
  else if y = .isolated ∨ z = .isolated then
    let other := if y = .isolated then z else y
    if x = .low ∧ other = .high then .high else x
  else reset (reset x y) z

instance : (Equational.language (Symbol Unit)).Structure Carrier where
  funMap f args := match f with
    | .reset => reset (args 0) (args 1)
    | .guarded _ => guarded (args 0) (args 1) (args 2)
  RelMap r := nomatch r


/-- Each proper subset embeds into Four squared. -/
def embed : Carrier → Carrier → Four × Four
  | .isolated, .low => (.ambiguous, .ambiguous)
  | .isolated, .middle => (.winning, .ambiguous)
  | .isolated, .high => (.winning, .winning)
  | .middle, .low => (.ambiguous, .ambiguous)
  | .middle, .high => (.winning, .winning)
  | .middle, .isolated => (.other, .other)
  | .low, .middle => (.ambiguous, .ambiguous)
  | .low, .high => (.winning, .winning)
  | .low, .isolated => (.owner, .owner)
  | .high, .low => (.ambiguous, .ambiguous)
  | .high, .middle => (.winning, .winning)
  | .high, .isolated => (.owner, .owner)
  | _, _ => (.owner, .owner)


/-- The four-variable identity violated by the concrete witness. -/
def rootExpansion : Equational.Identity (Symbol Unit) :=
  let u : Term Unit (Fin 4) := .var 0
  let r : Term Unit (Fin 4) := .var 1
  let a : Term Unit (Fin 4) := .var 2
  let b : Term Unit (Fin 4) := .var 3
  ⟨4, Term.guarded () (Term.step u r) a b,
    Term.step (Term.step u r) (Term.guarded () r a b)⟩

end BasisObstruction


/-! ## The explicitly listed forty-law candidate basis -/

namespace FiniteBasis

/-- Exactly the displayed forty equations, with six declared variable slots.
The two five-variable split laws reuse the slot unused by their other variables. -/
def basisAxiom (i : Fin 40) : Equational.Identity (Symbol Unit) :=
  let pair : Term Unit (Fin 6) × Term Unit (Fin 6) := match i.val with
    | 0 => ((Term.step (.var 0) (.var 0)), (.var 0)) -- R1
    | 1 => ((Term.step (Term.step (.var 0) (.var 1)) (.var 0)), (Term.step (.var 1) (.var 0))) -- R2
    | 2 => ((Term.step (Term.step (.var 0) (.var 1)) (.var 1)), (Term.step (.var 0) (.var 1))) -- R3
    | 3 => ((Term.step (.var 0) (Term.step (Term.step (.var 0) (.var 1)) (.var 2))), (Term.step (.var 0) (Term.step (.var 1) (.var 2)))) -- R4
    | 4 => ((Term.step (Term.step (Term.step (.var 0) (.var 1)) (.var 2)) (.var 1)), (Term.step (Term.step (.var 0) (.var 2)) (.var 1))) -- R5
    | 5 => ((Term.step (.var 0) (Term.step (.var 1) (.var 2))), (Term.step (.var 1) (Term.step (.var 0) (.var 2)))) -- R6
    | 6 => ((Term.guarded () (.var 0) (.var 1) (.var 2)), (Term.guarded () (.var 0) (.var 2) (.var 1))) -- h_sym
    | 7 => ((Term.guarded () (.var 0) (.var 1) (.var 1)), (Term.step (.var 1) (.var 0))) -- h_minor
    | 8 => ((Term.step (Term.guarded () (.var 0) (.var 1) (.var 2)) (.var 0)), (Term.guarded () (.var 0) (.var 1) (.var 2))) -- h_root
    | 9 => ((Term.guarded () (Term.step (.var 5) (.var 0)) (.var 1) (.var 2)), (Term.step (Term.step (.var 5) (.var 0)) (Term.guarded () (.var 0) (.var 1) (.var 2)))) -- h_expand
    | 10 => ((Term.guarded () (.var 0) (Term.step (.var 5) (.var 1)) (Term.step (.var 4) (.var 2))), (Term.step (Term.step (Term.guarded () (.var 0) (Term.step (.var 5) (.var 1)) (.var 2)) (.var 0)) (Term.step (Term.guarded () (.var 0) (.var 1) (Term.step (.var 4) (.var 2))) (.var 0)))) -- h_split
    | 11 => ((Term.guarded () (.var 0) (Term.step (.var 5) (.var 1)) (.var 2)), (Term.guarded () (.var 0) (Term.step (Term.step (.var 5) (.var 0)) (.var 1)) (.var 2))) -- h_back
    | 12 => ((Term.step (Term.guarded () (.var 1) (.var 5) (.var 2)) (.var 0)), (Term.step (Term.step (Term.guarded () (.var 0) (.var 5) (.var 2)) (.var 1)) (.var 0))) -- h_reroot
    | 13 => ((Term.guarded () (.var 0) (.var 1) (.var 2)), (Term.guarded () (.var 0) (Term.step (.var 0) (.var 1)) (.var 2))) -- h_insert
    | 14 => ((Term.step (Term.step (Term.step (.var 5) (.var 1)) (Term.step (.var 4) (.var 1))) (.var 0)), (Term.step (Term.step (Term.step (Term.step (.var 5) (.var 1)) (.var 0)) (.var 0)) (Term.step (Term.step (Term.step (.var 4) (.var 1)) (.var 0)) (.var 0)))) -- project_join
    | 15 => ((Term.step (.var 5) (Term.step (.var 4) (.var 1))), (Term.step (Term.step (.var 5) (.var 1)) (Term.step (.var 4) (.var 1)))) -- reset_split
    | 16 => ((Term.step (Term.step (.var 5) (.var 1)) (.var 0)), (Term.step (Term.step (Term.step (.var 5) (.var 0)) (.var 1)) (.var 0))) -- reset_back
    | 17 => ((Term.step (Term.step (.var 5) (.var 0)) (.var 0)), (Term.step (.var 5) (.var 0))) -- project_idem
    | 18 => ((Term.step (Term.step (.var 5) (Term.step (.var 4) (.var 0))) (.var 0)), (Term.step (.var 5) (Term.step (.var 4) (.var 0)))) -- root_preserve
    | 19 => ((Term.step (Term.guarded () (.var 0) (Term.step (Term.step (.var 5) (.var 0)) (.var 1)) (.var 2)) (.var 0)), (Term.guarded () (.var 0) (Term.step (Term.step (.var 5) (.var 0)) (.var 1)) (.var 2))) -- F_closed
    | 20 => ((Term.guarded () (.var 0) (Term.step (Term.step (Term.step (Term.step (.var 5) (.var 0)) (.var 0)) (Term.step (Term.step (.var 4) (.var 0)) (.var 0))) (.var 1)) (.var 2)), (Term.step (Term.step (Term.guarded () (.var 0) (Term.step (Term.step (.var 5) (.var 0)) (.var 1)) (.var 2)) (.var 0)) (Term.step (Term.guarded () (.var 0) (Term.step (Term.step (.var 4) (.var 0)) (.var 1)) (.var 2)) (.var 0)))) -- F_join
    | 21 => ((Term.step (Term.step (Term.guarded () (.var 0) (Term.step (Term.step (.var 5) (.var 0)) (.var 1)) (.var 2)) (.var 0)) (Term.step (Term.step (Term.step (Term.guarded () (.var 0) (Term.step (.var 0) (.var 1)) (.var 2)) (.var 0)) (Term.step (Term.step (.var 5) (.var 0)) (.var 0))) (.var 0))), (Term.step (Term.step (Term.guarded () (.var 0) (Term.step (.var 0) (.var 1)) (.var 2)) (.var 0)) (Term.step (Term.step (.var 5) (.var 0)) (.var 0)))) -- F_contract
    | 22 => ((Term.guarded () (.var 0) (Term.step (Term.guarded () (.var 0) (Term.step (Term.step (.var 5) (.var 0)) (.var 1)) (.var 2)) (.var 1)) (.var 2)), (Term.guarded () (.var 0) (Term.step (Term.step (.var 5) (.var 0)) (.var 1)) (.var 2))) -- F_idem
    | 23 => ((Term.guarded () (.var 0) (Term.step (Term.guarded () (.var 0) (Term.step (Term.guarded () (.var 0) (Term.step (Term.step (.var 5) (.var 0)) (.var 1)) (.var 2)) (.var 3)) (.var 4)) (.var 1)) (.var 2)), (Term.guarded () (.var 0) (Term.step (Term.guarded () (.var 0) (Term.step (Term.step (.var 5) (.var 0)) (.var 3)) (.var 4)) (.var 1)) (.var 2))) -- F_band
    | 24 => ((Term.guarded () (.var 0) (Term.step (Term.step (Term.step (Term.step (.var 5) (.var 0)) (.var 1)) (.var 0)) (.var 1)) (.var 2)), (Term.guarded () (.var 0) (Term.step (Term.step (.var 5) (.var 0)) (.var 1)) (.var 2))) -- F_Ga
    | 25 => ((Term.guarded () (.var 0) (Term.step (Term.guarded () (.var 0) (Term.step (.var 5) (.var 0)) (.var 1)) (.var 1)) (.var 2)), (Term.guarded () (.var 0) (Term.step (Term.step (.var 5) (.var 0)) (.var 1)) (.var 2))) -- F_Ka
    | 26 => ((Term.guarded () (.var 0) (Term.step (Term.guarded () (.var 0) (Term.step (.var 5) (.var 0)) (.var 2)) (.var 1)) (.var 2)), (Term.guarded () (.var 0) (Term.step (Term.step (.var 5) (.var 0)) (.var 1)) (.var 2))) -- F_Kb
    | 27 => ((Term.guarded () (.var 0) (Term.step (Term.step (.var 1) (.var 0)) (.var 1)) (.var 2)), (Term.guarded () (.var 0) (Term.step (.var 0) (.var 1)) (.var 2))) -- F_ca
    | 28 => ((Term.guarded () (.var 0) (Term.step (Term.step (.var 2) (.var 0)) (.var 1)) (.var 2)), (Term.guarded () (.var 0) (Term.step (.var 0) (.var 1)) (.var 2))) -- F_cb
    | 29 => ((Term.step (Term.step (Term.guarded () (.var 0) (Term.guarded () (.var 0) (Term.step (Term.step (.var 5) (.var 0)) (.var 1)) (.var 2)) (.var 2)) (.var 1)) (.var 0)), (Term.step (Term.step (Term.guarded () (.var 0) (Term.step (.var 5) (.var 0)) (.var 2)) (.var 1)) (.var 0))) -- capture
    | 30 => ((Term.step (Term.step (Term.guarded () (.var 0) (Term.step (Term.step (.var 5) (.var 0)) (.var 1)) (.var 2)) (.var 1)) (.var 0)), (Term.step (Term.step (Term.guarded () (.var 0) (Term.step (.var 5) (.var 0)) (.var 2)) (.var 1)) (.var 0))) -- weak_gate
    | 31 => ((Term.guarded () (.var 0) (Term.guarded () (.var 0) (.var 1) (.var 2)) (.var 2)), (Term.guarded () (.var 0) (Term.step (.var 1) (.var 0)) (.var 2))) -- terminal
    | 32 => ((Term.step (Term.step (Term.guarded () (.var 0) (.var 1) (.var 2)) (.var 0)) (Term.step (Term.step (Term.step (Term.step (.var 1) (.var 0)) (.var 0)) (Term.step (Term.step (.var 2) (.var 0)) (.var 0))) (.var 0))), (Term.step (Term.step (Term.step (.var 1) (.var 0)) (.var 0)) (Term.step (Term.step (.var 2) (.var 0)) (.var 0)))) -- terminal_bound
    | 33 => ((Term.step (Term.step (Term.guarded () (.var 0) (.var 1) (.var 2)) (.var 0)) (Term.step (Term.guarded () (.var 0) (Term.step (.var 1) (.var 0)) (.var 2)) (.var 0))), (Term.guarded () (.var 0) (Term.step (.var 1) (.var 0)) (.var 2))) -- terminal_weak
    | 34 => ((Term.step (Term.step (Term.step (.var 5) (.var 0)) (.var 1)) (.var 0)), (Term.guarded () (.var 0) (Term.step (Term.step (.var 5) (.var 0)) (.var 1)) (.var 1))) -- G_def
    | 35 => ((Term.guarded () (.var 0) (Term.step (.var 5) (.var 0)) (.var 1)), (Term.guarded () (.var 0) (Term.step (Term.step (.var 5) (.var 0)) (.var 0)) (.var 1))) -- K_def
    | 36 => ((Term.step (Term.step (.var 0) (.var 1)) (.var 0)), (Term.step (.var 1) (.var 0))) -- G_zero
    | 37 => ((Term.guarded () (.var 0) (Term.step (.var 0) (.var 1)) (.var 2)), (Term.guarded () (.var 0) (.var 1) (.var 2))) -- F_zero
    | 38 => ((Term.step (Term.step (Term.step (.var 5) (.var 0)) (.var 0)) (.var 0)), (Term.step (.var 5) (.var 0))) -- G_root
    | _ => ((Term.guarded () (.var 0) (Term.step (.var 5) (.var 0)) (.var 0)), (Term.step (.var 5) (.var 0))) -- K_root
  ⟨6, pair.1, pair.2⟩

/-- The explicitly listed theory, independent of semantic validity. -/
def theory : Equational.Theory (Symbol Unit) := Set.range basisAxiom

/-- The semantic law view of the same forty native equations. -/
structure Laws {M : Type u} (f : M → M → M) (h : M → M → M → M) : Prop where
  R1 (r : M) : (f r r) = r
  R2 (r a : M) : (f (f r a) r) = (f a r)
  R3 (r a : M) : (f (f r a) a) = (f r a)
  R4 (r a b : M) : (f r (f (f r a) b)) = (f r (f a b))
  R5 (r a b : M) : (f (f (f r a) b) a) = (f (f r b) a)
  R6 (r a b : M) : (f r (f a b)) = (f a (f r b))
  h_sym (r a b : M) : (h r a b) = (h r b a)
  h_minor (r a : M) : (h r a a) = (f a r)
  h_root (r a b : M) : (f (h r a b) r) = (h r a b)
  h_expand (r a b u : M) : (h (f u r) a b) = (f (f u r) (h r a b))
  h_split (r a b u v : M) : (h r (f u a) (f v b)) = (f (f (h r (f u a) b) r) (f (h r a (f v b)) r))
  h_back (r a b u : M) : (h r (f u a) b) = (h r (f (f u r) a) b)
  h_reroot (r a b u : M) : (f (h a u b) r) = (f (f (h r u b) a) r)
  h_insert (r a b : M) : (h r a b) = (h r (f r a) b)
  project_join (r a u v : M) : (f (f (f u a) (f v a)) r) = (f (f (f (f u a) r) r) (f (f (f v a) r) r))
  reset_split (a u v : M) : (f u (f v a)) = (f (f u a) (f v a))
  reset_back (r a u : M) : (f (f u a) r) = (f (f (f u r) a) r)
  project_idem (r u : M) : (f (f u r) r) = (f u r)
  root_preserve (r u v : M) : (f (f u (f v r)) r) = (f u (f v r))
  F_closed (r a b u : M) : (f (h r (f (f u r) a) b) r) = (h r (f (f u r) a) b)
  F_join (r a b u v : M) : (h r (f (f (f (f u r) r) (f (f v r) r)) a) b) = (f (f (h r (f (f u r) a) b) r) (f (h r (f (f v r) a) b) r))
  F_contract (r a b u : M) : (f (f (h r (f (f u r) a) b) r) (f (f (f (h r (f r a) b) r) (f (f u r) r)) r)) = (f (f (h r (f r a) b) r) (f (f u r) r))
  F_idem (r a b u : M) : (h r (f (h r (f (f u r) a) b) a) b) = (h r (f (f u r) a) b)
  F_band (r a b c d u : M) : (h r (f (h r (f (h r (f (f u r) a) b) c) d) a) b) = (h r (f (h r (f (f u r) c) d) a) b)
  F_Ga (r a b u : M) : (h r (f (f (f (f u r) a) r) a) b) = (h r (f (f u r) a) b)
  F_Ka (r a b u : M) : (h r (f (h r (f u r) a) a) b) = (h r (f (f u r) a) b)
  F_Kb (r a b u : M) : (h r (f (h r (f u r) b) a) b) = (h r (f (f u r) a) b)
  F_ca (r a b : M) : (h r (f (f a r) a) b) = (h r (f r a) b)
  F_cb (r a b : M) : (h r (f (f b r) a) b) = (h r (f r a) b)
  capture (r a b u : M) : (f (f (h r (h r (f (f u r) a) b) b) a) r) = (f (f (h r (f u r) b) a) r)
  weak_gate (r a b u : M) : (f (f (h r (f (f u r) a) b) a) r) = (f (f (h r (f u r) b) a) r)
  terminal (r a b : M) : (h r (h r a b) b) = (h r (f a r) b)
  terminal_bound (r a b : M) : (f (f (h r a b) r) (f (f (f (f a r) r) (f (f b r) r)) r)) = (f (f (f a r) r) (f (f b r) r))
  terminal_weak (r a b : M) : (f (f (h r a b) r) (f (h r (f a r) b) r)) = (h r (f a r) b)
  G_def (r a u : M) : (f (f (f u r) a) r) = (h r (f (f u r) a) a)
  K_def (r a u : M) : (h r (f u r) a) = (h r (f (f u r) r) a)
  G_zero (r a : M) : (f (f r a) r) = (f a r)
  F_zero (r a b : M) : (h r (f r a) b) = (h r a b)
  G_root (r u : M) : (f (f (f u r) r) r) = (f u r)
  K_root (r u : M) : (h r (f u r) r) = (f u r)


def resetOperation (M : Type u) [(Equational.language (Symbol Unit)).Structure M] (x y : M) : M :=
  FirstOrder.Language.Structure.funMap (L := Equational.language (Symbol Unit)) .reset
    (fun i => if i = 0 then x else y)

def guardedOperation (M : Type u) [(Equational.language (Symbol Unit)).Structure M] (x y z : M) : M :=
  FirstOrder.Language.Structure.funMap (L := Equational.language (Symbol Unit)) (.guarded ())
    (fun i => if i = 0 then x else if i = 1 then y else z)

/-- Fixed points of right reset by r, independent of the forty-law theory. -/
abbrev RootFiber {M : Type u} (f : M → M → M) (r : M) := {x : M // f x r = x}

end FiniteBasis

namespace Term

/-- The finite common-root word expansion. Each original variable occurrence
contributes one word, including independently repeated occurrences. -/
def actionWords {Var : Type v} : Term Unit Var → List (List (Var × Var))
  | .var j => [[(j, j)]]
  | .func .reset args =>
    ((actionWords (args 0)).map (fun w => (root (args 1), root (args 1)) :: w)) ++
      (actionWords (args 1))
  | .func (.guarded _) args =>
    (actionWords (args 0)) ++
      (((actionWords (args 1)).map (fun w =>
        (root (args 0), root (args 0)) ::
          (root (args 1), root (args 2)) :: w)) ++
        ((actionWords (args 2)).map (fun w =>
          (root (args 0), root (args 0)) ::
            (root (args 2), root (args 1)) :: w)))

end Term

end Owner
end KFOL
