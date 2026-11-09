module

public import KFOL.Definitions.Owner

/-! # Selective reset with an indexed family of blocking policies

Policies are independent sets of roles. Native syntax retains each original
ternary policy occurrence, even when different indices name the same policy.
-/

@[expose] public section

namespace KFOL

universe u v w

namespace WinnerSet

/-- Exactly the policy's named atoms block the third input. -/
def PolicyBlocks {Role : Type u} (D : Set Role) (Y : WinnerSet Role) : Prop :=
  ∃ r ∈ D, Y = singleton r

/-- Selective reset, before the outer root reset. -/
noncomputable def selective {Role : Type u} (D : Set Role) (Z Y : WinnerSet Role) : WinnerSet Role := by
  classical
  exact if PolicyBlocks D Y then Y else Y.union Z

/-- The paper's rooted policy operation R_D(X,Y,Z). -/
noncomputable def policyReset {Role : Type u} (D : Set Role) (X Y Z : WinnerSet Role) : WinnerSet Role :=
  (selective D Z Y).reset X

/-- Passing at one observer excludes the other policy atoms. -/
def PolicyPasses {Role : Type u} (D : Set Role) (observer : Role) (Y : WinnerSet Role) : Prop :=
  ∀ r ∈ D, r ≠ observer → Y ≠ singleton r

/-- The two-owned-choice expression G from the main text, independently of R. -/
noncomputable def twoOwnerSelective {Role : Type u} (a b : Role) (X Y Z : WinnerSet Role) : WinnerSet Role :=
  (choice a (choice b Y Z) Y).reset X

end WinnerSet

namespace Policies

/-- Native reset and each indexed ternary policy symbol. -/
inductive Symbol (Label : Type w) : ℕ → Type w
  | reset : Symbol Label 2
  | selective (label : Label) : Symbol Label 3

abbrev Term (Label : Type w) (Var : Type v) := Equational.Term (Symbol Label) Var

@[instance_reducible] noncomputable def structureOf {Role : Type u} {Label : Type w}
    (D : Label → Set Role) : (Equational.language (Symbol Label)).Structure (WinnerSet Role) where
  funMap f args := match f with
    | .reset => (args 0).reset (args 1)
    | .selective d => WinnerSet.policyReset (D d) (args 0) (args 1) (args 2)
  RelMap r := nomatch r

namespace Term

variable {Label : Type w} {Var : Type v}

def step (s t : Term Label Var) : Term Label Var :=
  .func .reset (fun i => if i = 0 then s else t)

def selective (d : Label) (x y z : Term Label Var) : Term Label Var :=
  .func (.selective d) (fun i => if i = 0 then x else if i = 1 then y else z)

def root : Term Label Var → Var
  | .var j => j
  | .func .reset args => root (args 1)
  | .func (.selective _) args => root (args 0)

noncomputable def eval {Role : Type u} (D : Label → Set Role) (t : Term Label Var) (v : Var → WinnerSet Role) : WinnerSet Role :=
  let _ := structureOf D
  t.realize v

def leafCount : Term Label Var → ℕ
  | .var _ => 1
  | .func .reset args => leafCount (args 0) + leafCount (args 1)
  | .func (.selective _) args => leafCount (args 0) + leafCount (args 1) + leafCount (args 2)

def size : Term Label Var → ℕ
  | .var _ => 1
  | .func .reset args => 1 + size (args 0) + size (args 1)
  | .func (.selective _) args => 1 + size (args 0) + size (args 1) + size (args 2)

end Term

/-- One source contribution, with positive ambiguity and labelled passing tests. -/
structure Guard (Label : Type w) (Var : Type v) where
  source : Var
  many : List Var := []
  passes : List (Label × Var) := []
  deriving DecidableEq

def Guard.addMany {Label : Type w} {Var : Type v} (j : Var) (g : Guard Label Var) : Guard Label Var :=
  { g with many := j :: g.many }

def Guard.addPass {Label : Type w} {Var : Type v} (d : Label) (j : Var) (g : Guard Label Var) : Guard Label Var :=
  { g with passes := (d, j) :: g.passes }

def Guard.Holds {Label : Type w} {Var : Type v} (M : Var → Prop) (N : Label → Var → Prop)
    (V : Var → Prop) (g : Guard Label Var) : Prop :=
  (∀ j ∈ g.many, M j) ∧ (∀ p ∈ g.passes, N p.1 p.2) ∧ V g.source

def Eval {Label : Type w} {Var : Type v} (guards : List (Guard Label Var))
    (M : Var → Prop) (N : Label → Var → Prop) (V : Var → Prop) : Prop :=
  ∃ g ∈ guards, g.Holds M N V

/-- One common raw guard per original native leaf, before any normalization. -/
def Term.guards {Label : Type w} {Var : Type v} : Term Label Var → List (Guard Label Var)
  | .var j => [⟨j, [], []⟩]
  | .func .reset args => guards (args 1) ++ (guards (args 0)).map (Guard.addMany (Term.root (args 1)))
  | .func (.selective d) args => guards (args 0) ++
    ((guards (args 1) ++ (guards (args 2)).map (Guard.addPass d (Term.root (args 1)))).map
      (Guard.addMany (Term.root (args 0))))

/-- Forget the repeated label in a signature with one fixed policy. -/
def Guard.toSingle {Label : Type w} {Var : Type v} (g : Guard Label Var) : Owner.Guard Var :=
  ⟨g.source, g.many, g.passes.map Prod.snd⟩

def Term.singleGuards {Label : Type w} {Var : Type v} (t : Term Label Var) : List (Owner.Guard Var) :=
  t.guards.map Guard.toSingle

/-- The common single-policy comparison inspects only native syntax.
Its correctness is proved independently for every nontrivial policy. -/
def Term.singleEquationB {Label : Type w} {Var : Type v} [DecidableEq Var]
    (left right : Term Label Var) : Bool :=
  Owner.coversB left.singleGuards right.singleGuards && Owner.coversB right.singleGuards left.singleGuards

/-- The passing pattern is indexed by symbols, including repeated policies. -/
def passingPattern {Role : Type u} {Label : Type w} (D : Label → Set Role) (r : Role) : Set Label :=
  {d | r ∉ D d}

def PatternChain {Role : Type u} {Label : Type w} (D : Label → Set Role) : Prop :=
  ∀ r s, passingPattern D r ⊆ passingPattern D s ∨ passingPattern D s ⊆ passingPattern D r

def PatternIntersectionClosed {Role : Type u} {Label : Type w} (D : Label → Set Role) : Prop :=
  ∀ r s, ∃ t, passingPattern D t = passingPattern D r ∩ passingPattern D s

def RepeatedPattern {Role : Type u} {Label : Type w} (D : Label → Set Role) : Prop :=
  ∃ r s, r ≠ s ∧ passingPattern D r = passingPattern D s

/-- The classification criterion, independent of equation validity or algorithms. -/
def FamilyEasy {Role : Type u} {Label : Type w} (D : Label → Set Role) : Prop :=
  PatternChain D ∨ PatternIntersectionClosed D ∧ RepeatedPattern D

/-- The blocking set imposed by a conjunction of finitely many policy tests. -/
def blockingUnion {Role : Type u} {Label : Type w} [DecidableEq Role]
    (D : Label → Finset Role) : List Label → Finset Role
  | [] => ∅
  | d :: rest => D d ∪ blockingUnion D rest

/-- Passing labels imposed at a single input of a guard. -/
def Guard.labelsAt {Label : Type w} {Var : Type v} [DecidableEq Var]
    (i : Var) (g : Guard Label Var) : List Label :=
  (g.passes.filter (fun p => p.2 = i)).map Prod.fst

def Guard.blockingAt {Role : Type u} {Label : Type w} {Var : Type v}
    [DecidableEq Role] [DecidableEq Var] (D : Label → Finset Role) (i : Var) (g : Guard Label Var) : Finset Role :=
  blockingUnion D (g.labelsAt i)

/-- A full blocking collision is replaced by ambiguity; its lost atomic
source case is supplied by the second child's unguarded root contribution. -/
def Guard.normalizeAt {Role : Type u} {Label : Type w} {Var : Type v}
    [DecidableEq Role] [DecidableEq Var] (D : Label → Finset Role) (top : Finset Role)
    (i : Var) (g : Guard Label Var) : Guard Label Var :=
  if g.blockingAt D i = top then g.addMany i else g

/-- The normalized native compiler introduces no additional guard records.
It inspects only the one input whose passing requirements just grew. -/
def Term.normalGuards {Role : Type u} {Label : Type w} {Var : Type v}
    [DecidableEq Role] [DecidableEq Var] (D : Label → Finset Role) (top : Finset Role) :
    Term Label Var → List (Guard Label Var)
  | .var j => [⟨j, [], []⟩]
  | .func .reset args => normalGuards D top (args 1) ++
      (normalGuards D top (args 0)).map (Guard.addMany (Term.root (args 1)))
  | .func (.selective d) args =>
      let third := ((normalGuards D top (args 2)).map (Guard.addPass d (Term.root (args 1)))).map
        (Guard.normalizeAt D top (Term.root (args 1)))
      normalGuards D top (args 0) ++
        (normalGuards D top (args 1) ++ third).map (Guard.addMany (Term.root (args 0)))

/-- Nonsource inputs without an ambiguity requirement retain a proper
blocking union. Source and ambiguity requirements already imply every pass. -/
def Guard.Normalized {Role : Type u} {Label : Type w} {Var : Type v}
    [DecidableEq Role] [DecidableEq Var] (D : Label → Finset Role) (top : Finset Role) (g : Guard Label Var) : Prop :=
  ∀ i, i ≠ g.source → i ∉ g.many → g.blockingAt D i ≠ top

/-- Coverage under the supplied blocking sets, with ambiguity and the source
membership discharging their own passing requirements. -/
def Guard.Dominates {Role : Type u} {Label : Type w} {Var : Type v}
    [DecidableEq Role] [DecidableEq Var] (D : Label → Finset Role) (weak strong : Guard Label Var) : Prop :=
  weak.source = strong.source ∧ (∀ i ∈ weak.many, i ∈ strong.many) ∧
    ∀ p ∈ weak.passes, p.2 ∈ strong.many ∨ p.2 = strong.source ∨ D p.1 ⊆ strong.blockingAt D p.2

def Covers {Role : Type u} {Label : Type w} {Var : Type v}
    [DecidableEq Role] [DecidableEq Var] (D : Label → Finset Role) (left right : List (Guard Label Var)) : Prop :=
  ∀ g ∈ left, ∃ h ∈ right, h.Dominates D g

def dominatesB {Role : Type u} {Label : Type w} {Var : Type v}
    [DecidableEq Role] [DecidableEq Var] (D : Label → Finset Role) (weak strong : Guard Label Var) : Bool :=
  decide (weak.source = strong.source) && weak.many.all (fun i => decide (i ∈ strong.many)) &&
    weak.passes.all (fun p => decide (p.2 ∈ strong.many ∨ p.2 = strong.source ∨ D p.1 ⊆ strong.blockingAt D p.2))

def coversB {Role : Type u} {Label : Type w} {Var : Type v}
    [DecidableEq Role] [DecidableEq Var] (D : Label → Finset Role) (left right : List (Guard Label Var)) : Bool :=
  left.all (fun g => right.any (fun h => dominatesB D h g))

/-- Observation comparison by the normalized native guard lists. -/
def Term.familyObservationB {Role : Type u} {Label : Type w} {Var : Type v}
    [DecidableEq Role] [DecidableEq Var] (D : Label → Finset Role) (top : Finset Role)
    (left right : Term Label Var) : Bool :=
  coversB D (left.normalGuards D top) (right.normalGuards D top) &&
    coversB D (right.normalGuards D top) (left.normalGuards D top)

/-- The explicit atom-or-pair valuation used in guard separation. The
nonsource atoms are supplied independently; their least-vector property is proved. -/
def Guard.atomPairVal {Role : Type u} {Label : Type w} {Var : Type v} [DecidableEq Var]
    (observer first second : Role) (atoms : Var → Role) (g : Guard Label Var) (i : Var) : WinnerSet Role :=
  if i = g.source then
    if i ∈ g.many then (WinnerSet.singleton observer).union (WinnerSet.singleton first)
      else WinnerSet.singleton observer
  else if i ∈ g.many then (WinnerSet.singleton first).union (WinnerSet.singleton second)
  else WinnerSet.singleton (atoms i)

/-- Every proper conjunction has an atom different from the observer whose
passing vector contains exactly the consequences of that conjunction. -/
def HasLeastAtoms {Role : Type u} {Label : Type w} [DecidableEq Role]
    (D : Label → Finset Role) (top : Finset Role) (k : Role) : Prop :=
  ∀ labels : List Label, blockingUnion D labels ≠ top →
    ∃ t, t ≠ k ∧ t ∉ blockingUnion D labels ∧
      ∀ d, t ∉ D d ↔ D d ⊆ blockingUnion D labels

/-- Explicit finite passing patterns for the classification program. Both
role and symbol dictionaries are input lists, so repeated names cannot
create a false multiplicity and numeric labels do not set iteration bounds. -/
def passingFinset {Role : Type u} {Label : Type w} [DecidableEq Role] [DecidableEq Label]
    (D : Label → Finset Role) (labels : List Label) (r : Role) : Finset Label :=
  (labels.filter (fun d => r ∉ D d)).toFinset

/-- Row comparability of the explicitly listed passing-pattern matrix. -/
def patternChainB {Role : Type u} {Label : Type w} [DecidableEq Role] [DecidableEq Label]
    (D : Label → Finset Role) (roles : List Role) (labels : List Label) : Bool :=
  let pattern := passingFinset D labels
  roles.all (fun r => roles.all (fun s => decide (pattern r ⊆ pattern s ∨ pattern s ⊆ pattern r)))

/-- Decide the exact family criterion by bounded scans of the supplied
role/policy descriptions. Correctness needs dictionary coverage, not sorting. -/
def familyEasyB {Role : Type u} {Label : Type w} [DecidableEq Role] [DecidableEq Label]
    (D : Label → Finset Role) (roles : List Role) (labels : List Label) : Bool :=
  let pattern := passingFinset D labels
  patternChainB D roles labels ||
    (roles.all (fun r => roles.all (fun s => roles.any (fun t => decide (pattern t = pattern r ∩ pattern s)))) &&
      roles.any (fun r => roles.any (fun s => decide (r ≠ s ∧ pattern r = pattern s))))

/-- The native equation checker for the two tractable branches. Chain
families compare every observer; the other branch uses the common guard
comparison on the original policies. Correctness requires FamilyEasy. -/
def Term.familyEquationB {Role : Type u} {Label : Type w} {Var : Type v}
    [DecidableEq Role] [DecidableEq Label] [DecidableEq Var] (D : Label → Finset Role)
    (roles : List Role) (labels : List Label) (left right : Term Label Var) : Bool :=
  if patternChainB D roles labels then
    roles.all (fun k => familyObservationB (fun d => (D d).erase k) (roles.toFinset.erase k) left right)
  else familyObservationB D roles.toFinset left right

end Policies
end KFOL
