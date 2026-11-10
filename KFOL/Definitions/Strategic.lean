module

public import KFOL.Definitions.Public
public import GameTheory.Core.Equilibrium

/-! # Public games, full plans, deviations and independently specified SPE -/

@[expose] public section

namespace KFOL.Strategic

universe u v

inductive Tree (α : Type u) where
  | leaf (winner : α)
  | node (owner : α) (left right : Tree α)

inductive Profile {α : Type u} : Tree α → Type u where
  | leaf (w : α) : Profile (.leaf w)
  | node {left right : Tree α} (r : α) (action : Bool)
      (p : Profile left) (q : Profile right) : Profile (.node r left right)

def winner {α : Type u} {g : Tree α} (p : Profile g) : α :=
  match p with
  | .leaf w => w
  | .node _ action left right => if action then winner right else winner left

inductive Deviation {α : Type u} (i : α) :
    {g : Tree α} → Profile g → Profile g → Prop where
  | leaf (w : α) : Deviation i (.leaf w) (.leaf w)
  | node {left right : Tree α} {r : α} {a b : Bool}
      {p p' : Profile left} {q q' : Profile right}
      (root : r ≠ i → a = b) (l : Deviation i p p') (h : Deviation i q q') :
      Deviation i (.node r a p q) (.node r b p' q')


def IsNash {α : Type u} {g : Tree α} (p : Profile g) : Prop :=
  ∀ i, ∀ q : Profile g, Deviation i p q → winner q = i → winner p = i

/-- Restriction to any subtree, including unreached branches. -/
inductive Restriction {α : Type u} : {g h : Tree α} → Profile g → Profile h → Prop where
  | refl {g} (p : Profile g) : Restriction p p
  | left {g h k} {r : α} {a : Bool} {p : Profile g} {q : Profile h} {s : Profile k}
      (sub : Restriction p s) : Restriction (.node r a p q) s
  | right {g h k} {r : α} {a : Bool} {p : Profile g} {q : Profile h} {s : Profile k}
      (sub : Restriction q s) : Restriction (.node r a p q) s

/-- Whole-player deviation optimality in every subtree. No backward recursion
or local optimality rule is used in this definition. -/
def IsSubgamePerfect {α : Type u} {g : Tree α} (p : Profile g) : Prop :=
  ∀ {h : Tree α} (q : Profile h), Restriction p q → IsNash q


def possibleWinners {α : Type u} (g : Tree α) : Set α :=
  fun i => ∃ p : Profile g, IsSubgamePerfect p ∧ winner p = i


namespace Profile

def action {α : Type u} {r : α} {left right : Tree α} : Profile (.node r left right) → Bool
  | .node _ a _ _ => a

def left {α : Type u} {r : α} {l h : Tree α} : Profile (.node r l h) → Profile l
  | .node _ _ p _ => p

def right {α : Type u} {r : α} {l h : Tree α} : Profile (.node r l h) → Profile h
  | .node _ _ _ q => q

end Profile

/-- Assemble player plans by reading only the actual owner's coordinate at
each decision site. Other entries in a player's plan are irrelevant. -/
def assemble {α : Type u} : (g : Tree α) → (α → Profile g) → Profile g
  | .leaf w, _ => .leaf w
  | .node r l h, plans => .node r (plans r).action
      (assemble l (fun i => (plans i).left)) (assemble h (fun i => (plans i).right))


/-- The game's strategic form uses genuine player-indexed plans. Redundant
entries at other owners' sites are ignored by assemble. -/
noncomputable abbrev gameForm {α : Type u} (g : Tree α) : GameTheory.GameForm α :=
  GameTheory.GameForm.deterministic
    { Strategy := fun _ => Profile g, Outcome := α } (fun plans => winner (assemble g plans))

/-- A player prefers a larger probability of its own victory. -/
def winningPreference (α : Type u) : GameTheory.WeakPreference α α :=
  fun i preferred alternative => alternative i ≤ preferred i


/-- Joint deviations by all opponents, preserving the designated player's
complete contingent choices, including choices off the path. -/
inductive OpponentDeviation {α : Type u} (i : α) :
    {g : Tree α} → Profile g → Profile g → Prop where
  | leaf (w : α) : OpponentDeviation i (.leaf w) (.leaf w)
  | node {left right : Tree α} {r : α} {a b : Bool}
      {p p' : Profile left} {q q' : Profile right}
      (root : r = i → a = b) (l : OpponentDeviation i p p')
      (h : OpponentDeviation i q q') :
      OpponentDeviation i (.node r a p q) (.node r b p' q')

/-- A role can force victory when it has a complete plan that wins against
every joint opponent replacement. Equilibria do not occur in this definition. -/
def CanForce {α : Type u} (g : Tree α) (i : α) : Prop :=
  ∃ p : Profile g, ∀ q : Profile g, OpponentDeviation i p q → winner q = i

/-- Apply an internal role switch to owners and winner leaves alike. -/
def Tree.rename {Role : Type u} (p : Equiv.Perm Role) : Tree Role → Tree Role
  | .leaf i => .leaf (p i)
  | .node r g h => .node (p r) (g.rename p) (h.rename p)

/-- Transport the full contingent plan, preserving all off-path actions. -/
def Profile.rename {Role : Type u} (p : Equiv.Perm Role) :
    {g : Tree Role} → Profile g → Profile (g.rename p)
  | _, .leaf i => .leaf (p i)
  | _, .node r a g h => .node (p r) a (g.rename p) (h.rename p)

/-- Compile the full public syntax. Repeated occurrences insert distinct tree
positions; no equality of strategies is imposed on repeated components. -/
def compile {Role : Type u} {Var : Type v} (components : Var → Tree Role) :
    Term Role Var → Tree Role
  | .winner r => .leaf r
  | .var x => components x
  | .choice r s t => .node r (compile components s) (compile components t)
  | .rename p t => (compile components t).rename p

end KFOL.Strategic

namespace KFOL.Strategic.FiniteChoice

universe u v
variable {Role : Type u} {Index : Type v}

/-- A simultaneous full plan for one observed finite-action decision and all
of its continuation subgames, including every unchosen action. -/
structure Profile (branches : Index → Tree Role) where
  action : Index
  continuation : ∀ i, Strategic.Profile (branches i)

def winner {branches : Index → Tree Role} (plan : Profile branches) : Role :=
  Strategic.winner (plan.continuation plan.action)

/-- One player's replacement changes all its continuation decisions and may
change the initial action precisely when that player owns the decision. -/
def Deviation (owner player : Role) {branches : Index → Tree Role}
    (source target : Profile branches) : Prop :=
  (owner ≠ player → source.action = target.action) ∧
    ∀ i, Strategic.Deviation player (source.continuation i) (target.continuation i)

def IsNash (owner : Role) {branches : Index → Tree Role} (plan : Profile branches) : Prop :=
  ∀ player, ∀ replacement : Profile branches,
    Deviation owner player plan replacement → winner replacement = player → winner plan = player

/-- Nash at the observed root and every subtree. Continuation perfection is
the existing full-deviation/subtree predicate; no winner recurrence is assumed. -/
def IsSubgamePerfect (owner : Role) {branches : Index → Tree Role} (plan : Profile branches) : Prop :=
  IsNash owner plan ∧ ∀ i, Strategic.IsSubgamePerfect (plan.continuation i)

def possibleWinners (owner : Role) (branches : Index → Tree Role) : Set Role :=
  {player | ∃ plan : Profile branches, IsSubgamePerfect owner plan ∧ winner plan = player}

end KFOL.Strategic.FiniteChoice
