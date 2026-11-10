module

public import KFOL.Definitions.Strategic

/-! # Public trees with arbitrary nonempty action sets

Trees are inductively well founded; a uniform finite depth is an additional
predicate. Full profiles and whole-player deviations include every action,
including actions outside a later finite pruning. Equilibrium definitions do
not use the owned-choice algebra or a winner-set recursion.
-/

@[expose] public section

namespace KFOL.Strategic

universe u v

/-- A well-founded public tree. Action types may depend on the entire history
and need not be finite or countable. Empty decisions are excluded. -/
inductive QuantifiedTree (Role : Type u) : Type (max u (v+1)) where
  | leaf (winner : Role)
  | node (owner : Role) (Action : Type v) (nonempty : Nonempty Action)
      (next : Action → QuantifiedTree Role)

namespace QuantifiedTree

variable {Role : Type u}

/-- The chosen action and full contingent plans for every continuation. -/
def Profile : QuantifiedTree.{u,v} Role → Type (max u v)
  | .leaf _ => PUnit
  | .node _ Action _ next => Action × ((a : Action) → Profile (next a))

def winner : {game : QuantifiedTree.{u,v} Role} → Profile game → Role
  | .leaf r, _ => r
  | .node _ _ _ _, plan => winner (plan.2 plan.1)

/-- A replacement may alter all of the player's decisions, also off the
realized path; choices owned by another player are fixed. -/
def Deviation (player : Role) :
    {game : QuantifiedTree.{u,v} Role} → Profile game → Profile game → Prop
  | .leaf _, _, _ => True
  | .node owner _ _ _, source, target =>
      (owner ≠ player → source.1 = target.1) ∧
        ∀ a, Deviation player (source.2 a) (target.2 a)

def IsNash {game : QuantifiedTree.{u,v} Role} (plan : Profile game) : Prop :=
  ∀ player, ∀ replacement : Profile game,
    Deviation player plan replacement → winner replacement = player → winner plan = player

/-- Nash equilibrium at every subgame. This recurses only over subgames and
uses complete deviations, not local optimality or the algebraic recurrence. -/
def IsSubgamePerfect : {game : QuantifiedTree.{u,v} Role} → Profile game → Prop
  | .leaf _, plan => IsNash plan
  | .node _ _ _ _, plan => IsNash plan ∧ ∀ a, IsSubgamePerfect (plan.2 a)

def possibleWinners (game : QuantifiedTree.{u,v} Role) : Set Role :=
  {player | ∃ plan : Profile game, IsSubgamePerfect plan ∧ winner plan = player}

/-- At most n decisions occur along any play, with no bound on branching. -/
def DepthLE : ℕ → QuantifiedTree.{u,v} Role → Prop
  | _, .leaf _ => True
  | 0, .node _ _ _ _ => False
  | n+1, .node _ _ _ next => ∀ a, DepthLE n (next a)

/-- A binary owned-choice fold of an explicitly ordered list of inputs.
Only helper nodes of the specified owner are added. The list records each
input occurrence, independently of its compiled game's internal syntax. -/
inductive BinaryFold {Index : Type v} (owner : Role) (inputs : Index → Strategic.Tree Role) :
    List Index → Strategic.Tree Role → Prop where
  | single (i : Index) : BinaryFold owner inputs [i] (inputs i)
  | node {left right : List Index} {first second : Strategic.Tree Role}
      (leftFold : BinaryFold owner inputs left first)
      (rightFold : BinaryFold owner inputs right second) :
      BinaryFold owner inputs (left ++ right) (.node owner first second)

/-- Structural binary compilation: retain every action exactly once at each
source node, recursively compile its continuation, and fold the results using
only the original owner's binary nodes. This definition has no evaluation,
equilibrium, or semantic equality premise. -/
inductive Compiles : QuantifiedTree.{u,v} Role → Strategic.Tree Role → Prop where
  | leaf (r : Role) : Compiles (.leaf r) (.leaf r)
  | node {owner : Role} {Action : Type v} {nonempty : Nonempty Action}
      {next : Action → QuantifiedTree.{u,v} Role}
      (actions : List Action) (distinct : actions.Nodup) (complete : ∀ a, a ∈ actions)
      (children : Action → Strategic.Tree Role)
      (compiled : ∀ a, Compiles (next a) (children a))
      {binary : Strategic.Tree Role} (fold : BinaryFold owner children actions binary) :
      Compiles (.node owner Action nonempty next) binary

/-- A structural pruning keeps original owners and a nonempty finite subset
of original actions at each retained node. The bound applies at every node;
no equilibrium or semantic equality occurs in this definition. -/
inductive Prunes (bound : ℕ) : QuantifiedTree.{u,v} Role → QuantifiedTree.{u,v} Role → Prop where
  | leaf (r : Role) : Prunes bound (.leaf r) (.leaf r)
  | node {owner : Role} {Action : Type v} {nonempty : Nonempty Action}
      {next : Action → QuantifiedTree.{u,v} Role}
      (support : Finset Action) (inhabited : Nonempty support) (small : support.card ≤ bound)
      (children : support → QuantifiedTree.{u,v} Role)
      (sub : ∀ a, Prunes bound (next a.val) (children a)) :
      Prunes bound (.node owner Action nonempty next) (.node owner support inhabited children)

/-- Every retained subgame has the same actual SPE winners as its matched
original subgame. This strengthens structural pruning without changing the
independent equilibrium predicates or the structural relation above. -/
inductive Prunes.PreservesValues {bound : ℕ} :
    {source target : QuantifiedTree.{u,v} Role} → Prunes bound source target → Prop where
  | leaf (r : Role) : PreservesValues (Prunes.leaf (bound := bound) r)
  | node {owner : Role} {Action : Type v} {nonempty : Nonempty Action}
      {next : Action → QuantifiedTree.{u,v} Role}
      {support : Finset Action} {inhabited : Nonempty support} {small : support.card ≤ bound}
      {children : support → QuantifiedTree.{u,v} Role}
      {sub : ∀ a, Prunes bound (next a.val) (children a)}
      (equal : possibleWinners (.node owner support inhabited children) =
        possibleWinners (.node owner Action nonempty next))
      (preserved : ∀ a, PreservesValues (sub a)) :
      PreservesValues (Prunes.node (owner := owner) (nonempty := nonempty)
        support inhabited small children sub)

end QuantifiedTree
end KFOL.Strategic
