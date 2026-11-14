module

public import KFOL.Definitions.Public

/-! # Public grafting of arbitrary continuation games

The continuation interface records complete plans and their independent
equilibrium predicate. It imposes no existence or termination assumption.
-/

@[expose] public section

namespace KFOL.InfiniteGames.PublicGrafting

universe u v w

structure Continuation (Role : Type u) where
  Plan : Type v
  winner : Plan → Role
  deviation : Role → Plan → Plan → Prop
  deviation_refl : ∀ i p, deviation i p p
  perfect : Plan → Prop
  perfect_nash : ∀ p, perfect p →
    ∀ i q, deviation i p q → winner q = i → winner p = i

namespace Continuation

variable {Role : Type u}

def possibleWinners (G : Continuation.{u, v} Role) : Set Role :=
  {i | ∃ p, G.perfect p ∧ G.winner p = i}

end Continuation

structure GraftPlan {Role : Type u} (G : Continuation.{u, v} Role)
    (H : Continuation.{u, w} Role) where
  action : Bool
  left : G.Plan
  right : H.Plan

namespace GraftPlan

variable {Role : Type u} {G : Continuation.{u, v} Role} {H : Continuation.{u, w} Role}

def winner (p : GraftPlan G H) : Role :=
  if p.action then H.winner p.right else G.winner p.left

def Deviation (owner player : Role) (p q : GraftPlan G H) : Prop :=
  (owner ≠ player → p.action = q.action) ∧
    G.deviation player p.left q.left ∧ H.deviation player p.right q.right

def IsNash (owner : Role) (p : GraftPlan G H) : Prop :=
  ∀ i q, Deviation owner i p q → winner q = i → winner p = i

/-- Nash at the new root and perfection in both continuation games. -/
def IsSubgamePerfect (owner : Role) (p : GraftPlan G H) : Prop :=
  IsNash owner p ∧ G.perfect p.left ∧ H.perfect p.right

end GraftPlan

def possibleWinners {Role : Type u} (owner : Role) (G : Continuation.{u, v} Role)
    (H : Continuation.{u, w} Role) : Set Role :=
  {i | ∃ p : GraftPlan G H, p.IsSubgamePerfect owner ∧ p.winner = i}

/-- Empty SPE sets propagate even through an unchosen continuation.
On nonempty sets this is exactly the paper's owned choice. -/
noncomputable def strictChoice {Role : Type u} (owner : Role) (S T : Set Role) : Set Role :=
  if S = ∅ ∨ T = ∅ then ∅
  else if S = {owner} ∨ T = {owner} then {owner} else S ∪ T

end KFOL.InfiniteGames.PublicGrafting
