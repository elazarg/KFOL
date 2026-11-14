module

public import Mathlib.Order.FixedPoints
public import Mathlib.Data.List.Basic

/-! # Infinite public games and objective-sensitive fixedpoints

Histories are finite words of moves. A profile chooses at every history,
including histories it does not reach. Equilibrium is specified by complete
unilateral replacements, independently of the fixedpoint formulas below.
-/

@[expose] public section

namespace KFOL.InfiniteGames

universe u v w

variable {V : Type u}

/-- Existential predecessor along a relation. -/
def pre (R : V → V → Prop) (S : Set V) : Set V :=
  {x | ∃ y, R x y ∧ y ∈ S}

/-- Universal predecessor, including the vacuous case at a dead end. -/
def allPre (R : V → V → Prop) (S : Set V) : Set V :=
  {x | ∀ y, R x y → y ∈ S}

def reachHom (R : V → V → Prop) (A : Set V) : Set V →o Set V where
  toFun X := A ∪ pre R X
  monotone' _ _ h _x hx := hx.elim Or.inl fun ⟨y, hxy, hy⟩ =>
    Or.inr ⟨y, hxy, h hy⟩

/-- `μ X. A ∪ Pre X`: a finite path to `A`. -/
def reach (R : V → V → Prop) (A : Set V) : Set V := (reachHom R A).lfp

def untilHom (R : V → V → Prop) (Q P Z : Set V) : Set V →o Set V where
  toFun Y := (P ∩ pre R Z) ∪ (Q ∩ pre R Y)
  monotone' _ _ h _x hx := hx.elim Or.inl fun ⟨hx, y, hxy, hy⟩ =>
    Or.inr ⟨hx, y, hxy, h hy⟩

def buchiHom (R : V → V → Prop) (Q P : Set V) : Set V →o Set V where
  toFun Z := (untilHom R Q P Z).lfp
  monotone' _ _ h := OrderHom.lfp.mono fun _Y _x hx =>
    hx.elim (fun ⟨hx, y, hxy, hy⟩ => Or.inl ⟨hx, y, hxy, h hy⟩) Or.inr

/-- `ν Z. μ Y. (P ∩ Pre Z) ∪ (Q ∩ Pre Y)`: visit `P` infinitely
often while remaining in `Q`, when `P ⊆ Q`. -/
def buchi (R : V → V → Prop) (Q P : Set V) : Set V := (buchiHom R Q P).gfp

/-- Independent path semantics for a Büchi objective inside a region. -/
def BuchiRun (R : V → V → Prop) (Q P : Set V) (x : V) : Prop :=
  ∃ π : ℕ → V, π 0 = x ∧ (∀ k, R (π k) (π (k + 1))) ∧
    (∀ k, π k ∈ Q) ∧ ∀ N, ∃ k, N ≤ k ∧ π k ∈ P

/-- A finite prefix followed by a path whose largest recurrent priority is `p`. -/
def priorityRegion {n : ℕ} (R : V → V → Prop) (priority : V → Fin n)
    (p : Fin n) : Set V :=
  reach R (buchi R {x | priority x ≤ p} {x | priority x = p})

/-- Full-action history tree: every move in `Move` is available at every
history, and owners and priorities may depend on the entire history. -/
structure PriorityGame (Role : Type u) (Move : Type v) (priorities : ℕ) where
  owner : List Move → Role
  priority : List Move → Fin priorities
  priorityWinner : Fin priorities → Role

/-- A finite or infinite arena with a total action-labelled successor
function. Vertex finiteness is not required. -/
structure PriorityArena (Role : Type u) (Move : Type v) (Vertex : Type w) (priorities : ℕ) where
  owner : Vertex → Role
  priority : Vertex → Fin priorities
  priorityWinner : Fin priorities → Role
  successor : Vertex → Move → Vertex

/-- Unfold an action-labelled arena into its full history tree, retaining
complete action histories even when the arena revisits a vertex. -/
def PriorityArena.unfold {Role : Type u} {Move : Type v} {Vertex : Type w} {n : ℕ}
    (G : PriorityArena Role Move Vertex n) (initial : Vertex) : PriorityGame Role Move n where
  owner h := G.owner (h.foldl G.successor initial)
  priority h := G.priority (h.foldl G.successor initial)
  priorityWinner := G.priorityWinner

abbrev Profile (Move : Type v) := List Move → Move

def legal {Move : Type v} (h k : List Move) : Prop := ∃ a, k = h ++ [a]

def profileRel {Move : Type v} (σ : Profile Move) (h k : List Move) : Prop :=
  k = h ++ [σ h]

def run {Move : Type v} (σ : Profile Move) (h : List Move) : ℕ → List Move
  | 0 => h
  | k + 1 => run σ h k ++ [σ (run σ h k)]

namespace PriorityGame

def deviationRel {Role : Type u} {Move : Type v} {n : ℕ}
    (G : PriorityGame Role Move n) (σ : Profile Move) (i : Role)
    (h k : List Move) : Prop :=
  ∃ a, k = h ++ [a] ∧ (G.owner h ≠ i → a = σ h)

/-- Whole-player replacement, preserving every other owner's choice. -/
def Deviation {Role : Type u} {Move : Type v} {n : ℕ}
    (G : PriorityGame Role Move n) (i : Role) (σ τ : Profile Move) : Prop :=
  ∀ h, G.owner h ≠ i → τ h = σ h

/-- The maximum priority occurring infinitely often, stated without a
chosen winner or a fixedpoint computation. -/
def DominantPriority {Role : Type u} {Move : Type v} {n : ℕ}
    (G : PriorityGame Role Move n) (π : ℕ → List Move) (p : Fin n) : Prop :=
  (∀ N, ∃ k, N ≤ k ∧ G.priority (π k) = p) ∧
    ∃ N, ∀ k, N ≤ k → G.priority (π k) ≤ p

def Wins {Role : Type u} {Move : Type v} {n : ℕ}
    (G : PriorityGame Role Move n) (i : Role) (π : ℕ → List Move) : Prop :=
  ∃ p, G.priorityWinner p = i ∧ G.DominantPriority π p

def IsNash {Role : Type u} {Move : Type v} {n : ℕ}
    (G : PriorityGame Role Move n) (σ : Profile Move) (h : List Move) : Prop :=
  ∀ i τ, G.Deviation i σ τ → G.Wins i (run τ h) → G.Wins i (run σ h)

/-- Nash after every finite continuation, reached or not. -/
def IsSubgamePerfect {Role : Type u} {Move : Type v} {n : ℕ}
    (G : PriorityGame Role Move n) (σ : Profile Move) (h : List Move) : Prop :=
  ∀ suffix, G.IsNash σ (h ++ suffix)

def possibleWinners {Role : Type u} {Move : Type v} {n : ℕ}
    (G : PriorityGame Role Move n) (h : List Move) : Set Role :=
  {i | ∃ σ, G.IsSubgamePerfect σ h ∧ G.Wins i (run σ h)}

/-- Objective-sensitive winning region under a selected transition relation. -/
def winRegion {Role : Type u} {Move : Type v} {n : ℕ}
    (G : PriorityGame Role Move n) (R : List Move → List Move → Prop)
    (i : Role) : Set (List Move) :=
  {h | ∃ p, G.priorityWinner p = i ∧ h ∈ priorityRegion R G.priority p}

def equilibriumHom {Role : Type u} {Move : Type v} {n : ℕ}
    (G : PriorityGame Role Move n) (σ : Profile Move) :
    Set (List Move) →o Set (List Move) where
  toFun Z := {h | ∀ i, h ∈ G.winRegion (deviationRel G σ i) i →
      h ∈ G.winRegion (profileRel σ) i} ∩ allPre legal Z
  monotone' _ _ h _ hx := ⟨hx.1, fun y hy => h (hx.2 y hy)⟩

/-- `ν Z. (all full-deviation tests succeed) ∩ □ Z`. -/
def equilibriumRegion {Role : Type u} {Move : Type v} {n : ℕ}
    (G : PriorityGame Role Move n) (σ : Profile Move) : Set (List Move) :=
  (equilibriumHom G σ).gfp

def fixedpointPossibleWinners {Role : Type u} {Move : Type v} {n : ℕ}
    (G : PriorityGame Role Move n) (h : List Move) : Set Role :=
  {i | ∃ σ, h ∈ G.equilibriumRegion σ ∧ h ∈ G.winRegion (profileRel σ) i}

end PriorityGame

end KFOL.InfiniteGames
