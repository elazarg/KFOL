module

public import KFOL.Definitions.Core
public import Mathlib.Combinatorics.SimpleGraph.Clique

/-! # Finite colored-graph realizations of source guards

Vertices are independent occurrences of input variables. Edges carry owners.
The predicates below use graph colors, maximal cliques and singleton tests;
they do not refer to term syntax or a saturation procedure.
-/

@[expose] public section

namespace KFOL.Core.ColoredGraph

universe u v w

/-- An owner color for each edge of a complete graph. Diagonal colors are unused. -/
structure Graph (Role : Type u) (Vertex : Type v) where
  color : Vertex → Vertex → Role
  symm : ∀ x y, color x y = color y x

variable {Role : Type u} {Vertex : Type v} {Var : Type w}

/-- Change the vertex names, retaining their edge colors. -/
def Graph.comap {Vertex' : Type*} (G : Graph Role Vertex) (f : Vertex' → Vertex) :
    Graph Role Vertex' where
  color x y := G.color (f x) (f y)
  symm x y := G.symm (f x) (f y)

/-- Join two disjoint colored graphs with crossing edges of one owner. -/
def Graph.sum {Vertex' : Type*} (G : Graph Role Vertex) (H : Graph Role Vertex')
    (r : Role) : Graph Role (Vertex ⊕ Vertex') where
  color
    | .inl x, .inl y => G.color x y
    | .inr x, .inr y => H.color x y
    | .inl _, .inr _ => r
    | .inr _, .inl _ => r
  symm x y := by cases x <;> cases y <;> simp [G.symm, H.symm]

/-- The simple graph consisting of the edges of one owner. -/
def Graph.component (G : Graph Role Vertex) (r : Role) : SimpleGraph Vertex where
  Adj x y := x ≠ y ∧ G.color x y = r
  symm := ⟨fun x y h => ⟨h.1.symm, (G.symm y x).trans h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- No triangle has three different edge colors. -/
def Graph.NoRainbow (G : Graph Role Vertex) : Prop :=
  ∀ x y z, x ≠ y → x ≠ z → y ≠ z →
    G.color x y = G.color y z ∨ G.color x y = G.color x z ∨
      G.color y z = G.color x z

/-- No four vertices induce the two-colored path and its complementary path. -/
def Graph.NoAlternatingPath (G : Graph Role Vertex) : Prop :=
  ∀ x : Fin 4 ↪ Vertex, ∀ a b : Role, a ≠ b →
    ¬(G.color (x 0) (x 1) = a ∧ G.color (x 1) (x 2) = a ∧
      G.color (x 2) (x 3) = a ∧ G.color (x 0) (x 2) = b ∧
      G.color (x 0) (x 3) = b ∧ G.color (x 1) (x 3) = b)

/-- A nontrivial partition whose crossing edges all have the same owner. -/
def Graph.Cut (G : Graph Role Vertex) (A : Set Vertex) (r : Role)
    (L R : Set Vertex) : Prop :=
  L.Nonempty ∧ R.Nonempty ∧ Disjoint L R ∧ L ∪ R = A ∧
    ∀ x ∈ L, ∀ y ∈ R, G.color x y = r

/-- A maximal monochromatic clique inside the indicated set of vertices. -/
def Graph.MaxClique (G : Graph Role Vertex) (A : Set Vertex) (r : Role)
    (D : Set Vertex) : Prop :=
  Maximal (fun C : Set Vertex => C ⊆ A ∧ (G.component r).IsClique C) D

/-- A singleton owner blocks every monochromatic clique in the indicated region. -/
def Graph.Blocks (G : Graph Role Vertex) (A : Set Vertex) (label : Vertex → Var)
    (v : Var → WinnerSet Role) (r : Role) : Prop :=
  ∀ D, G.MaxClique A r D → ∃ x ∈ D, v (label x) = WinnerSet.singleton r

/-- A source survives when every other owner has a monochromatic clique through
it whose other occurrences can avoid that owner's singleton. -/
def Graph.Wins (G : Graph Role Vertex) (A : Set Vertex) (label : Vertex → Var)
    (v : Var → WinnerSet Role) (k : Role) : Prop :=
  ∃ x ∈ A, k ∈ (v (label x)).val ∧ ∀ r, r ≠ k →
    ∃ D, G.MaxClique A r D ∧ x ∈ D ∧
      ∀ y ∈ D, y ≠ x → v (label y) ≠ WinnerSet.singleton r

/-- A finite graph representation of an operation, with independent input
occurrences and the two forbidden colored subgraphs. The representing graph
need not be unique. -/
def Represents (f : (Var → WinnerSet Role) → WinnerSet Role) : Prop :=
  ∃ (n : ℕ) (G : Graph Role (Fin n)) (label : Fin n → Var),
    0 < n ∧ G.NoRainbow ∧ G.NoAlternatingPath ∧
      ∀ v k, k ∈ (f v).val ↔ G.Wins Set.univ label v k

end KFOL.Core.ColoredGraph
