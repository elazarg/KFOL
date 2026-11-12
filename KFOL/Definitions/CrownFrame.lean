module

public import Mathlib.Data.Finset.Grade
public import Mathlib.GroupTheory.Perm.Fin

/-! # Crown intervals in a finite Boolean lattice

The lower and upper vertices are specified by sets. Incidence is the cyclic
crown relation; its edges are covers in the Boolean lattice. -/

@[expose] public section
namespace KFOL.Core.IntervalCrown

universe u

/-- A cyclic family of cover intervals, with no additional lower/upper incidences. -/
structure Frame (Var : Type u) [Fintype Var] [DecidableEq Var] (m : ℕ) where
  lower : Fin m → Finset Var
  upper : Fin m → Finset Var
  lower_nonempty : ∀ i, (lower i).Nonempty
  upper_ne_univ : ∀ i, upper i ≠ Finset.univ
  cover : ∀ i, lower i ⋖ upper i
  incidence : ∀ i j, lower j ⊆ upper i ↔ j = i ∨ j = finRotate m i

namespace Frame
variable {Var : Type u} [Fintype Var] [DecidableEq Var] {m : ℕ}

/-- Matching intervals selected by their cycle indices. -/
def edges (G : Frame Var m) (selected : Set (Fin m)) : Set (Finset Var × Finset Var) :=
  {p | ∃ i ∈ selected, p = (G.lower i, G.upper i)}

/-- Omit precisely one matching interval. -/
def deleteEdges (G : Frame Var m) (h : Fin m) : Set (Finset Var × Finset Var) :=
  G.edges {i | i ≠ h}

/-- Change the starting point of the same cyclic frame. -/
def reindex (G : Frame Var m) (e : Equiv.Perm (Fin m))
    (he : ∀ i, e (finRotate m i) = finRotate m (e i)) : Frame Var m where
  lower i := G.lower (e i)
  upper i := G.upper (e i)
  lower_nonempty i := G.lower_nonempty (e i)
  upper_ne_univ i := G.upper_ne_univ (e i)
  cover i := G.cover (e i)
  incidence i j := by
    rw [G.incidence]
    constructor
    · rintro (h | h)
      · exact Or.inl (e.injective h)
      · exact Or.inr (e.injective (h.trans (he i).symm))
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr (he i)

/-- Retain all matching intervals except the wrapping edge. -/
def cutEdges (G : Frame Var m) : Set (Finset Var × Finset Var) :=
  {p | ∃ i, i.val + 1 < m ∧ p = (G.lower i, G.upper i)}

/-- The principal upset after reversing the nonwrapping matching intervals. -/
noncomputable def cut (G : Frame Var m) (A S : Finset Var) : Bool :=
  decide (A ⊆ S ∨ ∃ i : Fin m, i.val + 1 < m ∧ A ⊆ G.upper i ∧
    ∃ j : Fin m, j.val ≤ i.val ∧ G.lower j ⊆ S)

end Frame
end KFOL.Core.IntervalCrown
