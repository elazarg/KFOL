module

public import KFOL.Core.CrownObstruction
public import Mathlib.Data.Finset.Lattice.Fold

/-! # No finite family of relations characterizes the core clone

A finite family has a greatest arity. A cyclic obstruction interpolable on
that many valuations preserves each supplied invariant relation, while no
core term realizes it. Empty families and nullary relations are included.
-/

@[expose] public section
namespace KFOL.Core.Crown

/-- Every finite family of core-invariant relations admits an operation
preserving all its members that is not a core term operation. -/
theorem exists_finite_family_obstruction {Role I : Type*} [Fintype Role] [Finite I]
    (three : Fin 3 ↪ Role) (arity : I → ℕ)
    (relations : ∀ i, Set (Fin (arity i) → WinnerSet Role))
    (hrelations : ∀ i, InvariantRelation (arity i) (relations i)) :
    ∃ n : ℕ, ∃ f : (Fin n → WinnerSet Role) → WinnerSet Role,
      (∀ i, PreservesRelation (relations i) f) ∧
      ¬∃ t : Term Role (Fin n), t.IsCore ∧ ∀ v, t.eval v = f v := by
  classical
  let _ := Fintype.ofFinite I
  let m := Finset.univ.sup arity
  obtain ⟨f, hf, hn⟩ := exists_local_obstruction three m
  refine ⟨m + 3, f, ?_, hn⟩
  intro i
  have hle : arity i ≤ m := Finset.le_sup (Finset.mem_univ i)
  exact (locallyInterpolable_iff_preservesInvariants (arity i) f).mp
    (hf.of_le hle) (relations i) (hrelations i)

end KFOL.Core.Crown
