module

public import KFOL.Core.CrownPatches
public import KFOL.Core.CyclicPersistence
public import KFOL.Core.PatchInterpolation

/-! # The core clone is not finitely related

For every locality bound m, a cycle on m+3 inputs supplies a noncore
operation. Deleting any matching edge gives a core operation, and each
valuation disagrees with at most one of these deletion patches.
-/

@[expose] public section
namespace KFOL.Core.Crown
open WinnerSet

theorem positive_mem {Role : Type*} (three : Fin 3 ↪ Role) (n : ℕ) (i : Fin (n+3)) :
    three 0 ∈ (operation (three 1) (three 2) (finRotate (n+3)) Set.univ
      (positive three (finRotate (n+3)) i)).val := by
  classical
  have hnone := positive_no_cylinder three (finRotate (n+3)) i
    (rotate_ne_self n i) (rotate_twice_ne_self n i)
  have hcond : ¬∃ j ∈ (Set.univ : Set (Fin (n+3))),
      Cylinder (three 1) (three 2) (finRotate (n+3)) j
        (positive three (finRotate (n+3)) i) := fun ⟨j, _, hj⟩ => hnone ⟨j, hj⟩
  rw [operation, ite_eq_right hcond]
  exact Set.mem_iUnion.mpr ⟨i, by simp [positive]⟩

/-- The full cycle violates a winner-persistence law satisfied by every core term. -/
theorem operation_not_core {Role : Type*} (three : Fin 3 ↪ Role) (n : ℕ) :
    ¬∃ t : Term Role (Fin (n+3)), t.IsCore ∧ ∀ v,
      t.eval v = operation (three 1) (three 2) (finRotate (n+3)) Set.univ v := by
  classical
  rintro ⟨t, ht, he⟩
  have hp : three 0 ∈ (t.eval (positive three (finRotate (n+3)) 0)).val := by
    rw [he]
    exact positive_mem three n 0
  obtain ⟨j, hj⟩ := persistence three (finRotate (n+3)) 0 (rotate_ne_self n 0) t ht hp
  rw [he, operation_negative three _ j (rotate_ne_self n j)] at hj
  simp [WinnerSet.val_union] at hj

/-- Every m evaluations of the full cyclic operation share a deletion patch. -/
theorem operation_locallyInterpolable {Role : Type*} [Fintype Role]
    (three : Fin 3 ↪ Role) (m : ℕ) :
    LocallyInterpolable m
      (operation (three 1) (three 2) (finRotate (m+3)) Set.univ) := by
  classical
  choose patches hc hp using exists_patch three m
  apply locallyInterpolable_of_finite_patches m (by simp) patches hc
    (operation (three 1) (three 2) (finRotate (m+3)) Set.univ)
  intro v
  obtain ⟨bad, hb⟩ := operation_agreement (three 1) (three 2) (finRotate (m+3)) v
  exact ⟨bad, fun i hi => (hp i v).trans (hb i hi)⟩

/-- At every fixed finite role set of size at least three, no finite number of
sample valuations suffices to recognize term operations, uniformly in arity. -/
theorem exists_local_obstruction {Role : Type*} [Fintype Role]
    (three : Fin 3 ↪ Role) (m : ℕ) :
    ∃ f : (Fin (m+3) → WinnerSet Role) → WinnerSet Role,
      LocallyInterpolable m f ∧
      ¬∃ t : Term Role (Fin (m+3)), t.IsCore ∧ ∀ v, t.eval v = f v :=
  ⟨_, operation_locallyInterpolable three m, operation_not_core three m⟩

/-- Equivalent relational form: every arity bound admits a nonterm operation
preserving all core-invariant relations of that arity. -/
theorem exists_invariant_obstruction {Role : Type*} [Fintype Role]
    (three : Fin 3 ↪ Role) (m : ℕ) :
    ∃ f : (Fin (m+3) → WinnerSet Role) → WinnerSet Role,
      PreservesInvariants m f ∧
      ¬∃ t : Term Role (Fin (m+3)), t.IsCore ∧ ∀ v, t.eval v = f v := by
  obtain ⟨f, hf, hn⟩ := exists_local_obstruction three m
  exact ⟨f, (locallyInterpolable_iff_preservesInvariants m f).mp hf, hn⟩

end KFOL.Core.Crown
