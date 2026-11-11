module

public import KFOL.Core.CrownObstruction
public import KFOL.Algebra.Idempotent
public import Mathlib.Data.Finset.Lattice.Fold

/-! # Cyclic obstructions for the full winner-set signature

The cyclic operation is idempotent. Any full-language realization would
therefore extract to a core realization, contradicted by cyclic persistence.
-/

@[expose] public section
namespace KFOL.Core.Crown

open WinnerSet

/-- Constant valuations lie in no exceptional cylinder, so every selected
cyclic suppression operation is idempotent. -/
theorem operation_idempotent {Role Var : Type*} [Nonempty Var]
    (b c : Role) (next : Equiv.Perm Var) (selected : Set Var) (A : WinnerSet Role) :
    operation b c next selected (fun _ => A) = A := by
  classical
  have hn : ¬∃ i ∈ selected, Cylinder b c next i (fun _ => A) := by
    rintro ⟨i, _, hi⟩
    exact hi.2.2.1 hi.1
  rw [operation, ite_eq_right hn]
  apply Subtype.ext
  ext r
  simp only [inputUnion, Set.mem_iUnion]
  exact ⟨fun ⟨_, hr⟩ => hr, fun hr => ⟨Classical.arbitrary Var, hr⟩⟩

/-- Winner constants and arbitrary internal role permutations cannot realize
the full cyclic obstruction. No finiteness of the role type is needed. -/
theorem operation_not_full {Role : Type*} (three : Fin 3 ↪ Role) (n : ℕ) :
    ¬∃ t : Term Role (Fin (n+3)), ∀ v,
      t.eval v = operation (three 1) (three 2) (finRotate (n+3)) Set.univ v := by
  rintro ⟨t, he⟩
  have hd (A : WinnerSet Role) : t.eval (fun _ => A) = A := by
    rw [he]
    exact operation_idempotent _ _ _ _ A
  obtain ⟨ht, hte, _⟩ := t.idempotent_extraction three hd
  exact operation_not_core three n ⟨t.pushRenames 1, ht,
    fun v => (hte v).trans (he v)⟩

/-- Arbitrarily many local core interpolants do not guarantee realization
even in the full signature with constants and role permutations. -/
theorem exists_full_syntax_obstruction {Role : Type*} [Fintype Role]
    (three : Fin 3 ↪ Role) (m : ℕ) :
    ∃ f : (Fin (m+3) → WinnerSet Role) → WinnerSet Role,
      LocallyInterpolable m f ∧
      ¬∃ t : Term Role (Fin (m+3)), ∀ v, t.eval v = f v :=
  ⟨_, operation_locallyInterpolable three m, operation_not_full three m⟩

/-- A finite family of core-invariant relations cannot exclude every operation
outside the full signature either. This applies in particular to relations
invariant under either expansion of the owned-choice algebra. -/
theorem exists_full_finite_family_obstruction {Role I : Type*} [Fintype Role] [Finite I]
    (three : Fin 3 ↪ Role) (arity : I → ℕ)
    (relations : ∀ i, Set (Fin (arity i) → WinnerSet Role))
    (hrelations : ∀ i, InvariantRelation (arity i) (relations i)) :
    ∃ n : ℕ, ∃ f : (Fin n → WinnerSet Role) → WinnerSet Role,
      (∀ i, PreservesRelation (relations i) f) ∧
      ¬∃ t : Term Role (Fin n), ∀ v, t.eval v = f v := by
  classical
  let _ := Fintype.ofFinite I
  let m := Finset.univ.sup arity
  obtain ⟨f, hf, hn⟩ := exists_full_syntax_obstruction three m
  refine ⟨m + 3, f, ?_, hn⟩
  intro i
  have hle : arity i ≤ m := Finset.le_sup (Finset.mem_univ i)
  exact (locallyInterpolable_iff_preservesInvariants (arity i) f).mp
    (hf.of_le hle) (relations i) (hrelations i)

end KFOL.Core.Crown
