module

public import KFOL.Congruences.Closure

/-! # Congruences are exactly the kernels of owner-admissible closures -/

@[expose] public section

namespace KFOL.WinnerSet

universe u

variable {Role : Type u}

/-- A closure is determined by its kernel: the closure of an element is the
greatest member of its class. No finiteness assumption is needed here. -/
theorem closure_eq_of_kernel_eq (c d : ClosureOperator (WinnerSet Role))
    (h : ∀ A B, c A = c B ↔ d A = d B) : c = d := by
  apply _root_.ClosureOperator.ext
  intro A
  apply le_antisymm
  · have he := (h A (c A)).mp (c.idempotent A).symm
    exact (d.le_closure (c A)).trans_eq he.symm
  · have he := (h A (d A)).mpr (d.idempotent A).symm
    exact (c.le_closure (d A)).trans_eq he.symm

namespace Congruence

/-- Complete bijective closure classification of every congruence, using
mathlib's independent Setoid and ClosureOperator semantics. -/
noncomputable def equivAtomClosures [Finite Role] [Nonempty Role] (three : Fin 3 ↪ Role) :
    Congruence Role ≃ {c : ClosureOperator (WinnerSet Role) // AtomClosure c} where
  toFun θ := ⟨θ.closureOperator three,θ.closureOperator_atom three⟩
  invFun c := ClosureOperator.kernel c.val c.property
  left_inv θ := by
    apply Congruence.ext
    intro A B
    exact θ.closureOperator_rel_iff three A B
  right_inv c := by
    apply Subtype.ext
    apply closure_eq_of_kernel_eq
    intro A B
    exact (ClosureOperator.kernel c.val c.property).closureOperator_rel_iff three A B

/-- Full paper-facing kernel statement, with unique closure and both
directions of the relation. -/
theorem exists_unique_closure [Finite Role] [Nonempty Role] (three : Fin 3 ↪ Role)
    (θ : Congruence Role) :
    ∃! c : ClosureOperator (WinnerSet Role),
      AtomClosure c ∧ ∀ A B, θ.r A B ↔ c A = c B := by
  refine ⟨θ.closureOperator three,⟨θ.closureOperator_atom three,
    fun A B => (θ.closureOperator_rel_iff three A B).symm⟩,?_⟩
  intro d hd
  apply closure_eq_of_kernel_eq
  intro A B
  exact (hd.2 A B).symm.trans (θ.closureOperator_rel_iff three A B).symm

end Congruence

end KFOL.WinnerSet
