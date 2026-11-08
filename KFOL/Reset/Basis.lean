module

public import KFOL.Reset.Basis.Presentation

/-! # Soundness and completeness of the six-equation reset basis

The proof uses common-root path normalization and suffix absorption in arbitrary
six-law algebras, then the independently proved completeness of equational logic.
Freese et al.'s Theorem 3.7 is a proof reference, not a theorem hypothesis.
-/

@[expose] public section

namespace KFOL.Reset

universe u v

/-- The concrete reset algebra satisfies the six explicit identities for every
role type, including the two-role case. -/
theorem models_winnerSet_basis (Role : Type u) :
    letI := structureOf (WinnerSet.reset (Role := Role))
    Equational.Models basis (WinnerSet Role) := by
  let _ := structureOf (WinnerSet.reset (Role := Role))
  exact models_basis_iff.mpr (winnerSet_laws Role)

/-- Completeness for all terms, over arbitrary variable types and every role
set containing three distinct roles. -/
theorem derives_iff_eval_eq {Role : Type u} {Var : Type v} (three : Fin 3 ↪ Role)
    (s t : Term Var) :
    Equational.Derives basis s t ↔ ∀ v : Var → WinnerSet Role, s.eval v = t.eval v := by
  constructor
  · intro hd
    let _ := structureOf (WinnerSet.reset (Role := Role))
    exact hd.sound (WinnerSet Role) (models_winnerSet_basis Role)
  · intro he
    have hselected := s.selected_iff_of_chain_eq t three (fun v _ => he v)
    apply Equational.derives_of_valid_in_models basis s t
    intro M str _ hM v
    have hlaws := models_basis_iff.mp hM
    have hh := hlaws.interpret_eq_of_selected s t v hselected
    simpa only [interpret_operation] using hh

/-- A basis in the shared independent semantic/derivational API. -/
theorem isBasis {Role : Type u} (three : Fin 3 ↪ Role) :
    letI := structureOf (WinnerSet.reset (Role := Role))
    Equational.IsBasis (WinnerSet Role) basis := by
  let _ := structureOf (WinnerSet.reset (Role := Role))
  intro e
  exact (derives_iff_eval_eq three e.lhs e.rhs).symm

/-- Finite basability follows with the actual family, not an external theorem
or a model supplied as an additional hypothesis. -/
theorem hasFiniteBasis {Role : Type u} (three : Fin 3 ↪ Role) :
    letI := structureOf (WinnerSet.reset (Role := Role))
    Equational.HasFiniteBasis Symbol (WinnerSet Role) :=
  ⟨basis, basis_finite, isBasis three⟩

end KFOL.Reset
