module

public import KFOL.Core.GridBounded

/-! # No bounded-variable equational basis for any finite core with three roles -/

@[expose] public section

namespace KFOL.Core

universe u

variable {Role : Type u} [DecidableEq Role] [Finite Role]

attribute [local instance] Native.structureOf Equational.coreStructure

/-- The full unbounded result: no infinite or finite basis whose identities
have any fixed bound on their actual variable support can axiomatize the
winner core. This is stronger than the separate K-variable obstruction. -/
theorem no_basis_with_variable_bound (three : Fin 3 ↪ Role) (d : ℕ)
    (T : Equational.Theory (Equational.CoreSymbol Role)) (hT : Equational.HasVariableBound T d) :
    ¬ Equational.IsBasis (WinnerSet Role) T := by
  intro hb
  obtain ⟨B,str,hne,_,_,hnot,hlocal⟩ := Grid.finite_local_countermodel three d
  let _ := str
  let _ := hne
  have hm : Equational.Models T B := by
    intro e he
    exact e.holds_of_local_variety d (hT e he) (hb.models e he) hlocal
  exact hnot (hb.inVariety hm)

/-- In particular no finite equational basis exists. The proof uses the
actual finite countermodels and proved arbitrary-generator local covers. -/
theorem not_hasFiniteBasis (three : Fin 3 ↪ Role) :
    ¬ Equational.HasFiniteBasis (Equational.CoreSymbol Role) (WinnerSet Role) := by
  rintro ⟨T,hfinite,hbasis⟩
  obtain ⟨d,hd⟩ := Equational.finite_hasVariableBound T hfinite
  exact no_basis_with_variable_bound three d T hd hbasis

/-- The same finite countermodels forbid every bounded-variable basis of
the ambient full-native variety. -/
theorem native_no_basis_with_variable_bound (three : Fin 3 ↪ Role) (d : ℕ)
    (T : Equational.Theory (Equational.CoreSymbol Role)) (hT : Equational.HasVariableBound T d) :
    ¬ Equational.IsBasis (Native Role) T := by
  intro hb
  obtain ⟨B,str,hne,_,hnot,_,hlocal⟩ := Grid.finite_local_countermodel three d
  let _ := str
  let _ := hne
  have hm : Equational.Models T B := by
    intro e he
    have hw : e.Holds (WinnerSet Role) :=
      Native.winner_equation_of_native e.lhs e.rhs (hb.models e he)
    exact e.holds_of_local_variety d (hT e he) hw hlocal
  exact hnot (hb.inVariety hm)

theorem native_not_hasFiniteBasis (three : Fin 3 ↪ Role) :
    ¬ Equational.HasFiniteBasis (Equational.CoreSymbol Role) (Native Role) := by
  rintro ⟨T,hfinite,hbasis⟩
  obtain ⟨d,hd⟩ := Equational.finite_hasVariableBound T hfinite
  exact native_no_basis_with_variable_bound three d T hd hbasis

end KFOL.Core
