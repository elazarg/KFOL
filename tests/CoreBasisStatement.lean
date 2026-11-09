module

public import KFOL.Core

/-! Compilable full statement proposed for root Paper.lean. -/

@[expose] public section

namespace KFOLTest.CoreBasisStatement

open KFOL

theorem core_variable_bound_obstruction {Role : Type*} [DecidableEq Role] [Fintype Role]
    (three : Fin 3 ↪ Role) :
    letI := Equational.coreStructure Role
    letI := Core.Native.structureOf (Role := Role)
    Fintype.card (Core.Native Role) = Fintype.card Role + 2 ∧
    (∀ e : Equational.Identity (Equational.CoreSymbol Role),
      e.variableCount ≤ Fintype.card Role → e.Holds (WinnerSet Role) →
        e.Holds (Core.Native Role)) ∧
    (Core.exhaustionIdentity three).Holds (WinnerSet Role) ∧
    ¬(Core.exhaustionIdentity three).Holds (Core.Native Role) ∧
    (Core.exhaustionIdentity three).variableCount = Fintype.card Role + 1 ∧
    ¬Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) (Core.Native Role) ∧
    (∀ T : Equational.Theory (Equational.CoreSymbol Role),
      Equational.HasVariableBound T (Fintype.card Role) →
        ¬Equational.IsBasis (WinnerSet Role) T) ∧
    (∀ T : Equational.Theory (Equational.CoreSymbol Role),
      Equational.IsBasis (WinnerSet Role) T →
        ∃ e ∈ T, Fintype.card Role + 1 ≤ e.variableCount) := by
  let _ := Equational.coreStructure Role
  let _ := Core.Native.structureOf (Role := Role)
  exact ⟨Core.Native.card_native, Core.Native.holds_of_variableCount_le three,
    Core.exhaustion_valid three, Core.exhaustion_not_valid three,
    Core.exhaustion_variableCount three, Core.native_not_inVariety three,
    Core.no_basis_with_role_bound three, Core.exists_large_identity_of_basis three⟩

/-- info: 'KFOLTest.CoreBasisStatement.core_variable_bound_obstruction' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOLTest.CoreBasisStatement.core_variable_bound_obstruction

end KFOLTest.CoreBasisStatement
