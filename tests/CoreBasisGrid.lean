module

public import KFOL.Core

/-! Complete proposed paper statements and concrete padded-grid regressions. -/

@[expose] public section

namespace KFOLTest.CoreGrid

open KFOL

universe u

/-- Complete main nonfinite-basis statement, including the stronger finite
local countermodel assertion. In particular the bound also permits d=0. -/
theorem core_nonfinite_basis {Role : Type u} [DecidableEq Role] [Finite Role]
    (three : Fin 3 ↪ Role) :
    letI := Equational.coreStructure Role
    letI := Core.Native.structureOf (Role := Role)
    (∀ d : ℕ,
      ∃ (B : Type u) (_str : (Equational.language (Equational.CoreSymbol Role)).Structure B),
        Nonempty B ∧ Finite B ∧
        ¬ Equational.InVariety (Equational.CoreSymbol Role) (Core.Native Role) B ∧
        ¬ Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) B ∧
        (∀ X : Finset B, X.card ≤ d →
          Nonempty (FirstOrder.Language.Substructure.closure
            (Equational.language (Equational.CoreSymbol Role)) (X : Set B)) →
          Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role)
            (FirstOrder.Language.Substructure.closure
              (Equational.language (Equational.CoreSymbol Role)) (X : Set B)))) ∧
    (∀ (d : ℕ) (T : Equational.Theory (Equational.CoreSymbol Role)),
      Equational.HasVariableBound T d → ¬ Equational.IsBasis (WinnerSet Role) T) ∧
    ¬ Equational.HasFiniteBasis (Equational.CoreSymbol Role) (WinnerSet Role) := by
  let _ := Equational.coreStructure Role
  let _ := Core.Native.structureOf (Role := Role)
  exact ⟨Core.Grid.finite_local_countermodel three,
    Core.no_basis_with_variable_bound three, Core.not_hasFiniteBasis three⟩

/-- Complete ambient native-variety conclusion. -/
theorem ambient_nonfinite_basis {Role : Type u} [DecidableEq Role] [Finite Role]
    (three : Fin 3 ↪ Role) :
    letI := Core.Native.structureOf (Role := Role)
    (∀ (d : ℕ) (T : Equational.Theory (Equational.CoreSymbol Role)),
      Equational.HasVariableBound T d → ¬ Equational.IsBasis (Core.Native Role) T) ∧
    ¬ Equational.HasFiniteBasis (Equational.CoreSymbol Role) (Core.Native Role) := by
  let _ := Core.Native.structureOf (Role := Role)
  exact ⟨Core.native_no_basis_with_variable_bound three, Core.native_not_hasFiniteBasis three⟩

private def three3 : Fin 3 ↪ Fin 3 := Function.Embedding.refl _
private def three4 : Fin 3 ↪ Fin 4 := {
  toFun := fun i => ⟨i.val,by omega⟩
  inj' := fun _ _ h => Fin.ext (congrArg (fun x : Fin 4 => x.val) h) }

attribute [local instance] Core.Native.structureOf Equational.coreStructure Core.Grid.structureOf

example : ¬ Equational.HasFiniteBasis (Equational.CoreSymbol (Fin 3)) (WinnerSet (Fin 3)) :=
  Core.not_hasFiniteBasis three3

example : ¬ Equational.HasFiniteBasis (Equational.CoreSymbol (Fin 4)) (WinnerSet (Fin 4)) :=
  Core.not_hasFiniteBasis three4

example : ¬ Equational.HasFiniteBasis (Equational.CoreSymbol (Fin 4)) (Core.Native (Fin 4)) :=
  Core.native_not_hasFiniteBasis three4

example : (Core.Grid.crossingEquation (r := 2) (s := 3) three3 0 0).arity = 12 := by
  exact Core.Grid.crossingEquation_arity three3 0 0

example : (Core.Grid.crossingEquation (r := 2) (s := 3) three3 0 0).Holds (WinnerSet (Fin 3)) :=
  Core.Grid.crossingEquation_winner three3 0 0

example :
    letI := Core.upperStructure (Role := Fin 3) (Core.Grid.lower (r := 2) (s := 3) three3)
    ¬ (Core.Grid.crossingEquation (r := 2) (s := 3) three3 0 0).Holds
      (Option (Core.Grid.span (r := 2) (s := 3) three3)) :=
  Core.Grid.crossingEquation_fails (by decide) (by decide) three3 0 0

/-- info: 'KFOLTest.CoreGrid.core_nonfinite_basis' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOLTest.CoreGrid.core_nonfinite_basis

/-- info: 'KFOLTest.CoreGrid.ambient_nonfinite_basis' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOLTest.CoreGrid.ambient_nonfinite_basis

end KFOLTest.CoreGrid
