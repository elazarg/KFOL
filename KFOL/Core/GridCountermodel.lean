module

public import KFOL.Core.GridClone
public import KFOL.Core.NativeTheory

/-! # The full uniform padded-grid countermodel proposition -/

@[expose] public section

namespace KFOL.Core.Grid

universe u

open FirstOrder

variable {Role : Type u} [DecidableEq Role]

attribute [local instance] Native.structureOf Equational.coreStructure structureOf

/-- The padded crossing identity in the independently defined finite-arity
equational logic. Every occurrence of neutral join is expanded in its syntax. -/
noncomputable def crossingEquation {r s : ℕ} (three : Fin 3 ↪ Role) (i : Fin r) (j : Fin s) :
    Equational.Identity (Equational.CoreSymbol Role) where
  arity := Fintype.card (Option (Variable r s))
  lhs := (crossingIdentity three i j).1.relabel (Fintype.equivFin (Option (Variable r s)))
  rhs := (crossingIdentity three i j).2.relabel (Fintype.equivFin (Option (Variable r s)))

omit [DecidableEq Role] in
theorem crossingEquation_arity {r s : ℕ} (three : Fin 3 ↪ Role) (i : Fin r) (j : Fin s) :
    (crossingEquation three i j).arity = (r+1)*(s+1) := crossing_variable_card r s

theorem crossingEquation_native {r s : ℕ} (three : Fin 3 ↪ Role) (i : Fin r) (j : Fin s) :
    (crossingEquation three i j).Holds (Native Role) := by
  unfold Equational.Identity.Holds crossingEquation
  intro v
  simp only [Language.Term.realize_relabel]
  exact crossing_valid three i j _

theorem crossingEquation_winner {r s : ℕ} (three : Fin 3 ↪ Role) (i : Fin r) (j : Fin s) :
    (crossingEquation three i j).Holds (WinnerSet Role) :=
  Native.winner_equation_of_native _ _ (crossingEquation_native three i j)

theorem crossingEquation_fails {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role)
    (i : Fin r) (j : Fin s) :
    letI := upperStructure (Role := Role) (lower (r := r) (s := s) three)
    ¬ (crossingEquation three i j).Holds (Option (span (r := r) (s := s) three)) := by
  let _ := upperStructure (Role := Role) (lower (r := r) (s := s) three)
  intro h
  let v := cloneValuation (r := r) (s := s) three ∘ (Fintype.equivFin (Option (Variable r s))).symm
  have he := h v
  simp only [crossingEquation, Language.Term.realize_relabel] at he
  have hv : v ∘ Fintype.equivFin (Option (Variable r s)) = cloneValuation three := by
    funext x
    simp only [v, Function.comp_apply, Equiv.symm_apply_apply]
  rw [hv] at he
  exact crossing_fails hr hs three i j he

theorem clone_not_in_native_variety {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role) :
    letI := upperStructure (Role := Role) (lower (r := r) (s := s) three)
    ¬ Equational.InVariety (Equational.CoreSymbol Role) (Native Role)
      (Option (span (r := r) (s := s) three)) := by
  let _ := upperStructure (Role := Role) (lower (r := r) (s := s) three)
  let i : Fin r := ⟨0,by omega⟩
  let j : Fin s := ⟨0,by omega⟩
  intro h
  exact crossingEquation_fails hr hs three i j (h.2 _ (crossingEquation_native three i j))

theorem clone_not_in_core_variety {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role) :
    letI := upperStructure (Role := Role) (lower (r := r) (s := s) three)
    ¬ Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role)
      (Option (span (r := r) (s := s) three)) := by
  let _ := upperStructure (Role := Role) (lower (r := r) (s := s) three)
  let i : Fin r := ⟨0,by omega⟩
  let j : Fin s := ⟨0,by omega⟩
  intro h
  exact crossingEquation_fails hr hs three i j (h.2 _ (crossingEquation_winner three i j))

/-- The complete grid-countermodel proposition, uniformly in the role
set and both side lengths. This proves the grid construction; the further
arbitrary-generator local-cover theorem is a separate obligation. -/
theorem grid_countermodel [Finite Role] {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s)
    (three : Fin 3 ↪ Role) :
    ∃ (C : Type u) (_str : (Equational.language (Equational.CoreSymbol Role)).Structure C),
      Nonempty C ∧ Finite C ∧
      ∃ e T S : C,
        Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) C ∧
        (∀ (owner : Role) (c : C), Core.join three (Core.operation owner e c) e = e → Core.join three c e = e) ∧
        (∀ c, Core.join three c e = e ↔ c = T ∨ c = S ∨ c = e) ∧
        T ≠ e ∧ S ≠ e ∧ T ≠ S ∧
        (∀ (owner : Role), Core.operation owner e T = if owner = three 0 then T else e) ∧
        (∀ (owner : Role), Core.operation owner e S = if owner = three 1 then S else e) ∧
        Core.join three T S = e ∧
        (letI := upperStructure (Role := Role) e
         ∃ equation : Equational.Identity (Equational.CoreSymbol Role),
           equation.arity = (r+1)*(s+1) ∧ equation.Holds (Native Role) ∧
             equation.Holds (WinnerSet Role) ∧ ¬ equation.Holds (Option C)) := by
  refine ⟨span (r := r) (s := s) three, inferInstance, inferInstance, inferInstance,
    lower three, T hr three, S hs three, span_inVariety three,
    lower_reflecting three, lower_ideal_exact hr hs three,
    T_ne_lower hr hs three, S_ne_lower hr hs three, T_ne_S hr hs three,
    lower_operation_T hr hs three, lower_operation_S hr hs three, T_join_S hr hs three, ?_⟩
  let _ := upperStructure (Role := Role) (lower (r := r) (s := s) three)
  let i : Fin r := ⟨0,by omega⟩
  let j : Fin s := ⟨0,by omega⟩
  exact ⟨crossingEquation three i j, crossingEquation_arity three i j,
    crossingEquation_native three i j, crossingEquation_winner three i j,
    crossingEquation_fails hr hs three i j⟩

end KFOL.Core.Grid
