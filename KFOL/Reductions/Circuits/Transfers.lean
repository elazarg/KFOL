module

public import KFOL.Reductions.Circuits.Satisfying
public import KFOL.Owner.Public
public import KFOL.Policies.Basic

/-! Reset as a repeated-edge minor in a single ternary-operation DAG. -/

@[expose] public section

namespace KFOL.Circuit

universe u v w

/- H(root,left,left) uses the SAME left ref twice. It does not copy a
previously constructed subgraph or expand its shared continuation. -/
theorem Gate.validAt_liftReset {σ : ℕ → Type u} {Var : Type v} (operation : σ 3)
    (gate : Gate Reset.Symbol Var) (position : ℕ) :
    (gate.liftReset operation).ValidAt position ↔ gate.ValidAt position := by
  cases gate with
  | input j => rfl
  | @func n symbol refs =>
    cases symbol
    constructor
    · intro h i
      have hi : i = 0 ∨ i = 1 := by omega
      rcases hi with rfl | rfl
      · exact h 1
      · exact h 0
    · intro h i
      change (if i = 0 then refs 1 else refs 0) < position
      split_ifs <;> exact h _

theorem validFrom_liftReset {σ : ℕ → Type u} {Var : Type v} (operation : σ 3)
    (gates : List (Gate Reset.Symbol Var)) (position : ℕ) :
    ValidFrom position (gates.map (Gate.liftReset operation)) ↔ ValidFrom position gates := by
  induction gates generalizing position with
  | nil => rfl
  | cons gate gates ih => simp only [List.map_cons, ValidFrom, Gate.validAt_liftReset, ih]

@[simp] theorem Equation.wellFormed_liftReset {σ : ℕ → Type u} {Var : Type v} (operation : σ 3)
    (equation : Equation Reset.Symbol Var) :
    (equation.liftReset operation).WellFormed ↔ equation.WellFormed := by
  simp only [WellFormed, liftReset, List.length_map, validFrom_liftReset]

@[simp] theorem Equation.length_liftReset {σ : ℕ → Type u} {Var : Type v} (operation : σ 3)
    (equation : Equation Reset.Symbol Var) : (equation.liftReset operation).gates.length = equation.gates.length := by
  simp [liftReset]

/- Every resulting operation node is the single displayed ternary symbol;
there is no retained primitive reset node. -/
theorem Equation.gates_liftReset {σ : ℕ → Type u} {Var : Type v} (operation : σ 3)
    (equation : Equation Reset.Symbol Var) (gate : Gate σ Var) (hgate : gate ∈ (equation.liftReset operation).gates) :
    (∃ j, gate = .input j) ∨ ∃ refs : Fin 3 → ℕ, gate = .func operation refs := by
  obtain ⟨source, _, rfl⟩ := List.mem_map.mp hgate
  cases source with
  | input j => exact Or.inl ⟨j, rfl⟩
  | @func n symbol refs => cases symbol; exact Or.inr ⟨_, rfl⟩

theorem Gate.eval_liftReset {σ : ℕ → Type u} {Var : Type v} {M : Type w}
    [(Equational.language Reset.Symbol).Structure M] [(Equational.language σ).Structure M]
    (operation : σ 3)
    (hminor : ∀ x y : M,
      FirstOrder.Language.Structure.funMap (L := Equational.language σ) operation (fun i => if i = 0 then y else x) =
        Reset.operation M x y)
    (valuation : Var → M) (cache : List M) (gate : Gate Reset.Symbol Var) :
    (gate.liftReset operation).eval valuation cache = gate.eval valuation cache := by
  cases gate with
  | input j => rfl
  | @func n symbol refs =>
    cases symbol
    have hb : (∀ i : Fin 3, (if i = 0 then refs 1 else refs 0) < cache.length) ↔
        ∀ i : Fin 2, refs i < cache.length := by
      exact Gate.validAt_liftReset (Var := Var) operation (.func .reset refs) cache.length
    by_cases h : ∀ i : Fin 2, refs i < cache.length
    · have ht := hb.mpr h
      simp only [liftReset, eval, dite_eq_left h, dite_eq_left ht]
      apply congrArg some
      have hargs : (fun i : Fin 3 => cache[if i = 0 then refs 1 else refs 0]'(ht i)) =
          (fun i : Fin 3 => if i = 0 then cache[refs 1]'(h 1) else cache[refs 0]'(h 0)) := by
        funext i
        split_ifs <;> rfl
      rw [hargs, hminor]
      unfold Reset.operation
      apply congrArg (FirstOrder.Language.Structure.funMap (L := Equational.language Reset.Symbol) Reset.Symbol.reset)
      funext i
      have hi : i = 0 ∨ i = 1 := by omega
      rcases hi with rfl | rfl <;> rfl
    · have ht : ¬∀ i : Fin 3, (if i = 0 then refs 1 else refs 0) < cache.length := mt hb.mp h
      simp only [liftReset, eval, dite_eq_right h, dite_eq_right ht]

theorem runFrom_liftReset {σ : ℕ → Type u} {Var : Type v} {M : Type w}
    [(Equational.language Reset.Symbol).Structure M] [(Equational.language σ).Structure M]
    (operation : σ 3)
    (hminor : ∀ x y : M,
      FirstOrder.Language.Structure.funMap (L := Equational.language σ) operation (fun i => if i = 0 then y else x) =
        Reset.operation M x y)
    (valuation : Var → M) (gates : List (Gate Reset.Symbol Var)) (cache : List M) :
    runFrom valuation (gates.map (Gate.liftReset operation)) cache = runFrom valuation gates cache := by
  induction gates generalizing cache with
  | nil => rfl
  | cons gate gates ih =>
    simp only [List.map_cons, runFrom, Gate.eval_liftReset operation hminor]
    cases he : gate.eval valuation cache with
    | none => rfl
    | some value => exact ih (cache ++ [value])

theorem Equation.eval_liftReset {σ : ℕ → Type u} {Var : Type v} {M : Type w}
    [(Equational.language Reset.Symbol).Structure M] [(Equational.language σ).Structure M]
    (operation : σ 3)
    (hminor : ∀ x y : M,
      FirstOrder.Language.Structure.funMap (L := Equational.language σ) operation (fun i => if i = 0 then y else x) =
        Reset.operation M x y)
    (valuation : Var → M) (equation : Equation Reset.Symbol Var) :
    (equation.liftReset operation).eval valuation = equation.eval valuation := by
  unfold eval liftReset
  rw [runFrom_liftReset operation hminor]

theorem Equation.holds_liftReset_iff {σ : ℕ → Type u} {Var : Type v} {M : Type w}
    [(Equational.language Reset.Symbol).Structure M] [(Equational.language σ).Structure M]
    (operation : σ 3)
    (hminor : ∀ x y : M,
      FirstOrder.Language.Structure.funMap (L := Equational.language σ) operation (fun i => if i = 0 then y else x) =
        Reset.operation M x y)
    (equation : Equation Reset.Symbol Var) :
    (equation.liftReset operation).Holds M ↔ equation.Holds M := by
  simp only [Holds, wellFormed_liftReset, eval_liftReset operation hminor]

end KFOL.Circuit

namespace KFOL.Circuit

universe u v w

theorem Equation.eval_toGuarded {Role : Type u} {Var : Type v} (owner : Role)
    (equation : Equation Reset.Symbol Var) (valuation : Var → WinnerSet Role) :
    let _ := Reset.structureOf (WinnerSet.reset (Role := Role))
    let _ := Owner.oneOwnerStructure owner
    (equation.liftReset (Owner.Symbol.guarded ())).eval valuation = equation.eval valuation := by
  let _ := Reset.structureOf (WinnerSet.reset (Role := Role))
  let _ := Owner.oneOwnerStructure owner
  change (equation.liftReset (Owner.Symbol.guarded ())).eval valuation = equation.eval valuation
  apply Equation.eval_liftReset (σ := Owner.Symbol Unit) (Owner.Symbol.guarded ()) (valuation := valuation) (equation := equation)
  intro x y
  change WinnerSet.guardedChoice owner y x x = x.reset y
  simp only [WinnerSet.guardedChoice, WinnerSet.choice_self]

theorem Equation.holds_toGuarded_iff {Role : Type u} {Var : Type v} (owner : Role)
    (equation : Equation Reset.Symbol Var) :
    let _ := Reset.structureOf (WinnerSet.reset (Role := Role))
    let _ := Owner.oneOwnerStructure owner
    (equation.liftReset (Owner.Symbol.guarded ())).Holds (WinnerSet Role) ↔ equation.Holds (WinnerSet Role) := by
  let _ := Reset.structureOf (WinnerSet.reset (Role := Role))
  let _ := Owner.oneOwnerStructure owner
  change (equation.liftReset (Owner.Symbol.guarded ())).Holds (WinnerSet Role) ↔ equation.Holds (WinnerSet Role)
  apply Equation.holds_liftReset_iff
  intro x y
  change WinnerSet.guardedChoice owner y x x = x.reset y
  simp only [WinnerSet.guardedChoice, WinnerSet.choice_self]

theorem Equation.eval_toPolicy {Role : Type u} {Label : Type w} {Var : Type v}
    (D : Label → Set Role) (label : Label) (equation : Equation Reset.Symbol Var)
    (valuation : Var → WinnerSet Role) :
    let _ := Reset.structureOf (WinnerSet.reset (Role := Role))
    let _ := Policies.structureOf D
    (equation.liftReset (Policies.Symbol.selective label)).eval valuation = equation.eval valuation := by
  let _ := Reset.structureOf (WinnerSet.reset (Role := Role))
  let _ := Policies.structureOf D
  change (equation.liftReset (Policies.Symbol.selective label)).eval valuation = equation.eval valuation
  apply Equation.eval_liftReset (σ := Policies.Symbol Label) (Policies.Symbol.selective label) (valuation := valuation) (equation := equation)
  intro x y
  change WinnerSet.policyReset (D label) y x x = x.reset y
  exact WinnerSet.policyReset_minor _ _ _

theorem Equation.holds_toPolicy_iff {Role : Type u} {Label : Type w} {Var : Type v}
    (D : Label → Set Role) (label : Label) (equation : Equation Reset.Symbol Var) :
    let _ := Reset.structureOf (WinnerSet.reset (Role := Role))
    let _ := Policies.structureOf D
    (equation.liftReset (Policies.Symbol.selective label)).Holds (WinnerSet Role) ↔ equation.Holds (WinnerSet Role) := by
  let _ := Reset.structureOf (WinnerSet.reset (Role := Role))
  let _ := Policies.structureOf D
  change (equation.liftReset (Policies.Symbol.selective label)).Holds (WinnerSet Role) ↔ equation.Holds (WinnerSet Role)
  apply Equation.holds_liftReset_iff
  intro x y
  change WinnerSet.policyReset (D label) y x x = x.reset y
  exact WinnerSet.policyReset_minor _ _ _

namespace ResetCNF

/- The original linear reset DAG becomes a pure single-H DAG by repeated
EDGES; its actual evaluation is still a complete CNF reduction. -/
theorem guarded_holds_iff_unsatisfiable {Role : Type u} (three : Fin 3 ↪ Role) (owner : Role) (formula : Reductions.CNF) :
    let _ := Owner.oneOwnerStructure owner
    ((equation formula).liftReset (Owner.Symbol.guarded ())).Holds (WinnerSet Role) ↔ ¬Reductions.Satisfiable formula := by
  let _ := Owner.oneOwnerStructure owner
  let _ := Reset.structureOf (WinnerSet.reset (Role := Role))
  have hh := Equation.holds_toGuarded_iff owner (equation formula)
  dsimp only at hh
  exact hh.trans (equation_holds_iff_unsatisfiable three formula)

/- Any one policy, including an endpoint policy, suffices. Its signature
contains no constant, extra variable or primitive reset gate. -/
theorem policy_holds_iff_unsatisfiable {Role : Type u} {Label : Type w} (three : Fin 3 ↪ Role)
    (D : Label → Set Role) (label : Label) (formula : Reductions.CNF) :
    let _ := Policies.structureOf D
    ((equation formula).liftReset (Policies.Symbol.selective label)).Holds (WinnerSet Role) ↔ ¬Reductions.Satisfiable formula := by
  let _ := Policies.structureOf D
  let _ := Reset.structureOf (WinnerSet.reset (Role := Role))
  have hh := Equation.holds_toPolicy_iff D label (equation formula)
  dsimp only at hh
  exact hh.trans (equation_holds_iff_unsatisfiable three formula)

end ResetCNF
end KFOL.Circuit

namespace KFOL.Circuit

universe u v

theorem edgeCount_reset {Var : Type v} (gates : List (Gate Reset.Symbol Var)) :
    edgeCount gates = 2 * operationCount gates := by
  induction gates with
  | nil => rfl
  | cons gate gates ih =>
    cases gate with
    | input j => simpa [edgeCount, operationCount, Gate.references] using ih
    | @func n symbol refs =>
      cases symbol
      simp_all [edgeCount, operationCount, Gate.references]
      omega

theorem operationCount_liftReset {σ : ℕ → Type u} {Var : Type v} (operation : σ 3)
    (gates : List (Gate Reset.Symbol Var)) :
    operationCount (gates.map (Gate.liftReset operation)) = operationCount gates := by
  induction gates with
  | nil => rfl
  | cons gate gates ih =>
    cases gate with
    | input j => simpa [operationCount, Gate.liftReset] using ih
    | @func n symbol refs => cases symbol; simpa [operationCount, Gate.liftReset] using ih

theorem edgeCount_liftReset {σ : ℕ → Type u} {Var : Type v} (operation : σ 3)
    (gates : List (Gate Reset.Symbol Var)) :
    edgeCount (gates.map (Gate.liftReset operation)) = 3 * operationCount gates := by
  induction gates with
  | nil => rfl
  | cons gate gates ih =>
    cases gate with
    | input j => simpa [edgeCount, Gate.liftReset, Gate.references, operationCount] using ih
    | @func n symbol refs =>
      cases symbol
      simp_all [edgeCount, operationCount, Gate.references, Gate.liftReset]
      omega

end KFOL.Circuit
