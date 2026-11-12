module

public import KFOL.Definitions.Bichain

/-! # The four-state observer quotient and its projection envelope

The two collapse maps are endomorphisms of the union expansion. As a result,
the possible-value trace determines every full term operation. A neutral
median lift encodes such a trace by a pure bichain operation one arity higher.
-/

@[expose] public section
namespace KFOL.Bichain

namespace Value

@[simp] theorem ofView_toView (x : Value) : ofView (toView x) = x := viewEquiv.left_inv x

@[simp] theorem toView_ofView (x : KFOL.PlayerView (0 : Fin 3)) : toView (ofView x) = x :=
  viewEquiv.right_inv x

@[simp] theorem toView_inf (x y : Value) :
    toView (inf x y) = KFOL.PlayerView.choice 1 (toView x) (toView y) := by
  cases x <;> cases y <;> simp [inf, toView, KFOL.PlayerView.choice, KFOL.PlayerView.union]

@[simp] theorem toView_sup (x y : Value) :
    toView (sup x y) = KFOL.PlayerView.choice 2 (toView x) (toView y) := by
  cases x <;> cases y <;> simp [sup, toView, KFOL.PlayerView.choice, KFOL.PlayerView.union]

@[simp] theorem toView_union (x y : Value) :
    toView (union x y) = KFOL.PlayerView.union (toView x) (toView y) := by
  cases x <;> cases y <;> simp [union, toView, KFOL.PlayerView.union]

@[simp] theorem toView_owner_zero (x y : Value) :
    toView (union x y) = KFOL.PlayerView.choice 0 (toView x) (toView y) := by
  simp [KFOL.PlayerView.choice]

/-- Union becomes a two-operation expression when a neutral parameter is supplied. -/
theorem median_neutral : ∀ x y : Value, median x y .neutral = union x y := by
  decide +kernel

/-- The observer quotient is the union expansion of the four-element bichain. -/
theorem observer_model :
    (∀ x y : Value,
      viewEquiv (inf x y) = KFOL.PlayerView.choice 1 (viewEquiv x) (viewEquiv y)) ∧
    (∀ x y : Value,
      viewEquiv (sup x y) = KFOL.PlayerView.choice 2 (viewEquiv x) (viewEquiv y)) ∧
    (∀ x y : Value,
      viewEquiv (union x y) = KFOL.PlayerView.choice 0 (viewEquiv x) (viewEquiv y)) ∧
    ∀ x y : Value, median x y .neutral = union x y :=
  ⟨toView_inf, toView_sup, toView_owner_zero, median_neutral⟩

@[simp] theorem collapseB_inf : ∀ x y : Value,
    collapseB (inf x y) = inf (collapseB x) (collapseB y) := by
  decide +kernel
@[simp] theorem collapseB_sup : ∀ x y : Value,
    collapseB (sup x y) = sup (collapseB x) (collapseB y) := by
  decide +kernel
@[simp] theorem collapseB_union : ∀ x y : Value,
    collapseB (union x y) = union (collapseB x) (collapseB y) := by
  decide +kernel
@[simp] theorem collapseC_inf : ∀ x y : Value,
    collapseC (inf x y) = inf (collapseC x) (collapseC y) := by
  decide +kernel
@[simp] theorem collapseC_sup : ∀ x y : Value,
    collapseC (sup x y) = sup (collapseC x) (collapseC y) := by
  decide +kernel
@[simp] theorem collapseC_union : ∀ x y : Value,
    collapseC (union x y) = union (collapseC x) (collapseC y) := by
  decide +kernel

private theorem eq_of_possible_tests : ∀ x y : Value,
    (x = .possible ↔ y = .possible) →
    (collapseB x = .possible ↔ collapseB y = .possible) →
    (collapseC x = .possible ↔ collapseC y = .possible) → x = y := by
  decide +kernel

theorem envelope_cases : ∀ x z : Value,
    envelope x z = match x with
      | .b => .b
      | .c => .c
      | .possible => .possible
      | .neutral => if z = .possible then .possible else .neutral := by
  decide +kernel

end Value

namespace Term

variable {Var : Type*}

@[simp] theorem eval_collapseB (t : Term Var) (v : Var → Value) :
    t.eval (fun j => Value.collapseB (v j)) = Value.collapseB (t.eval v) := by
  induction t <;> simp_all [eval]

@[simp] theorem eval_collapseC (t : Term Var) (v : Var → Value) :
    t.eval (fun j => Value.collapseC (v j)) = Value.collapseC (t.eval v) := by
  induction t <;> simp_all [eval]

/-- Equality of possible-value traces already implies equality of full term operations. -/
theorem eval_eq_of_possible_iff (s t : Term Var)
    (h : ∀ v, s.eval v = .possible ↔ t.eval v = .possible) :
    ∀ v, s.eval v = t.eval v := by
  intro v
  apply Value.eq_of_possible_tests _ _ (h v)
  · simpa only [eval_collapseB] using h (fun j => Value.collapseB (v j))
  · simpa only [eval_collapseC] using h (fun j => Value.collapseC (v j))

theorem eval_eq_iff_possible_iff (s t : Term Var) :
    (∀ v, s.eval v = t.eval v) ↔ (∀ v, s.eval v = .possible ↔ t.eval v = .possible) :=
  ⟨fun h v => by rw [h v], eval_eq_of_possible_iff s t⟩

@[simp] theorem eval_median (s t u : Term Var) (v : Var → Value) :
    (median s t u).eval v = Value.median (s.eval v) (t.eval v) (u.eval v) := rfl

/-- The neutral lift uses only the original two bichain operations. -/
theorem neutralLift_isPure (t : Term Var) : t.neutralLift.IsPure := by
  induction t <;> simp_all [neutralLift, median, IsPure]

theorem fiberLift_isPure (t : Term Var) : t.fiberLift.IsPure := by
  simp [fiberLift, IsPure, neutralLift_isPure]

/-- At the neutral distinguished input, median elimination is exact. -/
theorem eval_neutralLift (t : Term Var) (v : Option Var → Value) (hv : v none = .neutral) :
    t.neutralLift.eval v = t.eval (fun j => v (some j)) := by
  induction t <;> simp_all [neutralLift, eval, Value.median_neutral]

/-- Every full term has a pure projection-envelope realization. -/
theorem eval_fiberLift (t : Term Var) (v : Option Var → Value) :
    t.fiberLift.eval v = Value.envelope (v none) (t.eval (fun j => v (some j))) := by
  change Value.envelope (v none) (t.neutralLift.eval v) = _
  rw [Value.envelope_cases, Value.envelope_cases]
  cases hx : v none <;> simp only
  rw [eval_neutralLift t v hx]

end Term
end KFOL.Bichain
