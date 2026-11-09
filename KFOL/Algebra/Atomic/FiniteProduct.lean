module

public import KFOL.Algebra.Atomic.Matrix
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Function.Basic

/-! # Finite-product functions preserving the repeated-entry relation -/

@[expose] public section

namespace KFOL.Atomic

universe u v w

/-- Coordinatewise invariance makes a function on a finite product constant. -/
theorem eq_of_update_invariant {Index : Type u} [Finite Index] [DecidableEq Index] {Input : Type v}
    {Output : Type w} (f : (Index → Input) → Output)
    (h : ∀ x i a, f (Function.update x i a) = f x) (x y : Index → Input) : f x = f y := by
  classical
  let := Fintype.ofFinite Index
  have aux (S : Finset Index) : ∀ x y : Index → Input,
      (∀ i, i ∉ S → x i = y i) → f x = f y := by
    induction S using Finset.induction_on with
    | empty =>
      intro x y he
      exact congrArg f (funext fun i => he i (by simp))
    | @insert i S hi ih =>
      intro x y he
      calc
        f x = f (Function.update x i (y i)) := (h x i (y i)).symm
        _ = f y := ih _ _ (by
          intro j hj
          by_cases hji : j = i
          · subst j; simp
          · simpa [Function.update_of_ne hji] using he j (by simp [hj,hji]))
  exact aux Finset.univ x y (by simp)

/-- The repeated-entry relation alone forces every finite-product operation
with more than two values to depend on one coordinate. This is the finite
Slupecki lemma, proved directly through rectangle corners. -/
theorem essentiallyUnary_or_atMostTwo {Index : Type u} [Finite Index]
    {Input : Type v} [Nonempty Input] {Output : Type w}
    (f : (Index → Input) → Output) (hf : PreservesRepeat f) :
    EssentiallyUnary f ∨ AtMostTwo f := by
  classical
  by_cases hsmall : AtMostTwo f
  · exact Or.inr hsmall
  have sensitive : ∃ i x a, f (Function.update x i a) ≠ f x := by
    by_contra hn
    have invariant : ∀ x i a, f (Function.update x i a) = f x := by
      intro x i a
      by_contra he
      exact hn ⟨i,x,a,he⟩
    let base : Index → Input := fun _ => Classical.choice inferInstance
    exact hsmall ⟨f base,f base,fun x => Or.inl (eq_of_update_invariant f invariant x base)⟩
  obtain ⟨i,base,a,ha⟩ := sensitive
  let g (x : Index → Input) (a : Input) := f (Function.update x i a)
  have corners : ∀ r s x y, Repeat (g r x) (g r y) (g s x) := by
    intro r s x y
    apply hf
    intro j
    by_cases hji : j = i
    · subst j
      exact Or.inr (Or.inl (by simp))
    · exact Or.inl (by simp [Function.update_of_ne hji])
  have hrow : g base a ≠ g base (base i) := by simpa [g] using ha
  rcases matrix_of_nonconstant_row g corners base a (base i) hrow with htwo | heq
  · obtain ⟨p,q,hpq⟩ := htwo
    exact False.elim (hsmall ⟨p,q,fun x => by simpa [g] using hpq (x,x i)⟩)
  · exact Or.inl ⟨i,g base,fun x => by simpa [g] using heq x (x i)⟩

end KFOL.Atomic
