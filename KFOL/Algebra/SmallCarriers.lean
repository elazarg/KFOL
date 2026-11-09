module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.EquivFin

/-! # Idempotent binary operations on carriers with at most two elements -/

@[expose] public section

namespace KFOL.Algebra

universe u

/-- Idempotence forces associativity on a two-element carrier. Enumeration
ranges over every binary operation, not a supplied table certificate. -/
theorem idempotent_two_assoc : ∀ f : Fin 2 → Fin 2 → Fin 2,
    (∀ x, f x x = x) → ∀ x y z, f (f x y) z = f x (f y z) := by decide

theorem associative_transfer {M : Type u} {n : ℕ} (e : M ≃ Fin n) (f : M → M → M)
    (h : let g : Fin n → Fin n → Fin n := fun x y => e (f (e.symm x) (e.symm y))
      ∀ x y z, g (g x y) z = g x (g y z)) :
    ∀ x y z, f (f x y) z = f x (f y z) := by
  dsimp only at h
  intro x y z
  apply e.injective
  simpa only [Equiv.symm_apply_apply] using h (e x) (e y) (e z)

/-- Every idempotent binary operation on any finite carrier of size at most
two is associative. This also supplies the small reset-generator exclusion. -/
theorem idempotent_assoc_of_card_le_two {M : Type u} [Fintype M]
    (f : M → M → M) (hi : ∀ x, f x x = x) (hc : Fintype.card M ≤ 2) :
    ∀ x y z, f (f x y) z = f x (f y z) := by
  classical
  have transfer (n : ℕ) (e : M ≃ Fin n)
      (hf : ∀ g : Fin n → Fin n → Fin n,
        (∀ x, g x x = x) → ∀ x y z, g (g x y) z = g x (g y z)) :
      ∀ x y z, f (f x y) z = f x (f y z) := by
    let g : Fin n → Fin n → Fin n := fun x y => e (f (e.symm x) (e.symm y))
    have hg : ∀ x, g x x = x := by intro x; simp only [g, hi, Equiv.apply_symm_apply]
    exact associative_transfer e f (hf g hg)
  have hcases : Fintype.card M = 0 ∨ Fintype.card M = 1 ∨ Fintype.card M = 2 := by omega
  rcases hcases with h | h | h
  · apply transfer 0 (Fintype.equivFinOfCardEq h)
    intro g _ x
    exact x.elim0
  · apply transfer 1 (Fintype.equivFinOfCardEq h)
    exact fun _ _ _ _ _ => Subsingleton.elim _ _
  · exact transfer 2 (Fintype.equivFinOfCardEq h) idempotent_two_assoc

end KFOL.Algebra
