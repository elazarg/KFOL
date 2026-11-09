module

public import KFOL.Owner.Four
public import Mathlib.Data.Fintype.Pi

/-! # Exhaustive three-element reset reduct classification -/

@[expose] public section

namespace KFOL.Owner

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
/-- Every nonassociative three-element model of the six reset laws has the
unique chain multiplication table, up to naming its three elements. The
finite function space is fully enumerated by kernel reduction. -/
theorem reset_three_classification : ∀ f : Fin 3 → Fin 3 → Fin 3,
    (∀ x, f x x = x) →
    (∀ x y, f (f x y) x = f y x) →
    (∀ x y, f (f x y) y = f x y) →
    (∀ x y z, f x (f (f x y) z) = f x (f y z)) →
    (∀ x y z, f (f (f x y) z) y = f (f x z) y) →
    (∀ x y z, f x (f y z) = f y (f x z)) →
    (∀ x y z, f (f x y) z = f x (f y z)) ∨
      ∃ a b c : Fin 3, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        f a a = a ∧ f a b = b ∧ f a c = c ∧
        f b a = a ∧ f b b = b ∧ f b c = c ∧
        f c a = a ∧ f c b = c ∧ f c c = c := by
  have check : ∀ a01 a02 a10 a12 a20 a21 : Fin 3,
      let f : Fin 3 → Fin 3 → Fin 3 := fun x y => ![![0, a01, a02], ![a10, 1, a12], ![a20, a21, 2]] x y
      (∀ x y, f (f x y) x = f y x) →
      (∀ x y, f (f x y) y = f x y) →
      (∀ x y z, f x (f (f x y) z) = f x (f y z)) →
      (∀ x y z, f (f (f x y) z) y = f (f x z) y) →
      (∀ x y z, f x (f y z) = f y (f x z)) →
      (∀ x y z, f (f x y) z = f x (f y z)) ∨
        ∃ a b c : Fin 3, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
          f a a = a ∧ f a b = b ∧ f a c = c ∧
          f b a = a ∧ f b b = b ∧ f b c = c ∧
          f c a = a ∧ f c b = c ∧ f c c = c := by decide
  intro f hidem
  have h := check (f 0 1) (f 0 2) (f 1 0) (f 1 2) (f 2 0) (f 2 1)
  let table : Fin 3 → Fin 3 → Fin 3 := fun x y => ![![0, f 0 1, f 0 2], ![f 1 0, 1, f 1 2], ![f 2 0, f 2 1, 2]] x y
  have he : table = f := by
    funext x y
    have hx : x = 0 ∨ x = 1 ∨ x = 2 := by omega
    have hy : y = 0 ∨ y = 1 ∨ y = 2 := by omega
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first | exact (hidem _).symm | rfl
  change (∀ x y, table (table x y) x = table y x) →
      (∀ x y, table (table x y) y = table x y) →
      (∀ x y z, table x (table (table x y) z) = table x (table y z)) →
      (∀ x y z, table (table (table x y) z) y = table (table x z) y) →
      (∀ x y z, table x (table y z) = table y (table x z)) →
      (∀ x y z, table (table x y) z = table x (table y z)) ∨
        ∃ a b c : Fin 3, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
          table a a = a ∧ table a b = b ∧ table a c = c ∧
          table b a = a ∧ table b b = b ∧ table b c = c ∧
          table c a = a ∧ table c b = c ∧ table c c = c at h
  rw [he] at h
  exact h

end KFOL.Owner
