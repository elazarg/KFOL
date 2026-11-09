module

public import KFOL.Algebra.Basic
public import Mathlib.Order.BooleanAlgebra.Defs

/-! # Owned choices do not embed in products of Boolean meet/join coordinates -/

@[expose] public section

namespace KFOL

universe u v w

private def latticeChoice {M : Type u} [Lattice M] (b : Bool) (x y : M) : M :=
  if b then x ⊔ y else x ⊓ y

private theorem latticeChoice_distributes {M : Type u} [DistribLattice M]
    (p q : Bool) (x y z : M) :
    latticeChoice q (latticeChoice p x y) z =
      latticeChoice p (latticeChoice q x z) (latticeChoice q y z) := by
  cases p <;> cases q
  · simp [latticeChoice,inf_assoc,inf_left_comm]
  · exact sup_inf_right _ _ _
  · exact inf_sup_right _ _ _
  · simp [latticeChoice,sup_assoc,sup_left_comm]

namespace WinnerSet

variable {Role : Type u}

/-- Three distinct roles explicitly refute mutual distribution of owned choices. -/
theorem choice_not_mutually_distributive (three : Fin 3 ↪ Role) :
    choice (three 1) (choice (three 0) (singleton (three 0)) (singleton (three 1))) (singleton (three 2)) ≠
      choice (three 0) (choice (three 1) (singleton (three 0)) (singleton (three 2)))
        (choice (three 1) (singleton (three 1)) (singleton (three 2))) := by
  classical
  have h01 : three 0 ≠ three 1 := three.injective.ne (by decide)
  have h02 : three 0 ≠ three 2 := three.injective.ne (by decide)
  have h12 : three 1 ≠ three 2 := three.injective.ne (by decide)
  intro he
  have hl : three 1 ∉ (choice (three 1)
      (choice (three 0) (singleton (three 0)) (singleton (three 1))) (singleton (three 2))).val := by
    simp [choice,singleton_inj,union,h01,h12,Ne.symm h01,Ne.symm h12]
  have hU : union (singleton (three 0)) (singleton (three 2)) ≠ singleton (three 0) := by
    intro hu
    have hc : three 2 ∈ (union (singleton (three 0)) (singleton (three 2))).val := Or.inr rfl
    rw [hu] at hc
    exact h02 hc.symm
  have hr : three 1 ∈ (choice (three 0)
      (choice (three 1) (singleton (three 0)) (singleton (three 2)))
      (choice (three 1) (singleton (three 1)) (singleton (three 2)))).val := by
    simp [choice,singleton_inj,hU,h01,Ne.symm h01,Ne.symm h12]
  exact hl (he ▸ hr)

/-- No injective map can preserve all owned choices into coordinatewise
meet/join operations. Distributive lattices already suffice for the
obstruction, so in particular products of Boolean algebras are excluded. -/
theorem no_boolean_product_embedding (three : Fin 3 ↪ Role)
    {Index : Type v} (M : Index → Type w) [∀ i, DistribLattice (M i)]
    (select : Role → Index → Bool) (f : WinnerSet Role → ∀ i, M i)
    (hf : ∀ r A B i, f (choice r A B) i =
      if select r i then f A i ⊔ f B i else f A i ⊓ f B i) :
    ¬Function.Injective f := by
  intro hinj
  apply choice_not_mutually_distributive three
  apply hinj
  funext i
  simpa only [hf,latticeChoice] using latticeChoice_distributes
    (select (three 0) i) (select (three 1) i)
    (f (singleton (three 0)) i) (f (singleton (three 1)) i) (f (singleton (three 2)) i)

end WinnerSet

end KFOL
