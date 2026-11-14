module

public import KFOL.Representation.Cooperations
public import KFOL.Representation.Morphisms

/-! # Operator homomorphisms are exactly commuting ideal-lattice diagrams -/

@[expose] public section

namespace KFOL.IdealDuality

universe u v w z

namespace BiIdeal

variable {A : Type u} {B : Type v} {A' : Type w} {B' : Type z}
variable [SemilatticeSup A] [SemilatticeSup B] [SemilatticeSup A'] [SemilatticeSup B']

/-- Inverse image of a biideal along a pair of join homomorphisms. -/
def preimage (f : SupHom A' A) (g : SupHom B' B) (R : BiIdeal A B) : BiIdeal A' B' where
  carrier := {p | (f p.1, g p.2) ∈ R}
  lower' := fun ha hb h => R.lower' (OrderHomClass.mono f ha) (OrderHomClass.mono g hb) h
  sup_left' := by
    intro a a' b h h'
    change (f (a ⊔ a'), g b) ∈ R
    rw [map_sup]
    exact R.sup_left' h h'
  sup_right' := by
    intro a b b' h h'
    change (f a, g (b ⊔ b')) ∈ R
    rw [map_sup]
    exact R.sup_right' h h'

@[simp] theorem mem_preimage (f : SupHom A' A) (g : SupHom B' B)
    (R : BiIdeal A B) (p : A' × B') :
    p ∈ preimage f g R ↔ (f p.1, g p.2) ∈ R := Iff.rfl

end BiIdeal

variable {A : Type u} {B : Type v} [SemilatticeSup A] [SemilatticeSup B]

/-- Algebraic preservation of an entire binary operation is equivalent to
its contravariant ideal/biideal naturality diagram. -/
theorem preserves_operation_iff_diagram
    (f : SupHom A B) (m : SupHom A (SupHom A A)) (n : SupHom B (SupHom B B)) :
    (∀ a b, f (m a b) = n (f a) (f b)) ↔
      ∀ J : Ideals B, BiIdeal.operation m (comap f J) =
        BiIdeal.preimage f f (BiIdeal.operation n J) := by
  constructor
  · intro h J
    apply BiIdeal.ext
    rintro ⟨a, b⟩
    change (f (m a b) : WithBot B) ∈ J ↔ (n (f a) (f b) : WithBot B) ∈ J
    rw [h]
  · intro h a b
    have memeq (J : Ideals B) :
        (f (m a b) : WithBot B) ∈ J ↔ (n (f a) (f b) : WithBot B) ∈ J := by
      exact Iff.of_eq (congrArg (fun R : BiIdeal A A => (a, b) ∈ R) (h J))
    apply le_antisymm
    · exact (mem_principal _ _).mp ((memeq (principal (n (f a) (f b)))).mpr
        Order.Ideal.mem_principal_self)
    · exact (mem_principal _ _).mp ((memeq (principal (f (m a b)))).mp
        Order.Ideal.mem_principal_self)

end KFOL.IdealDuality
