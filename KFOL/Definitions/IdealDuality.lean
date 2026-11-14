module

public import Mathlib.Order.Ideal
public import Mathlib.Order.WithBot
public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.Order.Hom.CompleteLattice

/-! # Ideal and biideal vocabulary for semilattice representation

Ideals of `WithBot A` permit the empty ideal of the original unbounded
semilattice. Positive compact elements recover that original carrier.
Binary co-operations take values in biideals, with joins closed separately
in the two coordinates.
-/

@[expose] public section

namespace KFOL.IdealDuality

universe u v w

/-- The ideal completion of an unbounded join-semilattice, including its
empty ideal through the newly adjoined bottom. -/
abbrev Ideals (A : Type u) [SemilatticeSup A] := Order.Ideal (WithBot A)

/-- Positive compact elements of a complete lattice. Bottom is compact in
mathlib's convention and is excluded explicitly. -/
def PositiveCompact (L : Type u) [CompleteLattice L] :=
  {x : L // IsCompactElement x ∧ x ≠ ⊥}

namespace PositiveCompact

variable {L : Type u} [CompleteLattice L]

instance : PartialOrder (PositiveCompact L) := inferInstanceAs
  (PartialOrder {x : L // IsCompactElement x ∧ x ≠ ⊥})

instance : Max (PositiveCompact L) where
  max x y := ⟨x.1 ⊔ y.1, x.2.1.sup y.2.1, by
    intro h
    exact x.2.2 (le_bot_iff.mp (le_sup_left.trans_eq h))⟩

instance : SemilatticeSup (PositiveCompact L) where
  sup := (· ⊔ ·)
  le_sup_left := fun _ _ => le_sup_left (α := L)
  le_sup_right := fun _ _ => le_sup_right (α := L)
  sup_le := fun _ _ _ hx hy => sup_le hx hy

end PositiveCompact

/-- The order-theoretic maps in the ideal dual category. Preservation of
all meets includes top; preservation of bottom is a separate condition. -/
structure IdealMap (L : Type u) (M : Type v) [CompleteLattice L] [CompleteLattice M]
    extends sInfHom L M where
  map_bot' : toFun ⊥ = ⊥
  map_directed_sSup' (s : Set L) (hne : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s) :
    toFun (sSup s) = sSup (toFun '' s)

namespace IdealMap

variable {L : Type u} {M : Type v} [CompleteLattice L] [CompleteLattice M]

instance : FunLike (IdealMap L M) L M where
  coe f := f.toFun
  coe_injective := by
    intro f g h
    cases f
    cases g
    congr
    exact DFunLike.coe_injective h

instance : sInfHomClass (IdealMap L M) L M where
  map_sInf := fun f => f.map_sInf'

end IdealMap

/-- A downward relation closed under joins separately in either coordinate.
There is no nonemptiness requirement. -/
structure BiIdeal (A : Type u) (B : Type v) [SemilatticeSup A] [SemilatticeSup B] where
  carrier : Set (A × B)
  lower' : ∀ {a a' : A} {b b' : B}, a' ≤ a → b' ≤ b → (a, b) ∈ carrier →
    (a', b') ∈ carrier
  sup_left' : ∀ {a a' : A} {b : B}, (a, b) ∈ carrier → (a', b) ∈ carrier →
    (a ⊔ a', b) ∈ carrier
  sup_right' : ∀ {a : A} {b b' : B}, (a, b) ∈ carrier → (a, b') ∈ carrier →
    (a, b ⊔ b') ∈ carrier

namespace BiIdeal

variable {A : Type u} {B : Type v} [SemilatticeSup A] [SemilatticeSup B]

instance : SetLike (BiIdeal A B) (A × B) where
  coe := carrier
  coe_injective := by
    intro x y h
    cases x
    cases y
    cases h
    rfl

instance : PartialOrder (BiIdeal A B) := .ofSetLike (BiIdeal A B)

@[ext] theorem ext {R S : BiIdeal A B} (h : ∀ p, p ∈ R ↔ p ∈ S) : R = S :=
  SetLike.ext h

/-- The principal rectangle at a pair of semilattice elements. -/
def rectangle (a : A) (b : B) : BiIdeal A B where
  carrier := {p | p.1 ≤ a ∧ p.2 ≤ b}
  lower' ha hb h := ⟨ha.trans h.1, hb.trans h.2⟩
  sup_left' h h' := ⟨sup_le h.1 h'.1, h.2⟩
  sup_right' h h' := ⟨h.1, sup_le h.2 h'.2⟩

end BiIdeal

end KFOL.IdealDuality
