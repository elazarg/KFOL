module

public import KFOL.Representation.Morphisms
public import KFOL.Representation.FrameRecovery

/-! # The two recoveries in ideal duality -/

@[expose] public section

namespace KFOL.IdealDuality

universe u v

/-- The entire original semilattice, rather than merely its image, is
recovered as the positive compact elements of its ideal lattice. -/
theorem carrier_recovery (A : Type u) [SemilatticeSup A] :
    Nonempty (A ≃o PositiveCompact (Ideals A)) :=
  ⟨principalEquiv⟩

/-- Every algebraic complete lattice is recovered from the ideals of its
positive compact semilattice. -/
theorem frame_recovery (L : Type u) [CompleteLattice L] [IsCompactlyGenerated L] :
    Nonempty (L ≃o Ideals (PositiveCompact L)) :=
  ⟨frameEquiv⟩

/-- Inverse image and recovery are inverse on all semilattice
homomorphisms and all ideal maps, in both directions. -/
theorem hom_recovery (A : Type u) (B : Type v) [SemilatticeSup A] [SemilatticeSup B] :
    (∀ f : SupHom A B, recoverHom (comap f) = f) ∧
      (∀ g : IdealMap (Ideals B) (Ideals A), comap (recoverHom g) = g) :=
  ⟨recoverHom_comap, comap_recoverHom⟩

end KFOL.IdealDuality
