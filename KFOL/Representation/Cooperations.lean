module

public import KFOL.Representation.Biideals
public import KFOL.Representation.Adjoints
public import KFOL.Representation.FrameRecovery

/-! # Binary co-operations and reconstruction of join-bilinear operations -/

@[expose] public section

namespace KFOL.IdealDuality

universe u v w

variable {A : Type u} {B : Type v} {C : Type w}
variable [SemilatticeSup A] [SemilatticeSup B] [SemilatticeSup C]

/-- Every join-bilinear operation determines a map of ideal lattices into
the biideal lattice. -/
def cooperation (f : SupHom A (SupHom B C)) :
    IdealMap (Ideals C) (BiIdeal A B) where
  toFun := BiIdeal.operation f
  map_sInf' S := by
    apply BiIdeal.ext
    intro p
    simp only [BiIdeal.mem_operation, Order.Ideal.mem_sInf, BiIdeal.mem_sInf]
    constructor
    · intro h R hR
      obtain ⟨J, hJ, rfl⟩ := hR
      exact h J hJ
    · intro h J hJ
      exact h _ ⟨J, hJ, rfl⟩
  map_bot' := by
    apply BiIdeal.ext
    intro p
    change (f p.1 p.2 : WithBot C) ∈ (⊥ : Ideals C) ↔ p ∈ (⊥ : BiIdeal A B)
    simp [← Order.Ideal.principal_bot, Order.Ideal.mem_principal]
  map_directed_sSup' S hne hdir := by
    apply BiIdeal.ext
    intro p
    have hm : Monotone (BiIdeal.operation f) := fun _ _ h _ hp => h hp
    have hd : DirectedOn (· ≤ ·) (BiIdeal.operation f '' S) := by
      rintro _ ⟨I, hI, rfl⟩ _ ⟨J, hJ, rfl⟩
      obtain ⟨K, hK, hIK, hJK⟩ := hdir I hI J hJ
      exact ⟨BiIdeal.operation f K, ⟨K, hK, rfl⟩, hm hIK, hm hJK⟩
    rw [BiIdeal.mem_operation,
      mem_sSup_iff_of_directed S hne hdir (f p.1 p.2 : WithBot C),
      BiIdeal.mem_sSup_iff_of_directed _ (hne.image _) hd p]
    constructor
    · rintro ⟨J, hJ, hp⟩
      exact ⟨BiIdeal.operation f J, ⟨J, hJ, rfl⟩, hp⟩
    · rintro ⟨_, ⟨J, hJ, rfl⟩, hp⟩
      exact ⟨J, hJ, hp⟩

@[simp] theorem cooperation_apply (f : SupHom A (SupHom B C)) (J : Ideals C) :
    cooperation f J = BiIdeal.operation f J := rfl

/-- The adjoint of the inverse-image co-operation recovers the original
operation at every principal rectangle. -/
theorem lowerAdjoint_cooperation_rectangle (f : SupHom A (SupHom B C)) (a : A) (b : B) :
    IdealMap.lowerAdjoint (cooperation f) (BiIdeal.rectangle a b) = principal (f a b) := by
  apply le_antisymm
  · apply (IdealMap.gc (cooperation f) _ _).mpr
    apply BiIdeal.rectangle_le_iff.mpr
    change (f a b : WithBot C) ∈ principal (f a b)
    exact Order.Ideal.mem_principal_self
  · apply principal_le_iff.mpr
    exact BiIdeal.rectangle_le_iff.mp
      (IdealMap.le_apply_lowerAdjoint (cooperation f) (BiIdeal.rectangle a b))

section Reconstruction

variable {L : Type u} [CompleteLattice L]

/-- Recover a binary operation from its abstract ideal-lattice co-operation. -/
noncomputable def reconstruct
    (δ : IdealMap L (BiIdeal (PositiveCompact L) (PositiveCompact L))) :
    SupHom (PositiveCompact L) (SupHom (PositiveCompact L) (PositiveCompact L)) where
  toFun a :=
    { toFun := fun b =>
        ⟨IdealMap.lowerAdjoint δ (BiIdeal.rectangle a b),
          IdealMap.lowerAdjoint_compact δ (BiIdeal.rectangle_compact a b),
          IdealMap.lowerAdjoint_ne_bot δ (BiIdeal.rectangle_ne_bot a b)⟩
      map_sup' b c := by
        apply Subtype.ext
        exact congrArg (IdealMap.lowerAdjoint δ) (BiIdeal.rectangle_sup_right a b c) |>.trans
          (IdealMap.lowerAdjoint_sup δ _ _) }
  map_sup' a b := by
    apply DFunLike.ext
    intro c
    apply Subtype.ext
    exact congrArg (IdealMap.lowerAdjoint δ) (BiIdeal.rectangle_sup_left a b c) |>.trans
      (IdealMap.lowerAdjoint_sup δ _ _)

/-- The recovered operation and the co-operation satisfy the defining
membership adjunction, for every abstract lattice element. -/
theorem mem_cooperation_iff_reconstruct
    (δ : IdealMap L (BiIdeal (PositiveCompact L) (PositiveCompact L)))
    (x : L) (a b : PositiveCompact L) :
    (a, b) ∈ δ x ↔ (reconstruct δ a b).1 ≤ x := by
  rw [← BiIdeal.rectangle_le_iff]
  exact (IdealMap.gc δ _ _).symm

/-- Reconstruction is inverse to the co-operation on every lattice element,
after the canonical recovery of the lattice as ideals of positive compacts. -/
theorem cooperation_reconstruct
    (δ : IdealMap L (BiIdeal (PositiveCompact L) (PositiveCompact L))) (x : L) :
    BiIdeal.operation (reconstruct δ) (compactIdeal x) = δ x := by
  apply BiIdeal.ext
  rintro ⟨a, b⟩
  rw [BiIdeal.mem_operation, mem_compactIdeal]
  exact (mem_cooperation_iff_reconstruct δ x a b).symm

end Reconstruction

/-- Transport a bimorphism from a carrier to the positive compacts of its
canonical lattice. -/
noncomputable def compactArguments (f : SupHom A (SupHom A A)) :
    SupHom (PositiveCompact (Ideals A)) (SupHom (PositiveCompact (Ideals A)) A) where
  toFun a := (f ((principalEquiv (A := A)).symm a)).comp
    ((principalEquiv (A := A)).symm : SupHom _ _)
  map_sup' a b := by
    apply DFunLike.ext
    intro c
    simp only [SupHom.comp_apply, map_sup, SupHom.sup_apply]

/-- The co-operation of a bimorphism, with coordinates already on the
positive compacts of the canonical ideal lattice. -/
noncomputable def canonicalCooperation (f : SupHom A (SupHom A A)) :
    IdealMap (Ideals A)
      (BiIdeal (PositiveCompact (Ideals A)) (PositiveCompact (Ideals A))) :=
  cooperation (compactArguments f)

/-- Representation preserves the entire binary operation, not just the
semilattice order or its principal embedding. -/
theorem reconstruct_canonicalCooperation (f : SupHom A (SupHom A A)) (a b : A) :
    reconstruct (canonicalCooperation f) (principalEquiv a) (principalEquiv b) =
      principalEquiv (f a b) := by
  apply Subtype.ext
  change IdealMap.lowerAdjoint (cooperation (compactArguments f))
    (BiIdeal.rectangle (principalEquiv a) (principalEquiv b)) = principal (f a b)
  rw [lowerAdjoint_cooperation_rectangle]
  simp [compactArguments]

end KFOL.IdealDuality
