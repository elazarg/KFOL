module

public import KFOL.Representation.Ideals
public import KFOL.Representation.Adjoints

/-! # Full recovery of semilattice homomorphisms from ideal-lattice maps -/

@[expose] public section

namespace KFOL.IdealDuality

universe u v w

variable {A : Type u} {B : Type v} {C : Type w}
variable [SemilatticeSup A] [SemilatticeSup B] [SemilatticeSup C]

/-- Adjoin a new bottom to a join homomorphism. -/
def withBotHom (f : SupHom A B) : SupHom (WithBot A) (WithBot B) where
  toFun := WithBot.map f
  map_sup' x y := by
    cases x with
    | bot => simp
    | coe x =>
      cases y with
      | bot => simp
      | coe y => simp [← WithBot.coe_sup]

@[simp] theorem withBotHom_coe (f : SupHom A B) (a : A) :
    withBotHom f (a : WithBot A) = (f a : WithBot B) := rfl

/-- Inverse image of an ideal under a semilattice homomorphism. -/
def idealPreimage (f : SupHom A B) (J : Ideals B) : Ideals A where
  carrier := {x | withBotHom f x ∈ J}
  lower' := fun _ _ hxy hy => J.lower (OrderHomClass.mono (withBotHom f) hxy) hy
  nonempty' := ⟨⊥, J.bot_mem⟩
  directed' := by
    intro x hx y hy
    refine ⟨x ⊔ y, ?_, le_sup_left, le_sup_right⟩
    change withBotHom f (x ⊔ y) ∈ J
    rw [map_sup]
    exact Order.Ideal.sup_mem hx hy

@[simp] theorem mem_idealPreimage (f : SupHom A B) (J : Ideals B) (a : WithBot A) :
    a ∈ idealPreimage f J ↔ withBotHom f a ∈ J := Iff.rfl

theorem idealPreimage_mono (f : SupHom A B) : Monotone (idealPreimage f) :=
  fun _ _ h _ hx => h hx

/-- Every semilattice homomorphism gives a contravariant ideal-lattice map. -/
def comap (f : SupHom A B) : IdealMap (Ideals B) (Ideals A) where
  toFun := idealPreimage f
  map_sInf' S := by
    apply Order.Ideal.ext
    ext a
    change withBotHom f a ∈ sInf S ↔ a ∈ sInf (idealPreimage f '' S)
    simp only [Order.Ideal.mem_sInf]
    constructor
    · intro h J hJ
      obtain ⟨K, hK, rfl⟩ := hJ
      exact h K hK
    · intro h J hJ
      exact h _ ⟨J, hJ, rfl⟩
  map_bot' := by
    apply Order.Ideal.ext
    ext a
    cases a with
    | bot => exact ⟨fun _ => Order.Ideal.bot_mem _, fun _ => Order.Ideal.bot_mem _⟩
    | coe a =>
      change (f a : WithBot B) ∈ (⊥ : Ideals B) ↔ (a : WithBot A) ∈ (⊥ : Ideals A)
      simp [← Order.Ideal.principal_bot]
  map_directed_sSup' S hne hdir := by
    apply Order.Ideal.ext
    ext a
    have hd : DirectedOn (· ≤ ·) (idealPreimage f '' S) := by
      rintro _ ⟨I, hI, rfl⟩ _ ⟨J, hJ, rfl⟩
      obtain ⟨K, hK, hIK, hJK⟩ := hdir I hI J hJ
      exact ⟨idealPreimage f K, ⟨K, hK, rfl⟩,
        idealPreimage_mono f hIK, idealPreimage_mono f hJK⟩
    change a ∈ idealPreimage f (sSup S) ↔ a ∈ sSup (idealPreimage f '' S)
    rw [mem_idealPreimage,
      mem_sSup_iff_of_directed S hne hdir (withBotHom f a),
      mem_sSup_iff_of_directed _ (hne.image _) hd a]
    constructor
    · rintro ⟨J, hJ, ha⟩
      exact ⟨idealPreimage f J, ⟨J, hJ, rfl⟩, ha⟩
    · rintro ⟨_, ⟨J, hJ, rfl⟩, ha⟩
      exact ⟨J, hJ, ha⟩

@[simp] theorem comap_apply (f : SupHom A B) (J : Ideals B) :
    comap f J = idealPreimage f J := rfl

/-- Inverse image respects identity maps. -/
@[simp] theorem comap_id (J : Ideals A) : comap (SupHom.id A) J = J := by
  apply Order.Ideal.ext
  ext x
  cases x <;> rfl

/-- Composition is reversed by the ideal representation. -/
theorem comap_comp (f : SupHom A B) (g : SupHom B C) (J : Ideals C) :
    comap (g.comp f) J = comap f (comap g J) := by
  apply Order.Ideal.ext
  ext x
  cases x <;> rfl

theorem lowerAdjoint_comap_principal (f : SupHom A B) (a : A) :
    IdealMap.lowerAdjoint (comap f) (principal a) = principal (f a) := by
  apply le_antisymm
  · apply (IdealMap.gc (comap f) _ _).mpr
    apply principal_le_iff.mpr
    change (f a : WithBot B) ∈ principal (f a)
    exact Order.Ideal.mem_principal_self
  · apply principal_le_iff.mpr
    have h := IdealMap.le_apply_lowerAdjoint (comap f) (principal a)
    have ha := principal_le_iff.mp h
    exact ha

@[simp] theorem onCompacts_comap (f : SupHom A B) (a : A) :
    IdealMap.onCompacts (comap f) (principalEquiv a) = principalEquiv (f a) := by
  apply Subtype.ext
  exact lowerAdjoint_comap_principal f a

/-- The algebra homomorphism determined by an ideal-lattice map. -/
noncomputable def recoverHom (g : IdealMap (Ideals B) (Ideals A)) : SupHom A B :=
  ((principalEquiv (A := B)).symm : SupHom _ _).comp
    ((IdealMap.onCompacts g).comp (principalEquiv (A := A) : SupHom _ _))

theorem principal_recoverHom (g : IdealMap (Ideals B) (Ideals A)) (a : A) :
    principal (recoverHom g a) = IdealMap.lowerAdjoint g (principal a) := by
  have h := (principalEquiv (A := B)).apply_symm_apply
    (IdealMap.onCompacts g (principalEquiv (A := A) a))
  exact congrArg Subtype.val h

@[simp] theorem recoverHom_comap (f : SupHom A B) : recoverHom (comap f) = f := by
  apply DFunLike.ext
  intro a
  apply principal_injective
  rw [principal_recoverHom, lowerAdjoint_comap_principal]

@[simp] theorem comap_recoverHom (g : IdealMap (Ideals B) (Ideals A)) :
    comap (recoverHom g) = g := by
  apply DFunLike.ext
  intro J
  apply Order.Ideal.ext
  ext x
  cases x with
  | bot => exact ⟨fun _ => Order.Ideal.bot_mem _, fun _ => Order.Ideal.bot_mem _⟩
  | coe a =>
    change (recoverHom g a : WithBot B) ∈ J ↔ (a : WithBot A) ∈ g J
    rw [← principal_le_iff, principal_recoverHom, IdealMap.gc, principal_le_iff]

/-- Inverse-image maps are exactly the ideal-lattice morphisms. -/
noncomputable def homEquiv :
    SupHom A B ≃ IdealMap (Ideals B) (Ideals A) where
  toFun := comap
  invFun := recoverHom
  left_inv := recoverHom_comap
  right_inv := comap_recoverHom

end KFOL.IdealDuality
