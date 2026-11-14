module

public import KFOL.Definitions.IdealDuality

/-! # Positive compact recovery from the canonical ideal completion -/

@[expose] public section

namespace KFOL.IdealDuality

universe u v

variable {A : Type u} [SemilatticeSup A]

/-- The canonical representative of a semilattice element. -/
def principal (a : A) : Ideals A := Order.Ideal.principal (a : WithBot A)

@[simp] theorem mem_principal (a b : A) : (a : WithBot A) ∈ principal b ↔ a ≤ b := by
  simp [principal]

@[simp] theorem principal_le_iff {a : A} {J : Ideals A} :
    principal a ≤ J ↔ (a : WithBot A) ∈ J := Order.Ideal.principal_le_iff

theorem principal_ne_bot (a : A) : principal a ≠ ⊥ := by
  intro h
  have ha : (a : WithBot A) ∈ principal a := Order.Ideal.mem_principal_self
  rw [h] at ha
  exact WithBot.coe_ne_bot (le_bot_iff.mp (Order.Ideal.mem_principal.mp ha))

instance [Nonempty A] : Nontrivial (Ideals A) :=
  ⟨⟨principal (Classical.choice (inferInstance : Nonempty A)), ⊥, principal_ne_bot _⟩⟩

@[simp] theorem principal_le_principal (a b : A) : principal a ≤ principal b ↔ a ≤ b := by
  rw [principal_le_iff, mem_principal]

theorem principal_injective : Function.Injective (principal : A → Ideals A) := by
  intro a b h
  exact le_antisymm ((principal_le_principal a b).mp h.le)
    ((principal_le_principal b a).mp h.ge)

theorem principal_sup (a b : A) : principal (a ⊔ b) = principal a ⊔ principal b := by
  apply le_antisymm
  · apply principal_le_iff.mpr
    rw [WithBot.coe_sup]
    exact Order.Ideal.sup_mem
      ((principal_le_iff.mp le_sup_left)) ((principal_le_iff.mp le_sup_right))
  · exact sup_le ((principal_le_principal _ _).mpr le_sup_left)
      ((principal_le_principal _ _).mpr le_sup_right)

/-- A nonempty directed join of ideals is their set union. -/
theorem mem_sSup_iff_of_directed (S : Set (Ideals A)) (hne : S.Nonempty)
    (hdir : DirectedOn (· ≤ ·) S) (a : WithBot A) :
    a ∈ sSup S ↔ ∃ J ∈ S, a ∈ J := by
  let U : Ideals A :=
    { carrier := {x | ∃ J ∈ S, x ∈ J}
      lower' := by
        intro x y hxy hy
        obtain ⟨J, hJ, hyJ⟩ := hy
        exact ⟨J, hJ, J.lower hxy hyJ⟩
      nonempty' := by
        obtain ⟨J, hJ⟩ := hne
        obtain ⟨x, hx⟩ := J.nonempty
        exact ⟨x, J, hJ, hx⟩
      directed' := by
        intro x hx y hy
        obtain ⟨I, hI, hxI⟩ := hx
        obtain ⟨J, hJ, hyJ⟩ := hy
        obtain ⟨K, hK, hIK, hJK⟩ := hdir I hI J hJ
        exact ⟨x ⊔ y, ⟨K, hK, Order.Ideal.sup_mem (hIK hxI) (hJK hyJ)⟩,
          le_sup_left, le_sup_right⟩ }
  have hU : sSup S = U := by
    apply le_antisymm
    · exact sSup_le fun J hJ x hx => ⟨J, hJ, hx⟩
    · intro x hx
      obtain ⟨J, hJ, hxJ⟩ := hx
      exact le_sSup hJ hxJ
  rw [hU]
  rfl

theorem principal_compact (a : A) : IsCompactElement (principal a) := by
  rw [isCompactElement_iff_le_of_directed_sSup_le]
  intro S hne hdir hle
  have ha : (a : WithBot A) ∈ sSup S := principal_le_iff.mp hle
  obtain ⟨J, hJ, haJ⟩ := (mem_sSup_iff_of_directed S hne hdir _).mp ha
  exact ⟨J, hJ, principal_le_iff.mpr haJ⟩

theorem eq_bot_iff (J : Ideals A) : J = ⊥ ↔ ∀ a : A, (a : WithBot A) ∉ J := by
  constructor
  · rintro rfl a ha
    exact WithBot.coe_ne_bot (le_bot_iff.mp (Order.Ideal.mem_principal.mp ha))
  · intro h
    apply le_antisymm
    · intro x hx
      cases x with
      | bot => exact Order.Ideal.bot_mem _
      | coe a => exact False.elim (h a hx)
    · exact bot_le

/-- Every ideal is the join of the principal ideals it contains. -/
theorem sSup_principal_below (J : Ideals A) :
    sSup {P : Ideals A | ∃ a : A, (a : WithBot A) ∈ J ∧ P = principal a} = J := by
  apply le_antisymm
  · apply sSup_le
    rintro P ⟨a, ha, rfl⟩
    exact principal_le_iff.mpr ha
  · intro x hx
    cases x with
    | bot => exact Order.Ideal.bot_mem _
    | coe a =>
      have hP : principal a ≤ sSup {P : Ideals A |
          ∃ b : A, (b : WithBot A) ∈ J ∧ P = principal b} := le_sSup ⟨a, hx, rfl⟩
      exact hP Order.Ideal.mem_principal_self

theorem compact_ne_bot_iff_principal (J : Ideals A) :
    IsCompactElement J ∧ J ≠ ⊥ ↔ ∃ a : A, J = principal a := by
  constructor
  · rintro ⟨hc, hn⟩
    let S : Set (Ideals A) := {P | ∃ a : A, (a : WithBot A) ∈ J ∧ P = principal a}
    have hne : S.Nonempty := by
      have hm : ∃ a : A, (a : WithBot A) ∈ J := by
        by_contra h
        exact hn ((eq_bot_iff J).mpr (by simpa only [not_exists] using h))
      obtain ⟨a, ha⟩ := hm
      exact ⟨principal a, a, ha, rfl⟩
    have hdir : DirectedOn (· ≤ ·) S := by
      rintro P ⟨a, ha, rfl⟩ Q ⟨b, hb, rfl⟩
      refine ⟨principal (a ⊔ b), ⟨a ⊔ b, ?_, rfl⟩, ?_, ?_⟩
      · rw [WithBot.coe_sup]
        exact Order.Ideal.sup_mem ha hb
      · exact (principal_le_principal _ _).mpr le_sup_left
      · exact (principal_le_principal _ _).mpr le_sup_right
    have he : sSup S = J := sSup_principal_below J
    obtain ⟨P, ⟨a, ha, rfl⟩, hJP⟩ :=
      (isCompactElement_iff_le_of_directed_sSup_le J).mp hc S hne hdir he.ge
    exact ⟨a, le_antisymm hJP (principal_le_iff.mpr ha)⟩
  · rintro ⟨a, rfl⟩
    exact ⟨principal_compact a, principal_ne_bot a⟩

instance : IsCompactlyGenerated (Ideals A) where
  exists_isLUB J := ⟨{P | ∃ a : A, (a : WithBot A) ∈ J ∧ P = principal a}, by
    rintro P ⟨a, _, rfl⟩
    exact principal_compact a, by
      have h := isLUB_sSup {P : Ideals A | ∃ a : A,
        (a : WithBot A) ∈ J ∧ P = principal a}
      rw [sSup_principal_below J] at h
      exact h⟩

/-- Every element of an abstract semilattice is recovered uniquely as a
positive compact in its ideal lattice. -/
noncomputable def principalEquiv : A ≃o PositiveCompact (Ideals A) where
  toFun a := ⟨principal a, principal_compact a, principal_ne_bot a⟩
  invFun J := Classical.choose ((compact_ne_bot_iff_principal J.1).mp J.2)
  left_inv a := by
    apply principal_injective
    exact (Classical.choose_spec ((compact_ne_bot_iff_principal (principal a)).mp
      ⟨principal_compact a, principal_ne_bot a⟩)).symm
  right_inv J := by
    apply Subtype.ext
    exact (Classical.choose_spec ((compact_ne_bot_iff_principal J.1).mp J.2)).symm
  map_rel_iff' := by
    intro a b
    exact principal_le_principal a b

end KFOL.IdealDuality
