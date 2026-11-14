module

public import KFOL.Representation.Ideals
public import KFOL.Representation.Adjoints

/-! # Every algebraic ideal lattice is recovered from its positive compacts -/

@[expose] public section

namespace KFOL.IdealDuality

universe u

variable {L : Type u} [CompleteLattice L]

/-- The ideal of positive compact elements below one lattice element. -/
def compactIdeal (x : L) : Ideals (PositiveCompact L) where
  carrier := {p | WithBot.recBotCoe True (fun c => c.1 ≤ x) p}
  lower' := by
    intro q p hpq hq
    cases p with
    | bot => trivial
    | coe p =>
      cases q with
      | bot => exact False.elim (WithBot.not_coe_le_bot p hpq)
      | coe q =>
        change q.1 ≤ x at hq
        have hpq' : p.1 ≤ q.1 :=
          (WithBot.coe_le_coe (α := PositiveCompact L)).mp hpq
        exact hpq'.trans hq
  nonempty' := ⟨⊥, by change True; trivial⟩
  directed' := by
    intro p hp q hq
    refine ⟨p ⊔ q, ?_, le_sup_left, le_sup_right⟩
    cases p with
    | bot => simpa using hq
    | coe p =>
      cases q with
      | bot => simpa using hp
      | coe q => exact sup_le hp hq

@[simp] theorem mem_compactIdeal (x : L) (c : PositiveCompact L) :
    (c : WithBot (PositiveCompact L)) ∈ compactIdeal x ↔ c.1 ≤ x := Iff.rfl

/-- The lattice value represented by an ideal of positive compacts. -/
noncomputable def idealValue (J : Ideals (PositiveCompact L)) : L :=
  sSup {x : L | ∃ c : PositiveCompact L,
    (c : WithBot (PositiveCompact L)) ∈ J ∧ c.1 = x}

theorem mem_le_idealValue {J : Ideals (PositiveCompact L)} {c : PositiveCompact L}
    (hc : (c : WithBot (PositiveCompact L)) ∈ J) : c.1 ≤ idealValue J :=
  le_sSup ⟨c, hc, rfl⟩

@[simp] theorem idealValue_bot : idealValue (⊥ : Ideals (PositiveCompact L)) = ⊥ := by
  apply le_antisymm
  · apply sSup_le
    rintro x ⟨c, hc, _⟩
    exact False.elim (WithBot.coe_ne_bot (le_bot_iff.mp (Order.Ideal.mem_principal.mp hc)))
  · exact bot_le

theorem compactIdeal_idealValue (J : Ideals (PositiveCompact L)) :
    compactIdeal (idealValue J) = J := by
  apply Order.Ideal.ext
  ext p
  cases p with
  | bot => exact ⟨fun _ => J.bot_mem, fun _ => Order.Ideal.bot_mem _⟩
  | coe c =>
    change (c : WithBot (PositiveCompact L)) ∈ compactIdeal (idealValue J) ↔
      (c : WithBot (PositiveCompact L)) ∈ J
    rw [mem_compactIdeal]
    constructor
    · intro hc
      by_cases hJ : J = ⊥
      · rw [hJ, idealValue_bot] at hc
        exact False.elim (c.2.2 (le_bot_iff.mp hc))
      have hn : ∃ d : PositiveCompact L, (d : WithBot (PositiveCompact L)) ∈ J := by
        by_contra h
        exact hJ ((eq_bot_iff J).mpr (by simpa only [not_exists] using h))
      let S : Set L := {x | ∃ d : PositiveCompact L,
        (d : WithBot (PositiveCompact L)) ∈ J ∧ d.1 = x}
      have hne : S.Nonempty := by
        obtain ⟨d, hd⟩ := hn
        exact ⟨d.1, d, hd, rfl⟩
      have hdir : DirectedOn (· ≤ ·) S := by
        rintro _ ⟨d, hd, rfl⟩ _ ⟨e, he, rfl⟩
        refine ⟨(d ⊔ e).1, ⟨d ⊔ e, ?_, rfl⟩, le_sup_left, le_sup_right⟩
        rw [WithBot.coe_sup]
        exact Order.Ideal.sup_mem hd he
      obtain ⟨_, ⟨d, hd, rfl⟩, hcd⟩ :=
        (isCompactElement_iff_le_of_directed_sSup_le c.1).mp c.2.1 S hne hdir hc
      exact J.lower (WithBot.coe_le_coe.mpr hcd) hd
    · exact mem_le_idealValue

theorem idealValue_compactIdeal [IsCompactlyGenerated L] (x : L) :
    idealValue (compactIdeal x) = x := by
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨c, hc, rfl⟩
    exact (mem_compactIdeal x c).mp hc
  · apply le_iff_forall_isCompactElement.mpr
    intro c hc hcx
    by_cases hz : c = ⊥
    · simpa only [hz] using (bot_le : (⊥ : L) ≤ idealValue (compactIdeal x))
    · exact mem_le_idealValue ((mem_compactIdeal x ⟨c, hc, hz⟩).mpr hcx)

/-- Algebraic complete lattices are exactly the canonical ideal lattices of
their positive compact semilattices. -/
noncomputable def frameEquiv [IsCompactlyGenerated L] :
    L ≃o Ideals (PositiveCompact L) where
  toFun := compactIdeal
  invFun := idealValue
  left_inv := idealValue_compactIdeal
  right_inv := compactIdeal_idealValue
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      apply le_iff_forall_isCompactElement.mpr
      intro c hc hcx
      by_cases hz : c = ⊥
      · simpa only [hz] using (bot_le : (⊥ : L) ≤ y)
      · exact (mem_compactIdeal y ⟨c, hc, hz⟩).mp
          (h ((mem_compactIdeal x ⟨c, hc, hz⟩).mpr hcx))
    · intro h p hp
      cases p with
      | bot => exact Order.Ideal.bot_mem _
      | coe p => exact ((mem_compactIdeal x p).mp hp).trans h

end KFOL.IdealDuality
