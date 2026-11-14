module

public import KFOL.Definitions.IdealDuality
public import Mathlib.Order.GaloisConnection.Basic

/-! # The adjoints of ideal-lattice maps preserve positive compacts -/

@[expose] public section

namespace KFOL.IdealDuality.IdealMap

universe u v w

variable {L : Type u} {M : Type v} {N : Type w}
variable [CompleteLattice L] [CompleteLattice M] [CompleteLattice N]

/-- The uniquely determined left adjoint of an ideal-lattice map. -/
noncomputable def lowerAdjoint (g : IdealMap L M) (y : M) : L :=
  sInf {x : L | y ≤ g x}

theorem le_apply_lowerAdjoint (g : IdealMap L M) (y : M) : y ≤ g (lowerAdjoint g y) := by
  rw [lowerAdjoint, map_sInf]
  apply le_sInf
  rintro _ ⟨x, hx, rfl⟩
  exact hx

theorem gc (g : IdealMap L M) : GaloisConnection (lowerAdjoint g) g := by
  intro y x
  constructor
  · intro h
    exact (le_apply_lowerAdjoint g y).trans (OrderHomClass.mono g h)
  · intro h
    exact sInf_le h

@[simp] theorem lowerAdjoint_sup (g : IdealMap L M) (x y : M) :
    lowerAdjoint g (x ⊔ y) = lowerAdjoint g x ⊔ lowerAdjoint g y := (gc g).l_sup

theorem lowerAdjoint_ne_bot (g : IdealMap L M) {y : M} (hy : y ≠ ⊥) :
    lowerAdjoint g y ≠ ⊥ := by
  intro h
  have he := le_apply_lowerAdjoint g y
  rw [h] at he
  change y ≤ g.toFun ⊥ at he
  rw [g.map_bot'] at he
  exact hy (le_bot_iff.mp he)

theorem lowerAdjoint_compact (g : IdealMap L M) {y : M} (hy : IsCompactElement y) :
    IsCompactElement (lowerAdjoint g y) := by
  rw [isCompactElement_iff_le_of_directed_sSup_le] at hy ⊢
  intro S hne hdir hle
  have hs : y ≤ sSup (g '' S) := by
    change y ≤ sSup (g.toFun '' S)
    rw [← g.map_directed_sSup' S hne hdir]
    exact (gc g _ _).mp hle
  have hd : DirectedOn (· ≤ ·) (g '' S) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hac, hbc⟩ := hdir a ha b hb
    exact ⟨g c, ⟨c, hc, rfl⟩, OrderHomClass.mono g hac, OrderHomClass.mono g hbc⟩
  obtain ⟨_, ⟨x, hx, rfl⟩, hxy⟩ := hy (g '' S) (hne.image g) hd hs
  exact ⟨x, hx, (gc g _ _).mpr hxy⟩

/-- The contravariant action of an ideal-lattice map on the recovered
semilattices of positive compact elements. -/
noncomputable def onCompacts (g : IdealMap L M) :
    SupHom (PositiveCompact M) (PositiveCompact L) where
  toFun y := ⟨lowerAdjoint g y.1, lowerAdjoint_compact g y.2.1,
    lowerAdjoint_ne_bot g y.2.2⟩
  map_sup' x y := Subtype.ext (lowerAdjoint_sup g x.1 y.1)

end KFOL.IdealDuality.IdealMap
