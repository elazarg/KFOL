module

public import KFOL.Reset.Realizability.Necessity
public import KFOL.Reset.Realizability.Synthesis
public import KFOL.Reset.Realizability.Recognition

/-! # Compact table realizability and certified bounded syntax size -/

@[expose] public section

namespace KFOL.Reset.GuardTable

universe v

variable {Var : Type v} [DecidableEq Var] [Fintype Var]

/-- The complete mathematical realizability criterion. -/
theorem wellFormed_iff_realizable (G : GuardTable Var) : G.WellFormed ↔
    ∃ t : Term Var, t.root = G.root ∧ t.table = G.guards := by
  constructor
  · intro h
    obtain ⟨t, hr, ht, _⟩ := G.exists_term_bounded h
    exact ⟨t, hr, ht⟩
  · rintro ⟨t, hr, ht⟩
    have he : t.guardTable = G := by
      cases G
      cases hr
      cases ht
      rfl
    rw [← he]
    exact t.guardTable_wellFormed

/-- The checker is connected to actual terms rather than an unconnected
certificate. The returned bound counts primitive tree occurrences. -/
theorem check_iff_bounded_realization (G : GuardTable Var) : G.check = true ↔
    ∃ t : Term Var, t.root = G.root ∧ t.table = G.guards ∧
      t.size ≤ 1 + 2 * Fintype.card Var * G.entryCount :=
  ⟨fun h => G.exists_term_bounded (G.check_eq_true.mp h),
    fun ⟨t, hr, ht, _⟩ => G.check_eq_true.mpr (G.wellFormed_iff_realizable.mpr ⟨t, hr, ht⟩)⟩

end KFOL.Reset.GuardTable
