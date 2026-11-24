module

public import KFOL.Core.AddressedQuantified
public import KFOL.Core.AddressedRecognition

/-! # Truth of quantified three-CNF as core recognition of one table -/

@[expose] public section
namespace KFOL.Core.AddressedTableQuantified

open AddressedRails AddressedQuantified AddressedRecognition ProfileBudgets
open Bichain Bichain.Quantified
open scoped Classical
attribute [local instance] Equational.coreStructure

variable {Role Track Bit : Type*} [DecidableEq Role] [Fintype Role]

/-- The full table for a quantified rectangle is realizable exactly when
the original quantified Boolean formula is true. -/
theorem table_iff_sat [Nontrivial Bit] [Fintype Track] [Fintype Bit]
    (three : Fin 3 ↪ Role) (F : Formula) (wf : F.WF) {B : Book (FLab F) Track Bit}
    (G : Geometry F B) (α : ℕ → Bool) :
    (∃ t : CoreTerm Role (Option (Rail (Track ⊕ Bool) Bit)), ∀ v,
      t.realize v = table three G.rectangle Finset.univ (Geometry.initialLeft F α) (Geometry.initialRight F) v)
    ↔ sat F F.n 0 α := by
  rw [table_iff_no_cut, G.cut_iff_not_sat wf α, not_not]
  · exact G.sparseLeft (.br 0 (α 0)) rfl
  · simpa [posted, isLeft, Geometry.initialRight] using G.sparseRight (.relay 0) rfl

/-- Twelve ordinary tracks, two private tracks, and one selector suffice.
There are exactly 28 inputs per address digit and one selector input. -/
theorem three_cnf_iff_table (three : Fin 3 ↪ Role) (F : Formula) (wf : F.WF)
    (short : ∀ q ∈ F.cls, q.length ≤ 3) (α : ℕ → Bool) :
    let T := ThreeSlot.translate F
    let G := translated_geometry F wf short
    (∃ t : CoreTerm Role (Option (Rail (Palette (Fin 3) ⊕ Bool) (Fin (AddressSize.width (labelBound T))))),
      ∀ v, t.realize v = table three G.rectangle Finset.univ
        (Geometry.initialLeft T α) (Geometry.initialRight T) v) ↔ sat F F.n 0 α :=
  (table_iff_sat three _ (ThreeSlot.wf_translate F wf) (translated_geometry F wf short) α).trans
    (ThreeSlot.sat_translate_iff F wf α)

end KFOL.Core.AddressedTableQuantified
