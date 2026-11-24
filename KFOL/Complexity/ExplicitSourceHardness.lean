module

public import KFOL.Complexity.AddressedSourceCorrectness
public import KFOL.Complexity.ExplicitTableHardness

/-! # PSPACE-hardness for the packed complete source table -/

@[expose] public section
namespace KFOL.Complexity.ExplicitSourceHardness

open AddressedSourceOutput AddressedCompiler Core.ExplicitTableReduction
open AddressTableOutput Turing.MultiTapeTM

/-- The emitted winner lists agree with the target under their declared
coordinate ordering, whether the quantified formula is true or false. -/
theorem winner_rows {K : ℕ} (three : Fin 3 ↪ Fin K) (u : Input) :
    let out := output K (three 0).val (three 1).val (three 2).val u
    WinnerRows K out.1 out.2 (fun v => target three u (fun j => v (ExplicitTableHardness.rank u j))) := by
  dsimp only
  have len := AddressTableOutput.table_length K 14 labels
    (fun x v => AddressedPoint.point K (three 0).val (three 1).val (three 2).val (layout x) v) u
  refine ⟨len,?_⟩
  intro i hi v bits
  have inRange : i < count K 14 (labels u) := by rwa [← len]
  apply AddressedPoint.represents_mem
  apply ExplicitTableHardness.output_entry three u i inRange
  intro j
  apply AddressedPoint.represents_ext
  · intro s mem
    exact (menu_mem _ _ _ _).mp mem |>.1
  · intro r
    exact ((menu_mem _ _ _ _).trans (and_iff_right r.isLt)).trans (bits _ r)

/-- The concrete bit stream has a word agreeing at every canonical probe
exactly when the input prenex formula is true. -/
theorem output_iff {K : ℕ} (three : Fin 3 ↪ Fin K) (u : Input) :
    project K (output K (three 0).val (three 1).val (three 2).val u) ∈ language three ↔
      u ∈ Cslib.Complexity.TQBFCNF :=
  (project_native_iff three (ExplicitTableHardness.rank u) (winner_rows three u)).trans
    (source_table_iff three u)

/-- A polynomial-time many-one reduction to the source table with d*K^d bits. -/
theorem reducible {K : ℕ} (three : Fin 3 ↪ Fin K) :
    Cslib.Complexity.PolyTimeReducible Cslib.Complexity.encPrenexCNF sourceEncoding
      Cslib.Complexity.TQBFCNF (language three) :=
  ⟨fun u => project K (output K (three 0).val (three 1).val (three 2).val u),
    (project_poly K).comp (output_poly ..), fun u => (output_iff three u).symm⟩

/-- Recognition of the complete canonical source table is PSPACE-hard
for every fixed owner count of at least three. -/
theorem pspaceHard {K : ℕ} (three : Fin 3 ↪ Fin K) :
    Cslib.Complexity.PSPACEHard sourceEncoding (language three) :=
  Cslib.Complexity.TQBFCNF_pspaceHard.trans (reducible three)

end KFOL.Complexity.ExplicitSourceHardness
