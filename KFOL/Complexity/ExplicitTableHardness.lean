module

public import KFOL.Complexity.AddressedCompiler
public import KFOL.Complexity.AddressedIncidenceCorrectness
public import KFOL.Complexity.AddressedRawReduction

/-! # PSPACE-hardness for the full explicit table on a multitape Turing machine

The reduction reads arbitrary binary variable names. Its output gives an arity
and all nonempty-input tuples in the order determined by that arity.
-/

@[expose] public section
namespace KFOL.Complexity.ExplicitTableHardness

open Bichain.Quantified Core Core.AddressedQuantified Core.ExplicitTableReduction
open AddressedCompiler AddressedIncidence AddressedPoint Recognition.Lists

/-- Checked on actual encoded inputs, including open formulas and empty matrices. -/
theorem output_iff {K : ℕ} (three : Fin 3 ↪ Fin K) (u : ExplicitTableReduction.Input) :
    RawAccepts K (output K (three 0).val (three 1).val (three 2).val u) ↔
      u ∈ Cslib.Complexity.TQBFCNF := by
  let T := ThreeCNF.translate (formulaOf u)
  let F := ThreeCNF.fromTQBFCNF u
  let G := translated_geometry T (ThreeCNF.wf_translate _) (ThreeCNF.width _)
  exact (rawAccepts_table_iff three G.rectangle Finset.univ
    (Geometry.initialLeft F (fun _ => false)) (Geometry.initialRight F)
    (ids F) trackEquiv (layout u) (codes_correct T)
    (rowData_correct F _ (exAt_input u) G true) (rowData_correct F _ (exAt_input u) G false)).trans
    (winner_table_iff three u)

/-- The numbering used in every emitted tuple, including the retained selector. -/
noncomputable def rank (u : ExplicitTableReduction.Input) :
    Variables u ≃ Fin (AddressTableOutput.arity 14 (labels u)) :=
  coordEquiv trackEquiv (AddressSize.width (labels u))

/-- Each individual output entry represents the semantic target also on false QBFs. -/
theorem output_entry {K : ℕ} (three : Fin 3 ↪ Fin K) (u : ExplicitTableReduction.Input)
    (i : ℕ) (hi : i < AddressTableOutput.count K 14 (labels u)) (v : Variables u → WinnerSet (Fin K))
    (input : ∀ j, FullSparseEvaluation.Represents (AddressTableOutput.menu K i (rank u j).val) (v j)) :
    FullSparseEvaluation.Represents
      ((output K (three 0).val (three 1).val (three 2).val u).2.getD i []) (target three u v) := by
  let T := ThreeCNF.translate (formulaOf u)
  let F := ThreeCNF.fromTQBFCNF u
  let G := translated_geometry T (ThreeCNF.wf_translate _) (ThreeCNF.width _)
  let menus := AddressTableOutput.tuple K (AddressTableOutput.arity 14 (labels u)) i
  have vals (j : Variables u) : FullSparseEvaluation.Represents (menus.getD (rank u j).val []) (v j) := by
    dsimp only [menus]
    rw [AddressTableOutput.tuple_getD _ _ _ _ (rank u j).isLt]
    exact input j
  change FullSparseEvaluation.Represents
    ((filled K (three 0).val (three 1).val (three 2).val 14 (labels u) (layout u)).2.getD i []) _
  rw [filled_getD _ i hi]
  exact point_represents three G.rectangle Finset.univ (Geometry.initialLeft F (fun _ => false))
    (Geometry.initialRight F) (ids F) railIndex (layout u) (codes_correct T)
    (rowData_correct F _ (exAt_input u) G true) (rowData_correct F _ (exAt_input u) G false)
    menus v (vals none) (fun j => vals (some j))

/-- Truth of quantified CNF polynomial-time many-one reduces to the complete table language. -/
theorem reducible {K : ℕ} (three : Fin 3 ↪ Fin K) :
    Cslib.Complexity.PolyTimeReducible Cslib.Complexity.encPrenexCNF rawEncoding
      Cslib.Complexity.TQBFCNF {p | RawAccepts K p} :=
  ⟨output K (three 0).val (three 1).val (three 2).val, output_poly ..,
    fun u => (output_iff three u).symm⟩

/-- The full table of a core operation is PSPACE-hard to recognize at every
fixed owner count of at least three. -/
theorem pspaceHard {K : ℕ} (three : Fin 3 ↪ Fin K) :
    Cslib.Complexity.PSPACEHard rawEncoding {p | RawAccepts K p} :=
  Cslib.Complexity.TQBFCNF_pspaceHard.trans (reducible three)

end KFOL.Complexity.ExplicitTableHardness
