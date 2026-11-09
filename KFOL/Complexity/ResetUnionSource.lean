module

public import KFOL.Complexity.ResetUnionReduction
public import Complexity.Computability.Complexity.Problems.ThreeSAT
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-! # Exact source syntax and source-class bridge for reset/union hardness -/

@[expose] public section

namespace KFOL.Complexity.ResetUnionSource

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.Reductions
open KFOL.Complexity.ResetUnionMachines

/-- The successor library source is exactly the local elementary CNF type,
with exactly the same binary tuple/list encoding. No reindexing occurs. -/
theorem source_encoding_eq : Cslib.Complexity.encCNF = ResetUnionReduction.cnfEncoding := rfl

theorem source_satisfiable_iff (formula : CNF) :
    Cslib.Logic.PL.CNF.Satisfiable formula ↔ KFOL.Reductions.Satisfiable formula := by
  simp only [Cslib.Logic.PL.CNF.Satisfiable, KFOL.Reductions.Satisfiable,
    Cslib.Logic.PL.CNF.eval_eq_true_iff, Cslib.Logic.PL.Clause.eval_eq_true_iff]

/-- The malformed-source branch is part of a total reduction from the
library's 3SAT language: a wide clause maps to a fixed valid equation. -/
def threeSATReduction (formula : CNF) : KFOL.ResetUnion.Equation :=
  if formula.all (fun clause => decide (clause.length ≤ 3)) then ResetUnion.equation formula
  else (.var 0, .var 0)

private theorem width_polyTime : ComputableInPolyTime
    (fun formula : CNF => formula.all (fun clause => decide (clause.length ≤ 3)))
    ResetUnionReduction.cnfEncoding encBool := by
  have hclause : ComputableInPolyTime (fun clause : Clause => decide (clause.length ≤ 3))
      ResetUnionReduction.clauseEncoding encBool := by fun_prop
  exact allWithInput (test := fun (_ : CNF) (clause : Clause) => decide (clause.length ≤ 3))
    id' (hclause.comp (snd _ _))

/-- The complete total 3SAT generator has a native deterministic polynomial
time machine under the published source and exact target encodings. -/
@[fun_prop] theorem threeSATReduction_polyTime : ComputableInPolyTime threeSATReduction
    Cslib.Complexity.encCNF equationEncoding := by
  rw [source_encoding_eq]
  exact width_polyTime.ite ResetUnionReduction.reduction_polyTime (const ((.var 0, .var 0) : KFOL.ResetUnion.Equation))

/-- The total source-language branch preserves nonmembership, given the
independent algebraic correctness theorem for the actual CNF construction.
The final hardness endpoint instantiates this ordinary reduction rule. -/
theorem reduction_correct_of_equation_correct {Role : Type*}
    (hcorrect : ∀ formula : CNF,
      KFOL.ResetUnion.Valid Role (ResetUnion.equation formula) ↔ ¬KFOL.Reductions.Satisfiable formula)
    (formula : CNF) :
    formula ∉ Cslib.Complexity.ThreeSAT ↔ KFOL.ResetUnion.Valid Role (threeSATReduction formula) := by
  unfold threeSATReduction
  by_cases hw : formula.all (fun clause => decide (clause.length ≤ 3)) = true
  · rw [ite_eq_left hw, hcorrect]
    have hwidth := List.all_eq_true.mp hw
    simp only [decide_eq_true_eq] at hwidth
    change ¬((∀ clause ∈ formula, clause.length ≤ 3) ∧
      Cslib.Logic.PL.CNF.Satisfiable formula) ↔ ¬KFOL.Reductions.Satisfiable formula
    rw [source_satisfiable_iff]
    constructor
    · intro hn hs; exact hn ⟨hwidth, hs⟩
    · intro hn hs; exact hn hs.2
  · rw [ite_eq_right hw]
    constructor
    · intro _ valuation
      rfl
    · intro _ hm
      exact hw (List.all_eq_true.mpr (fun clause hc => decide_eq_true (hm.1 clause hc)))

/-- Generic class transport from the imported machine-level 3SAT completeness
theorem. It is instantiated only after algebraic correctness is established. -/
theorem coNPHard_of_equation_correct {Role : Type*}
    (hcorrect : ∀ formula : CNF,
      KFOL.ResetUnion.Valid Role (ResetUnion.equation formula) ↔ ¬KFOL.Reductions.Satisfiable formula) :
    Cslib.Complexity.coNPHard equationEncoding {e | KFOL.ResetUnion.Valid Role e} := by
  apply Cslib.Complexity.coNPHard.trans Cslib.Complexity.ThreeSAT_npComplete.compl.2
  exact ⟨threeSATReduction, threeSATReduction_polyTime,
    reduction_correct_of_equation_correct hcorrect⟩

end KFOL.Complexity.ResetUnionSource
