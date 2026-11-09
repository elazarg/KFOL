module
public import KFOL.Definitions.Reductions
public import KFOL.Complexity.Language
public import Complexity.Computability.Complexity.Problems.ThreeSAT
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
@[expose] public section
namespace KFOL.Complexity.CNFHardness
open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.Reductions

private theorem source_satisfiable_iff (formula : CNF) :
    Cslib.Logic.PL.CNF.Satisfiable formula ↔ Satisfiable formula := by
  simp only [Cslib.Logic.PL.CNF.Satisfiable, Satisfiable,
    Cslib.Logic.PL.CNF.eval_eq_true_iff, Cslib.Logic.PL.Clause.eval_eq_true_iff]

private theorem width_polyTime : ComputableInPolyTime
    (fun formula : CNF => formula.all (fun clause => decide (clause.length ≤ 3)))
    Cslib.Complexity.encCNF encBool := by
  have hclause : ComputableInPolyTime (fun clause : Clause => decide (clause.length ≤ 3))
      (encList (encPair encNat encBool)) encBool := by fun_prop
  exact allWithInput (test := fun (_ : CNF) (clause : Clause) => decide (clause.length ≤ 3))
    id' (hclause.comp (snd _ _))

/-- A complete total class transport rule from the pinned machine-certified
3SAT language. Wide source clauses map to an actual member of the target. -/
theorem coNPHard_of_CNF {Target : Type} {encoding : Target ↪ List Bool}
    (predicate : Target → Prop) (reduction : CNF → Target)
    (hruntime : ComputableInPolyTime reduction Cslib.Complexity.encCNF encoding)
    (hcorrect : ∀ formula, predicate (reduction formula) ↔ ¬Satisfiable formula)
    (fallback : Target) (hfallback : predicate fallback) :
    Cslib.Complexity.coNPHard encoding {value | predicate value} := by
  apply Cslib.Complexity.coNPHard.trans Cslib.Complexity.ThreeSAT_npComplete.compl.2
  let total := fun formula : CNF =>
    if formula.all (fun clause => decide (clause.length ≤ 3)) then reduction formula else fallback
  refine ⟨total, width_polyTime.ite hruntime (const fallback), ?_⟩
  intro formula
  change formula ∉ Cslib.Complexity.ThreeSAT ↔ predicate (total formula)
  unfold total
  by_cases hw : formula.all (fun clause => decide (clause.length ≤ 3)) = true
  · rw [ite_eq_left hw, hcorrect]
    have hwidth := List.all_eq_true.mp hw
    simp only [decide_eq_true_eq] at hwidth
    change ¬((∀ clause ∈ formula, clause.length ≤ 3) ∧ Cslib.Logic.PL.CNF.Satisfiable formula) ↔ ¬Satisfiable formula
    rw [source_satisfiable_iff]
    constructor
    · intro hn hs; exact hn ⟨hwidth, hs⟩
    · intro hn hs; exact hn hs.2
  · rw [ite_eq_right hw]
    constructor
    · exact fun _ => hfallback
    · intro _ hm
      exact hw (List.all_eq_true.mpr (fun clause hc => decide_eq_true (hm.1 clause hc)))
/-- An injective target code transports hardness to its complete binary image,
whose independent existential clause rejects malformed target words. -/
theorem coNPHard_encode {Target : Type} (encoding : Target ↪ List Bool)
    (predicate : Target → Prop) (hard : Cslib.Complexity.coNPHard encoding {target | predicate target}) :
    Cslib.Complexity.coNPHard encBits
      {word | ∃ target, encoding target = word ∧ predicate target} := by
  apply Cslib.Complexity.coNPHard.trans hard
  refine ⟨encoding, ComputableInPolyTime.of_eq (fun _ => rfl), ?_⟩
  intro target
  constructor
  · intro h
    exact ⟨target, rfl, h⟩
  · rintro ⟨other, he, ho⟩
    exact encoding.injective he ▸ ho
end KFOL.Complexity.CNFHardness
