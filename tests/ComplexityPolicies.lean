module
public import KFOL.Complexity.PolicyWordFrontend
@[expose] public section
namespace KFOLTest.ComplexityPolicies
open KFOL KFOL.Policies KFOL.Complexity Turing.MultiTapeTM

def duplicatingPlan : Hardness.Plan Unit Unit where
  zero := .inf (.atom ()) (.atom ())
  one := .atom ()
  preliminary := []
  calibration := []
example : (PolicyReductionMachines.clauseAt duplicatingPlan 3 [(2^30,true),(0,true),(1,true)]).size = 57 := by decide
example : (duplicatingPlan.clause [(2^30,true),(0,true),(1,true),(2,true)]).size = 121 := by decide
example : (PolicyReductionMachines.clauseAt duplicatingPlan 3 [(2^30,true),(0,true),(1,true),(2,true)]).size = 57 := by decide
example {Role Label : Type} [Fintype Label] (code : Role ↪ ℕ) (plan : Hardness.Plan Role Label) :
    ComputableInPolyTime (PolicyReductionMachines.equationAt code plan)
      PolicyReductionMachines.cnfEncoding PolicyReductionMachines.equationEncoding :=
  PolicyReductionMachines.reduction_polyTime code plan
example {Role Label : Type} [Fintype Label] (code : Role ↪ ℕ) (plan : Hardness.Plan Role Label)
    (formula : Reductions.CNF) (width : ∀ clause ∈ formula, clause.length ≤ 3) :
    PolicyReductionMachines.equationAt code plan formula =
      ((plan.equation formula).1.relabel (Hardness.Variable.toNat code),
       (plan.equation formula).2.relabel (Hardness.Variable.toNat code)) :=
  PolicyReductionMachines.equationAt_eq code plan formula width
example {Role Label : Type} [Fintype Role] [Fintype Label]
    (D : Label → Set Role) (three : Fin 3 ↪ Role) (code : Role ↪ ℕ) (hne : ¬FamilyEasy D) :
    Cslib.Complexity.coNPComplete encBits (PolicyCompleteness.Language D) :=
  PolicyCompleteness.language_coNPComplete D three code hne
private def D (_ : Unit) : Finset (Fin 3) := ∅
private theorem easy : FamilyEasy (fun d => (D d : Set (Fin 3))) := by
  left
  intro r s
  left
  simp [passingPattern, D]
example : PolicyTermFrontend.checkWord D [0,1,2] [()] [] = false := rfl
example : PolicyCompleteness.Language (fun d => (D d : Set (Fin 3))) ∈ Cslib.Complexity.P encBits :=
  PolicyTermFrontend.language_mem_P (Function.Embedding.refl (Fin 3)) D easy
example {Role Label : Type} [Fintype Role] [Fintype Label] [DecidableEq Role] [DecidableEq Label]
    (D : Label → Finset Role) (three : Fin 3 ↪ Role) (code : Role ↪ ℕ) :
    (FamilyEasy (fun d => (D d : Set Role)) → PolicyCompleteness.Language (fun d => (D d : Set Role)) ∈ Cslib.Complexity.P encBits) ∧
    (¬FamilyEasy (fun d => (D d : Set Role)) → Cslib.Complexity.coNPComplete encBits (PolicyCompleteness.Language (fun d => (D d : Set Role)))) :=
  PolicyTermFrontend.language_dichotomy three D code

end KFOLTest.ComplexityPolicies
