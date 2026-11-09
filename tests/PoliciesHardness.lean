module

public import KFOL.Policies.Public

@[expose] public section

namespace KFOLTest.PoliciesHardness

open KFOL.Policies

private def missingMeetFamily (d : Fin 2) : Finset (Fin 3) := if d = 0 then {0} else {1}
private def calibratedFamily (d : Fin 2) : Finset (Fin 3) := if d = 0 then {0, 1} else {0, 2}

example : familyEasyB missingMeetFamily (List.finRange 3) (List.finRange 2) = false := by decide
example : familyEasyB calibratedFamily (List.finRange 3) (List.finRange 2) = false := by decide

private theorem not_easy_of_false (D : Fin 2 → Finset (Fin 3))
    (h : familyEasyB D (List.finRange 3) (List.finRange 2) = false) :
    ¬FamilyEasy (fun d => (D d : Set (Fin 3))) := by
  intro he
  have ht := (familyEasyB_correct D (List.finRange 3) (List.finRange 2)
    (fun r => by simp) (fun d => by simp)).mpr he
  simp only [h, Bool.false_eq_true] at ht

example : ∃ plan : Hardness.Plan (Fin 3) (Fin 2), ∀ formula : KFOL.Reductions.CNF,
    (∀ valuation : ℕ → KFOL.WinnerSet (Fin 3),
      Term.eval (fun d => (missingMeetFamily d : Set (Fin 3)))
        ((plan.equation formula).1.relabel (Hardness.Variable.toNat ⟨Fin.val, Fin.val_injective⟩)) valuation =
      Term.eval (fun d => (missingMeetFamily d : Set (Fin 3)))
        ((plan.equation formula).2.relabel (Hardness.Variable.toNat ⟨Fin.val, Fin.val_injective⟩)) valuation) ↔
      ¬KFOL.Reductions.Satisfiable formula :=
  non_easy_family_nat_cnf_reduction _ (Function.Embedding.refl _) ⟨Fin.val, Fin.val_injective⟩
    (not_easy_of_false missingMeetFamily (by decide))

example : ∃ plan : Hardness.Plan (Fin 3) (Fin 2), ∀ formula : KFOL.Reductions.CNF,
    (∀ valuation : Hardness.Variable (Fin 3) → KFOL.WinnerSet (Fin 3),
      (plan.equation formula).1.eval (fun d => (calibratedFamily d : Set (Fin 3))) valuation =
      (plan.equation formula).2.eval (fun d => (calibratedFamily d : Set (Fin 3))) valuation) ↔
      ¬KFOL.Reductions.Satisfiable formula :=
  non_easy_family_cnf_reduction _ (Function.Embedding.refl _)
    (not_easy_of_false calibratedFamily (by decide))

example (code : Fin 3 ↪ ℕ) (i : ℕ) :
    Hardness.Variable.toNat code (.boolean i) ≠ Hardness.Variable.toNat code (.calibration 0) := by
  intro h
  have hi := Hardness.Variable.toNat_injective code h
  cases hi

/-- info: 'KFOL.Policies.non_easy_family_nat_cnf_reduction' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Policies.non_easy_family_nat_cnf_reduction

/-- info: 'KFOL.Policies.Hardness.Plan.equation_size_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Policies.Hardness.Plan.equation_size_le

/-- info: 'KFOL.Policies.Hardness.Plan.calibration_identified' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Policies.Hardness.Plan.calibration_identified

end KFOLTest.PoliciesHardness
