module

public import KFOL.Reductions.RawSubsignature
public import Mathlib.Data.Fintype.Card

@[expose] public section

namespace KFOLTest.ReductionsRawSubsignature

open KFOL

private def infiniteRoleSignature : Finset (Raw.Operation ℕ) := {.choice 1000000000, .reset}

/-- A selected finite alphabet does not require a finite role carrier. -/
example : Fintype.card ((n : ℕ) × Raw.Symbol infiniteRoleSignature n) = 2 := by
  calc
    _ = Fintype.card {op // op ∈ infiniteRoleSignature} :=
      Fintype.card_congr (Raw.operationEquiv infiniteRoleSignature)
    _ = 2 := by
      change Fintype.card infiniteRoleSignature = 2
      rw [Fintype.card_coe]
      decide


example (s t : Raw.Term ({.choice (0 : Fin 3)} : Finset _) ℕ) :
    s.support = t.support ↔ ∀ v, s.eval v = t.eval v :=
  Raw.Term.support_eq_iff_valid_choice 0 1 (by decide) rfl s t

example (s t : Raw.Term ({.union} : Finset (Raw.Operation (Fin 3))) ℕ) :
    s.support = t.support ↔ ∀ v, s.eval v = t.eval v :=
  Raw.Term.support_eq_iff_valid_union 0 1 (by decide) rfl s t

example (s t : Raw.Term (∅ : Finset (Raw.Operation (Fin 3))) ℕ) :
    Raw.Valid ∅ (s, t) ↔ s = t := Raw.valid_empty_iff 0 1 (by decide) rfl s t

example (s : Raw.Term ({.reset} : Finset (Raw.Operation (Fin 3))) ℕ) (v : ℕ → WinnerSet (Fin 3)) :
    (s.toReset rfl).eval v = s.eval v := Raw.Term.eval_toReset rfl s v

example (selected : Finset (Raw.Operation (Fin 3))) (h : 1 < selected.card) :
    ∃ reduction : Reductions.CNF → Raw.Term selected ℕ × Raw.Term selected ℕ,
      ∀ formula, Raw.Valid selected (reduction formula) ↔ ¬Reductions.Satisfiable formula :=
  Raw.exists_cnf_reduction (Function.Embedding.refl _) selected h

/-- info: 'KFOL.Raw.Term.eval_ofRawPair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Raw.Term.eval_ofRawPair

/-- info: 'KFOL.Raw.Term.size_ofRawPair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Raw.Term.size_ofRawPair

/-- info: 'KFOL.Raw.Term.varFinset_ofRawPair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Raw.Term.varFinset_ofRawPair

/-- info: 'KFOL.Raw.Term.eval_eq_sup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Raw.Term.eval_eq_sup

/-- info: 'KFOL.Raw.Term.support_eq_iff_valid_choice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Raw.Term.support_eq_iff_valid_choice

/-- info: 'KFOL.Raw.Term.support_eq_iff_valid_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Raw.Term.support_eq_iff_valid_union

/-- info: 'KFOL.Raw.Term.exists_var_of_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Raw.Term.exists_var_of_empty

/-- info: 'KFOL.Raw.Term.eval_ofResetUnion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Raw.Term.eval_ofResetUnion

/-- info: 'KFOL.Raw.Term.size_ofResetUnion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Raw.Term.size_ofResetUnion

/-- info: 'KFOL.Raw.Term.eval_toReset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Raw.Term.eval_toReset

/-- info: 'KFOL.Raw.Reduction.valid_resetUnion_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Raw.Reduction.valid_resetUnion_iff

/-- info: 'KFOL.Raw.Reduction.valid_choiceUnion_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Raw.Reduction.valid_choiceUnion_iff

/-- info: 'KFOL.Raw.Reduction.valid_twoChoices_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Raw.Reduction.valid_twoChoices_iff

/-- info: 'KFOL.Raw.Reduction.valid_resetChoice_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Raw.Reduction.valid_resetChoice_iff

/-- info: 'KFOL.Raw.exists_hard_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Raw.exists_hard_pair

/-- info: 'KFOL.Raw.Term.support_eq_varFinset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Raw.Term.support_eq_varFinset

/-- info: 'KFOL.Raw.small_signature_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Raw.small_signature_cases

/-- info: 'KFOL.Raw.valid_empty_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Raw.valid_empty_iff

/-- info: 'KFOL.Raw.exists_cnf_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Raw.exists_cnf_reduction

end KFOLTest.ReductionsRawSubsignature
