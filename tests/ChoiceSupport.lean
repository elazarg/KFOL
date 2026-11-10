module

public import KFOL.Strategic.ChoiceSupport

@[expose] public section

namespace KFOLTest.ChoiceSupport

open KFOL

open Classical in
/-- Nat is genuinely infinite: only the role type needs a Fintype instance. -/
example (values : ℕ → WinnerSet (Fin 2)) :
    ∃ (S : Finset ℕ) (hS : S.Nonempty), S.card ≤ 1 ∧
      (WinnerSet.choiceFold 0 S hS values).val =
        if ∃ i, values i = WinnerSet.singleton 0 then {0}
        else {r | ∃ i, r ∈ (values i).val} := by
  classical
  simpa using WinnerSet.exists_small_choice_support (0 : Fin 2) values

example (branches : ℕ → Strategic.Tree (Fin 3)) :
    ∃ (S : Finset ℕ) (_ : S.Nonempty) (term : Term (Fin 3) S),
      S.card ≤ 2 ∧ term.IsCore ∧
      Strategic.possibleWinners (Strategic.compile (fun i : S => branches i.val) term) =
        Strategic.FiniteChoice.possibleWinners 0 branches := by
  simpa using Strategic.FiniteChoice.exists_small_binary_tree (0 : Fin 3) branches

private def full : Finset (Fin 4) := Finset.univ.erase 0
private def two : Finset (Fin 4) := {1, 2}

example : full.card = 3 := by decide
example :
    (WinnerSet.choiceFold 0 full (by decide) WinnerSet.singleton).val = {r | r ≠ (0 : Fin 4)} := by
  rw [WinnerSet.choiceFold_singletons 0 full (by decide) (by decide)]
  ext r
  simp only [full, Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true, Set.mem_ofPred_eq]

/-- Two terminal continuations cannot reproduce the three nonowner winners. -/
example : Strategic.FiniteChoice.possibleWinners (0 : Fin 4)
    (fun i : two => Strategic.Tree.leaf i.val) ≠ {r | r ≠ 0} := by
  intro he
  have hc := Strategic.FiniteChoice.terminal_support_sharp (0 : Fin 4) two
    (by decide) (by decide) he |>.2
  have hn : two.card ≠ Fintype.card (Fin 4) - 1 := by decide
  exact hn hc

/-- info: 'KFOL.WinnerSet.exists_small_union_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.WinnerSet.exists_small_union_support

/-- info: 'KFOL.WinnerSet.exists_small_choice_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.WinnerSet.exists_small_choice_support

/-- info: 'KFOL.WinnerSet.exists_small_choice_isLUB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.WinnerSet.exists_small_choice_isLUB

/-- info: 'KFOL.WinnerSet.choice_support_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.WinnerSet.choice_support_sharp

/-- info: 'KFOL.Term.exists_core_choice_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Term.exists_core_choice_fold

/-- info: 'KFOL.Strategic.FiniteChoice.possibleWinners_restrict_eq_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Strategic.FiniteChoice.possibleWinners_restrict_eq_fold

/-- info: 'KFOL.Strategic.FiniteChoice.exists_small_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Strategic.FiniteChoice.exists_small_support

/-- info: 'KFOL.Strategic.FiniteChoice.exists_small_binary_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Strategic.FiniteChoice.exists_small_binary_tree

/-- info: 'KFOL.Strategic.FiniteChoice.terminal_support_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Strategic.FiniteChoice.terminal_support_sharp

end KFOLTest.ChoiceSupport
