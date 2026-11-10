module

public import KFOL.Strategic.Quantified.Reduction

@[expose] public section

namespace KFOLTest.QuantifiedGames

open KFOL.Strategic
open QuantifiedTree

/-- The later witness set is infinite and depends on the first witness. -/
private def later (n : ℕ) : QuantifiedTree (Fin 3) :=
  .node 1 {m : ℕ // n ≤ m} ⟨⟨n, le_rfl⟩⟩
    (fun m => .leaf (if m.val = n then 2 else 0))

private def nested : QuantifiedTree (Fin 3) := .node 0 ℕ ⟨0⟩ later

private def laterPlan (n : ℕ) (chosen : {m : ℕ // n ≤ m}) : Profile (later n) :=
  ⟨chosen, fun _ => PUnit.unit⟩

private theorem laterPlan_spe (n : ℕ) (chosen : {m : ℕ // n ≤ m}) :
    IsSubgamePerfect (laterPlan n chosen) := by
  apply (spe_node_iff 1 _ _ _ _).mpr
  refine ⟨fun _ => spe_leaf _ _, ?_⟩
  rintro ⟨m, hm⟩
  change (if m.val = n then (2 : Fin 3) else 0) = 1 at hm
  split_ifs at hm
  · exact ((by decide : (2 : Fin 3) ≠ 1) hm).elim
  · exact ((by decide : (0 : Fin 3) ≠ 1) hm).elim

private def zeroContinuation (n : ℕ) : Profile (later n) := laterPlan n ⟨n, le_rfl⟩

/-- Only the unreached branch1 uses a witness strictly greater than n. -/
private def offPathContinuation (n : ℕ) : Profile (later n) :=
  laterPlan n ⟨if n = 1 then n+1 else n, by split_ifs <;> omega⟩

private noncomputable def losingPlan : Profile nested := ⟨0, zeroContinuation⟩
private noncomputable def winningPlan : Profile nested := ⟨1, offPathContinuation⟩
private noncomputable def badPlan : Profile nested := ⟨0, offPathContinuation⟩

example : DepthLE 2 nested := by
  intro n m
  trivial

private theorem losingPlan_spe : IsSubgamePerfect losingPlan := by
  apply (spe_node_iff 0 _ _ _ _).mpr
  refine ⟨fun n => laterPlan_spe n _, ?_⟩
  rintro ⟨n, hn⟩
  change (if n = n then (2 : Fin 3) else 0) = 0 at hn
  simp only [ite_true] at hn
  exact ((by decide : (2 : Fin 3) ≠ 0) hn).elim

private theorem winningPlan_spe : IsSubgamePerfect winningPlan := by
  apply (spe_node_iff 0 _ _ _ _).mpr
  exact ⟨fun n => laterPlan_spe n _, fun _ => rfl⟩

example : winner losingPlan = 2 := rfl
example : winner winningPlan = 0 := rfl
example : winner badPlan = 2 := rfl

/-- All continuation plans, including the offending off-path one, are SPE. -/
example (n : ℕ) : IsSubgamePerfect (offPathContinuation n) := laterPlan_spe n _

/-- A complete owner deviation changes the chosen action but preserves the
entire family of continuation profiles. -/
private theorem bad_deviation : Deviation 0 badPlan winningPlan :=
  ⟨fun h => (h rfl).elim, fun n => deviation_refl 0 (later n) (offPathContinuation n)⟩

/-- Local correctness on the realized path is insufficient: an available
winning off-path continuation makes the root profile fail whole-player Nash. -/
example : ¬IsNash badPlan := by
  intro hn
  have hw := hn 0 winningPlan bad_deviation rfl
  exact (by decide : (2 : Fin 3) ≠ 0) hw

example : ¬IsSubgamePerfect badPlan := by
  intro hp
  have hn := spe_nash hp
  have hw := hn 0 winningPlan bad_deviation rfl
  exact (by decide : (2 : Fin 3) ≠ 0) hw

/-- Both winners are witnessed by actual full SPE profiles; every profile's
outcome is one of those two terminal labels. -/
private theorem nested_possibleWinners : possibleWinners nested = ({0, 2} : Set (Fin 3)) := by
  ext player
  constructor
  · rintro ⟨plan, _, hw⟩
    change (if ((plan.2 plan.1).1).val = plan.1 then (2 : Fin 3) else 0) = player at hw
    split_ifs at hw <;> simp only [Set.mem_insert_iff, Set.mem_singleton_iff] <;> aesop
  · intro hp
    rcases hp with hp | hp
    · exact ⟨winningPlan, winningPlan_spe, hp.symm⟩
    · exact ⟨losingPlan, losingPlan_spe, hp.symm⟩


/-- The actual nested infinite/dependent fixture has a nodewise preserving
2-pruning of the same depth, and its binary game's full SPE winners are
exactly the two directly witnessed above. -/
example : ∃ (pruned : QuantifiedTree (Fin 3)) (binary : KFOL.Strategic.Tree (Fin 3))
    (pruning : Prunes 2 nested pruned),
    pruning.PreservesValues ∧ DepthLE 2 pruned ∧
    possibleWinners pruned = ({0, 2} : Set (Fin 3)) ∧
    KFOL.Strategic.possibleWinners binary = ({0, 2} : Set (Fin 3)) := by
  have hd : DepthLE 2 nested := by intro n m; trivial
  obtain ⟨pruned, binary, pruning, preserved, bounded, represented⟩ :=
    exists_value_preserving_pruning_binary_of_depthLE nested 2 hd
  have observed := preserved.possibleWinners_eq.trans nested_possibleWinners
  exact ⟨pruned, binary, pruning, preserved, bounded, observed, represented.trans observed⟩

/-- No source depth bound is required for the stronger well-founded API;
every structural pruning nevertheless has a finite uniform target depth. -/
example (game : QuantifiedTree (Fin 3)) :
    ∃ (pruned : QuantifiedTree (Fin 3)) (binary : KFOL.Strategic.Tree (Fin 3))
      (pruning : Prunes 2 game pruned),
      pruning.PreservesValues ∧ (∃ depth, DepthLE depth pruned) ∧
      KFOL.Strategic.possibleWinners binary = possibleWinners game := by
  obtain ⟨pruned, binary, pruning, preserved, represented⟩ :=
    exists_value_preserving_pruning_binary game
  exact ⟨pruned, binary, pruning, preserved, pruning.exists_depthLE,
    represented.trans preserved.possibleWinners_eq⟩

/-- info: 'KFOL.Strategic.QuantifiedTree.deviation_refl' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Strategic.QuantifiedTree.deviation_refl

/-- info: 'KFOL.Strategic.QuantifiedTree.spe_node_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Strategic.QuantifiedTree.spe_node_iff

/-- info: 'KFOL.Strategic.QuantifiedTree.exists_spe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Strategic.QuantifiedTree.exists_spe

/-- info: 'KFOL.Strategic.QuantifiedTree.possibleWinners_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Strategic.QuantifiedTree.possibleWinners_ne

/-- info: 'KFOL.Strategic.QuantifiedTree.exists_spe_losing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Strategic.QuantifiedTree.exists_spe_losing

/-- info: 'KFOL.Strategic.QuantifiedTree.possibleWinners_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Strategic.QuantifiedTree.possibleWinners_node

/-- info: 'KFOL.Strategic.QuantifiedTree.Prunes.depthLE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Strategic.QuantifiedTree.Prunes.depthLE

/-- info: 'KFOL.Strategic.QuantifiedTree.Prunes.exists_depthLE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Strategic.QuantifiedTree.Prunes.exists_depthLE

/-- info: 'KFOL.Strategic.QuantifiedTree.exists_value_preserving_pruning_binary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Strategic.QuantifiedTree.exists_value_preserving_pruning_binary

/-- info: 'KFOL.Strategic.QuantifiedTree.exists_value_preserving_pruning_binary_of_depthLE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Strategic.QuantifiedTree.exists_value_preserving_pruning_binary_of_depthLE

end KFOLTest.QuantifiedGames
