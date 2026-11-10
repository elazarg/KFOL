module

public import KFOL.Strategic.Quantified.Basic
public import KFOL.Strategic.Adequacy

/-! # Structural owned-choice fold compilation

The syntax certificate records the original owner's binary nodes and a
complete duplicate-free enumeration of the original finite menu. Semantic
correctness is proved from full-profile SPE after that independent certificate.
-/

@[expose] public section

namespace KFOL.Strategic.QuantifiedTree

universe u v
variable {Role : Type u} {Index : Type v}

/-- Every nonempty input list has a genuine binary owned-choice fold. -/
theorem BinaryFold.exists_of_ne_nil (owner : Role) (inputs : Index → Strategic.Tree Role)
    (actions : List Index) (nonempty : actions ≠ []) :
    ∃ binary, BinaryFold owner inputs actions binary := by
  induction actions with
  | nil => exact (nonempty rfl).elim
  | cons first rest ih =>
    cases rest with
    | nil => exact ⟨inputs first, .single first⟩
    | cons second rest =>
      obtain ⟨right, hr⟩ := ih (by simp)
      exact ⟨.node owner (inputs first) right, .node (.single first) hr⟩

/-- A fold is one input, or its outermost helper node has the specified
original owner. This is a syntactic fact independent of all payoffs. -/
theorem BinaryFold.root_or_input {owner : Role} {inputs : Index → Strategic.Tree Role}
    {actions : List Index} {binary : Strategic.Tree Role}
    (fold : BinaryFold owner inputs actions binary) :
    (∃ i ∈ actions, binary = inputs i) ∨
      ∃ left right, binary = Strategic.Tree.node owner left right := by
  cases fold with
  | single i => exact Or.inl ⟨i, List.mem_singleton_self _, rfl⟩
  | node first second => exact Or.inr ⟨_, _, rfl⟩

/-- Absorption depends on the actual enumerated operands, not on a semantic
premise in the compilation relation. -/
theorem BinaryFold.eq_owner_iff {owner : Role} {inputs : Index → Strategic.Tree Role}
    {actions : List Index} {binary : Strategic.Tree Role}
    (fold : BinaryFold owner inputs actions binary) :
    Strategic.value binary = WinnerSet.singleton owner ↔
      ∃ i ∈ actions, Strategic.value (inputs i) = WinnerSet.singleton owner := by
  induction fold with
  | single i => simp only [List.mem_singleton, exists_eq_left]
  | node first second ihfirst ihsecond =>
    rw [Strategic.value_node, WinnerSet.choice_eq_owner_iff, ihfirst, ihsecond]
    simp only [List.mem_append]
    constructor
    · rintro (⟨i, hi, he⟩ | ⟨i, hi, he⟩)
      · exact ⟨i, Or.inl hi, he⟩
      · exact ⟨i, Or.inr hi, he⟩
    · rintro ⟨i, hi | hi, he⟩
      · exact Or.inl ⟨i, hi, he⟩
      · exact Or.inr ⟨i, hi, he⟩

theorem BinaryFold.mem_of_no_owner {owner : Role} {inputs : Index → Strategic.Tree Role}
    {actions : List Index} {binary : Strategic.Tree Role}
    (fold : BinaryFold owner inputs actions binary)
    (hn : ∀ i ∈ actions, Strategic.value (inputs i) ≠ WinnerSet.singleton owner) (winner : Role) :
    winner ∈ Strategic.possibleWinners binary ↔
      ∃ i ∈ actions, winner ∈ Strategic.possibleWinners (inputs i) := by
  induction fold with
  | single i => simp only [List.mem_singleton, exists_eq_left]
  | @node left right first second hf hs ihfirst ihsecond =>
    have hnfirst : Strategic.value first ≠ WinnerSet.singleton owner := by
      rw [ne_eq, hf.eq_owner_iff]
      rintro ⟨i, hi, he⟩
      exact hn i (List.mem_append_left right hi) he
    have hnsecond : Strategic.value second ≠ WinnerSet.singleton owner := by
      rw [ne_eq, hs.eq_owner_iff]
      rintro ⟨i, hi, he⟩
      exact hn i (List.mem_append_right left hi) he
    have hnjoin : ¬(Strategic.value first = WinnerSet.singleton owner ∨
        Strategic.value second = WinnerSet.singleton owner) := not_or.mpr ⟨hnfirst, hnsecond⟩
    change winner ∈ (Strategic.value (.node owner first second)).val ↔ _
    rw [Strategic.value_node]
    simp only [WinnerSet.choice, ite_eq_right hnjoin, WinnerSet.val_union, Set.mem_union]
    change (winner ∈ Strategic.possibleWinners first ∨ winner ∈ Strategic.possibleWinners second) ↔ _
    rw [ihfirst (fun i hi => hn i (List.mem_append_left right hi)),
      ihsecond (fun i hi => hn i (List.mem_append_right left hi))]
    simp only [List.mem_append]
    constructor
    · rintro (⟨i, hi, hw⟩ | ⟨i, hi, hw⟩)
      · exact ⟨i, Or.inl hi, hw⟩
      · exact ⟨i, Or.inr hi, hw⟩
    · rintro ⟨i, hi | hi, hw⟩
      · exact Or.inl ⟨i, hi, hw⟩
      · exact Or.inr ⟨i, hi, hw⟩

open Classical in
theorem BinaryFold.possibleWinners_eq {owner : Role} {inputs : Index → Strategic.Tree Role}
    {actions : List Index} {binary : Strategic.Tree Role}
    (fold : BinaryFold owner inputs actions binary) :
    Strategic.possibleWinners binary =
      if ∃ i ∈ actions, Strategic.value (inputs i) = WinnerSet.singleton owner then {owner}
      else {winner | ∃ i ∈ actions, winner ∈ Strategic.possibleWinners (inputs i)} := by
  classical
  by_cases he : ∃ i ∈ actions, Strategic.value (inputs i) = WinnerSet.singleton owner
  · rw [ite_eq_left he]
    exact congrArg Subtype.val (fold.eq_owner_iff.mpr he)
  · rw [ite_eq_right he]
    ext winner
    exact fold.mem_of_no_owner (fun i hi hv => he ⟨i, hi, hv⟩) winner

/-- Any structural compilation has the same actual full-profile SPE winner
set as its quantified source. No role or action finiteness hypothesis is
needed: finiteness is already certified by the syntax relation itself. -/
theorem Compiles.possibleWinners_eq {source : QuantifiedTree.{u,v} Role}
    {binary : Strategic.Tree Role} (compiled : Compiles source binary) :
    Strategic.possibleWinners binary = possibleWinners source := by
  induction compiled with
  | leaf r => exact Strategic.possibleWinners_leaf r |>.trans (possibleWinners_leaf r).symm
  | @node owner Action nonempty next actions distinct complete children compiled binary fold ih =>
    classical
    rw [fold.possibleWinners_eq, possibleWinners_node]
    have atoms : (∃ a ∈ actions, Strategic.value (children a) = WinnerSet.singleton owner) ↔
        ∃ a, possibleWinners (next a) = {owner} := by
      constructor
      · rintro ⟨a, _, ha⟩
        exact ⟨a, (ih a).symm.trans (congrArg Subtype.val ha)⟩
      · rintro ⟨a, ha⟩
        exact ⟨a, complete a, Subtype.ext ((ih a).trans ha)⟩
    by_cases he : ∃ a, possibleWinners (next a) = {owner}
    · rw [ite_eq_left (atoms.mpr he), ite_eq_left he]
    · rw [ite_eq_right (fun h => he (atoms.mp h)), ite_eq_right he]
      ext winner
      constructor
      · rintro ⟨a, _, hw⟩
        exact ⟨a, (ih a) ▸ hw⟩
      · rintro ⟨a, hw⟩
        exact ⟨a, complete a, (ih a).symm ▸ hw⟩

/-- Every structural finite pruning has an actual recursive owned-choice
fold compilation. Retained children are listed exactly once. -/
theorem Prunes.exists_binary_compilation {bound : ℕ}
    {source pruned : QuantifiedTree.{u,v} Role} (pruning : Prunes bound source pruned) :
    ∃ binary : Strategic.Tree Role, Compiles pruned binary := by
  classical
  induction pruning with
  | leaf r => exact ⟨.leaf r, .leaf r⟩
  | @node owner Action nonempty next support inhabited small retained sub ih =>
    choose children compiled using ih
    let actions : List support := Finset.univ.toList
    have complete (a : support) : a ∈ actions := Finset.mem_toList.mpr (Finset.mem_univ a)
    have nonempty_actions : actions ≠ [] := List.ne_nil_of_mem (complete (Classical.choice inhabited))
    obtain ⟨binary, fold⟩ := BinaryFold.exists_of_ne_nil owner children actions nonempty_actions
    exact ⟨binary, .node actions (Finset.nodup_toList _) complete children compiled fold⟩

end KFOL.Strategic.QuantifiedTree
