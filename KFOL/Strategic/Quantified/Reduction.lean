module

public import KFOL.Strategic.Quantified.Basic
public import KFOL.Strategic.Quantified.Fold
public import KFOL.Strategic.ChoiceSupport

/-! # Finite structural pruning and binary representation of nested quantifiers

Supports are selected from the actual original child equilibrium values.
Every retained child is independently pruned, preserving its equilibrium
observation. A uniform finite depth is preserved when supplied, but is not a
premise for the structural induction on the original well-founded tree.
-/

@[expose] public section
namespace KFOL.Strategic.QuantifiedTree

universe u v
variable {Role : Type u}

/-- Increasing a decision-depth bound preserves it. -/
theorem DepthLE.mono {lower upper : ℕ} {game : QuantifiedTree.{u,v} Role}
    (bounded : DepthLE lower game) (le : lower ≤ upper) : DepthLE upper game := by
  induction game generalizing lower upper with
  | leaf => cases upper <;> trivial
  | node owner Action nonempty next ih =>
    cases lower with
    | zero => exact bounded.elim
    | succ lower =>
      cases upper with
      | zero => omega
      | succ upper => exact fun a => ih a (bounded a) (by omega)

/-- Structural pruning never increases a supplied decision-depth bound. -/
theorem Prunes.depthLE {bound depth : ℕ} {source pruned : QuantifiedTree.{u,v} Role}
    (pruning : Prunes bound source pruned) (bounded : DepthLE depth source) :
    DepthLE depth pruned := by
  induction pruning generalizing depth with
  | leaf => trivial
  | @node owner Action nonempty next support inhabited small children sub ih =>
    cases depth with
    | zero => exact bounded.elim
    | succ depth => exact fun a => ih a (bounded a.val)

/-- Finite branching in a structural pruning also gives a finite uniform
depth, even when the original well-founded tree has no such bound. -/
theorem Prunes.exists_depthLE {bound : ℕ} {source pruned : QuantifiedTree.{u,v} Role}
    (pruning : Prunes bound source pruned) : ∃ depth : ℕ, DepthLE depth pruned := by
  classical
  induction pruning with
  | leaf => exact ⟨0,trivial⟩
  | @node owner Action nonempty next support inhabited small children sub ih =>
    choose levels bounded using ih
    refine ⟨Finset.univ.sup levels + 1,fun a => ?_⟩
    exact (bounded a).mono (Finset.le_sup (Finset.mem_univ a))

/-- The arbitrary-action root rule transports along equality of the actual
continuation equilibrium observations, without a finiteness premise. -/
theorem possibleWinners_node_eq_finiteChoice (owner : Role) (Action : Type v)
    (nonempty : Nonempty Action) (next : Action → QuantifiedTree.{u,v} Role)
    (branches : Action → Strategic.Tree Role)
    (same : ∀ a, possibleWinners (next a) = Strategic.possibleWinners (branches a)) :
    possibleWinners (.node owner Action nonempty next) = FiniteChoice.possibleWinners owner branches := by
  classical
  rw [possibleWinners_node,FiniteChoice.possibleWinners_eq]
  have atoms : (∃ a, possibleWinners (next a) = {owner}) ↔
      ∃ a, Strategic.value (branches a) = WinnerSet.singleton owner := by
    constructor
    · rintro ⟨a,ha⟩
      exact ⟨a,Subtype.ext ((same a).symm.trans ha)⟩
    · rintro ⟨a,ha⟩
      exact ⟨a,(same a).trans (congrArg Subtype.val ha)⟩
  rw [propext atoms]
  congr 1
  ext player
  exact exists_congr (fun a => by rw [same a])

/-- The nodewise preservation property includes the root observation. -/
theorem Prunes.PreservesValues.possibleWinners_eq {bound : ℕ}
    {source pruned : QuantifiedTree.{u,v} Role} {pruning : Prunes bound source pruned}
    (preserved : pruning.PreservesValues) : possibleWinners pruned = possibleWinners source := by
  cases preserved with
  | leaf => rfl
  | node root _ => exact root

variable [Fintype Role] [Nontrivial Role]

/-- An entire well-founded quantified game, of arbitrary branching and
without a uniform finite depth assumption, has a structural pruning to at
most K-1 original actions per retained node and the same SPE winners. Its
observation is also realized by a finite binary public game. -/
theorem exists_value_preserving_pruning_binary (game : QuantifiedTree.{u,v} Role) :
    ∃ (pruned : QuantifiedTree.{u,v} Role) (binary : Strategic.Tree Role)
      (pruning : Prunes (Fintype.card Role-1) game pruned),
      pruning.PreservesValues ∧ Strategic.possibleWinners binary = possibleWinners pruned := by
  classical
  induction game with
  | leaf r =>
    refine ⟨.leaf r,.leaf r,.leaf r,.leaf r,?_⟩
    rw [possibleWinners_leaf]
    exact congrArg Subtype.val (Strategic.value_leaf r)
  | node owner Action nonempty next ih =>
    let _ : Nonempty Action := nonempty
    choose cut binary pruning preserved binary_preserved using ih
    obtain ⟨support,nonempty_support,small,fold_original⟩ := WinnerSet.exists_small_choice_support owner
      (fun a => value (next a))
    let inhabited : Nonempty support := ⟨⟨nonempty_support.choose,nonempty_support.choose_spec⟩⟩
    let retained : support → QuantifiedTree.{u,v} Role := fun a => cut a.val
    let pruned : QuantifiedTree.{u,v} Role := .node owner support inhabited retained
    have hprunes : Prunes (Fintype.card Role-1) (.node owner Action nonempty next) pruned :=
      Prunes.node support inhabited small retained (fun a => pruning a.val)
    have values : (fun a => Strategic.value (binary a)) = (fun a => value (next a)) := by
      funext a
      exact Subtype.ext ((binary_preserved a).trans (preserved a).possibleWinners_eq)
    have folded := FiniteChoice.possibleWinners_restrict_eq_fold owner binary support nonempty_support
    rw [values,fold_original] at folded
    have original :
        (if ∃ a, value (next a) = WinnerSet.singleton owner then {owner}
          else {player | ∃ a, player ∈ (value (next a)).val}) =
        possibleWinners (.node owner Action nonempty next) := by
      rw [possibleWinners_node]
      have atoms : (∃ a, value (next a) = WinnerSet.singleton owner) ↔
          ∃ a, possibleWinners (next a) = {owner} := by
        constructor
        · rintro ⟨a,ha⟩
          exact ⟨a,congrArg Subtype.val ha⟩
        · rintro ⟨a,ha⟩
          exact ⟨a,Subtype.ext ha⟩
      rw [propext atoms]
      rfl
    have pruned_to_binary := possibleWinners_node_eq_finiteChoice owner support inhabited retained
      (fun a => binary a.val) (fun a => (binary_preserved a.val).symm)
    have observed : possibleWinners pruned = possibleWinners (.node owner Action nonempty next) :=
      pruned_to_binary.trans (folded.trans original)
    let _ : Nonempty support := inhabited
    obtain ⟨result,realizes⟩ := FiniteChoice.exists_binary_tree owner (fun a : support => binary a.val)
    exact ⟨pruned,result,hprunes,.node (small := small) observed (fun a => preserved a.val),
      realizes.trans pruned_to_binary.symm⟩

/-- Root-observation-facing corollary of the stronger nodewise pruning. -/
theorem exists_small_pruning_binary (game : QuantifiedTree.{u,v} Role) :
    ∃ (pruned : QuantifiedTree.{u,v} Role) (binary : Strategic.Tree Role),
      Prunes (Fintype.card Role-1) game pruned ∧
      possibleWinners pruned = possibleWinners game ∧
      Strategic.possibleWinners binary = possibleWinners pruned := by
  obtain ⟨pruned,binary,pruning,preserved,represented⟩ := exists_value_preserving_pruning_binary game
  exact ⟨pruned,binary,pruning,preserved.possibleWinners_eq,represented⟩

/-- Nodewise preservation and an inherited finite-depth bound together. -/
theorem exists_value_preserving_pruning_binary_of_depthLE
    (game : QuantifiedTree.{u,v} Role) (depth : ℕ) (bounded : DepthLE depth game) :
    ∃ (pruned : QuantifiedTree.{u,v} Role) (binary : Strategic.Tree Role)
      (pruning : Prunes (Fintype.card Role-1) game pruned),
      pruning.PreservesValues ∧ DepthLE depth pruned ∧
      Strategic.possibleWinners binary = possibleWinners pruned := by
  obtain ⟨pruned,binary,pruning,preserved,represented⟩ := exists_value_preserving_pruning_binary game
  exact ⟨pruned,binary,pruning,preserved,pruning.depthLE bounded,represented⟩

/-- Finite-depth-facing version: branching is bounded structurally at every
retained decision and the original decision-depth bound is preserved. -/
theorem exists_small_pruning_binary_of_depthLE (game : QuantifiedTree.{u,v} Role) (depth : ℕ)
    (bounded : DepthLE depth game) :
    ∃ (pruned : QuantifiedTree.{u,v} Role) (binary : Strategic.Tree Role),
      Prunes (Fintype.card Role-1) game pruned ∧ DepthLE depth pruned ∧
      possibleWinners pruned = possibleWinners game ∧
      Strategic.possibleWinners binary = possibleWinners pruned := by
  obtain ⟨pruned,binary,pruning,preserved,represented⟩ := exists_small_pruning_binary game
  exact ⟨pruned,binary,pruning,pruning.depthLE bounded,preserved,represented⟩


/-- Strong syntactic realization: the binary game is an actual recursive
owned-choice fold of the retained children, each used exactly once. -/
theorem exists_value_preserving_pruning_binary_fold (game : QuantifiedTree.{u,v} Role) :
    ∃ (pruned : QuantifiedTree.{u,v} Role) (binary : Strategic.Tree Role)
      (pruning : Prunes (Fintype.card Role-1) game pruned),
      pruning.PreservesValues ∧ Compiles pruned binary ∧
      Strategic.possibleWinners binary = possibleWinners pruned := by
  obtain ⟨pruned, _, pruning, preserved, _⟩ := exists_value_preserving_pruning_binary game
  obtain ⟨binary, compiled⟩ := pruning.exists_binary_compilation
  exact ⟨pruned, binary, pruning, preserved, compiled, compiled.possibleWinners_eq⟩

/-- The structural owned-choice fold compilation and nodewise preservation
inherit a supplied decision-depth bound for the pruned quantified tree. -/
theorem exists_value_preserving_pruning_binary_fold_of_depthLE
    (game : QuantifiedTree.{u,v} Role) (depth : ℕ) (bounded : DepthLE depth game) :
    ∃ (pruned : QuantifiedTree.{u,v} Role) (binary : Strategic.Tree Role)
      (pruning : Prunes (Fintype.card Role-1) game pruned),
      pruning.PreservesValues ∧ DepthLE depth pruned ∧ Compiles pruned binary ∧
      Strategic.possibleWinners binary = possibleWinners pruned := by
  obtain ⟨pruned, binary, pruning, preserved, compiled, represented⟩ :=
    exists_value_preserving_pruning_binary_fold game
  exact ⟨pruned, binary, pruning, preserved, pruning.depthLE bounded, compiled, represented⟩

end KFOL.Strategic.QuantifiedTree
