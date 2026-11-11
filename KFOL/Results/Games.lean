module

public import KFOL.Results.Certificates
public import KFOL.Definitions.PaperGames
public import KFOL.Definitions.PaperAlgebra
public import KFOL.Strategic.Counting

/-! # Mathematical public-game and round statements

Assembly and changes of presentation live here. Paper.lean only states the
claims and names these proofs.
-/

@[expose] public section
noncomputable section
namespace KFOL.Results.Games

open KFOL.Strategic
universe u v
variable {Role : Type u}

theorem public_realizability [Finite Role] (three : Fin 3 ↪ Role) (A : WinnerSet Role) :
    ∃ game : Strategic.Tree Role, Strategic.value game = A :=
  Strategic.exists_value_of_finite three A (Set.toFinite A.val)

theorem public_optimal_realizability [Finite Role] (three : Fin 3 ↪ Role) (A : WinnerSet Role) :
    (∃ G : Strategic.Tree Role, Strategic.value G = A ∧ G.choiceCount = A.val.ncard - 1) ∧
      ∀ G : Strategic.Tree Role, Strategic.value G = A → A.val.ncard - 1 ≤ G.choiceCount :=
  Strategic.optimal_realizability three A

theorem public_sharp_winner_budget [Finite Role] (three : Fin 3 ↪ Role) (n : ℕ) :
    (∀ G : Strategic.Tree Role, G.choiceCount = n →
      (Strategic.value G).val.ncard ≤ min (Nat.card Role) (n + 1)) ∧
    ∃ G : Strategic.Tree Role, G.choiceCount = n ∧
      (Strategic.value G).val.ncard = min (Nat.card Role) (n + 1) :=
  Strategic.sharp_budget three n

theorem public_sharp_absorbing_budget [Finite Role] (three : Fin 3 ↪ Role)
    (n h : ℕ) (hn : h ≤ n) :
    (∀ G : Strategic.Tree Role, G.choiceCount = n → G.absorbingCount = h →
      (Strategic.value G).val.ncard ≤ min (Nat.card Role) (n + 1 - h)) ∧
    ∃ G : Strategic.Tree Role, G.choiceCount = n ∧ G.absorbingCount = h ∧
      (Strategic.value G).val.ncard = min (Nat.card Role) (n + 1 - h) :=
  Strategic.sharp_absorbing_budget three n h hn

open Rounds.Game
variable [Fintype Role] [DecidableEq Role]

theorem value_eq_serial (game : Rounds.Game Role)
    (order : GameTheory.Languages.Bridges.FOSGToEFG.ExplicitOrder Role) :
    game.value = game.sequentialValues order :=
  (game.sequentialValues_eq_observedValues (playerOrder Role)).trans
    (game.sequentialValues_eq_observedValues order).symm

theorem round_recursion :
    (∀ game : Rounds.Game Role, game.value = game.observedValues) ∧
    (∀ r : Role, (Rounds.Game.leaf r).value = {PMF.pure r}) ∧
    (∀ (sizes : Role → ℕ) (next : ((i : Role) → Fin (sizes i+1)) → Rounds.Game Role),
      (Rounds.Game.round sizes next).value = roundOperator sizes (fun a => (next a).value)) :=
  ⟨fun game => game.sequentialValues_eq_observedValues (playerOrder Role),
    fun r => sequentialValues_leaf r (playerOrder Role),
    fun sizes next => sequentialValues_round sizes next (playerOrder Role)⟩

theorem public_mixed_support (tree : Strategic.Tree Role) :
    possibleWinners (publicTree tree).value = (Strategic.value tree).val :=
  possibleWinners_publicTree tree (playerOrder Role)

theorem public_nonidempotence (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    midpointLaw (PMF.pure a) (PMF.pure c) ∉ (Public.nonconvexTree a b c).value ∧
    midpointLaw (PMF.pure a) (PMF.pure c) ∈
      (publicChoice b (Public.nonconvexTree a b c) (Public.nonconvexTree a b c)).value :=
  ⟨Public.midpoint_not_mem_example a b c hab hac hbc (playerOrder Role),
    Public.midpoint_mem_repeated_example a b c hab hac hbc (playerOrder Role)⟩

theorem constant_sum_value (a b : Role) (hab : a ≠ b) (game : Rounds.Game Role)
    (uses : game.UsesOnly a b) : ∃ x : ℝ, game.HasScalarValue a b x := by
  obtain ⟨x,h0,h1,hvalue⟩ := TwoPlayers.sequentialValues_scalar a b hab game uses (playerOrder Role)
  exact ⟨x,h0,h1,hvalue⟩

theorem diagonal_value (a b : Role) (hab : a ≠ b) (left right : Rounds.Game Role) (x y : ℝ)
    (hx : left.HasScalarValue a b x) (hy : right.HasScalarValue a b y) :
    (diagonal a b left right).HasScalarValue a b (Scalar.parallel x y) := by
  obtain ⟨hx0,hx1,hleft⟩ := hx
  obtain ⟨hy0,hy1,hright⟩ := hy
  exact ⟨Scalar.parallel_nonneg x y hx0 hy0,Scalar.parallel_le_one x y hx0 hx1 hy0,
    Scalar.sequentialValues_diagonal a b hab left right x y hx0 hx1 hy0 hy1
      (playerOrder Role) hleft hright⟩

theorem reciprocal_values (a b : Role) (hab : a ≠ b) (n : ℕ) :
    (reciprocal a b n).HasScalarValue a b (1/((n:ℝ)+1)) := by
  refine ⟨by positivity,?_,Scalar.sequentialValues_reciprocal a b hab n (playerOrder Role)⟩
  apply (div_le_one (by positivity : (0:ℝ) < (n:ℝ)+1)).2
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem scalar_full_abstraction (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (left right : ScalarTerm) :
    (left.rate = right.rate ↔ SameContextualWinners (left.game a b) (right.game a b)) ∧
    (left.rate = right.rate ↔ ContextuallyEquivalent c (left.game a b) (right.game a b)) :=
  ⟨Scalar.scalar_full_abstraction left right a b c hab hac hbc (playerOrder Role),
    Scalar.scalar_third_full_abstraction left right a b c hab hac hbc (playerOrder Role)⟩

theorem no_finite_summary (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {Carrier : Type v} [Finite Carrier] : ¬Nonempty (WinnerSummary a c Carrier) := by
  rintro ⟨summary⟩
  apply Scalar.no_finite_boolean_winner_algebra a b c hab hac hbc (playerOrder Role) summary.encode
  · intro left right rival same
    have hl := summary.composition left rival
      ⟨publicChoice a left.val rival.val,left.property.publicChoice rival.property⟩ rfl
    have hr := summary.composition right rival
      ⟨publicChoice a right.val rival.val,right.property.publicChoice rival.property⟩ rfl
    exact hl.trans ((congrArg (fun x => summary.choose x (summary.encode rival)) same).trans hr.symm)
  · intro left right same
    exact (summary.adequacy left).symm.trans (same ▸ summary.adequacy right)

theorem infinite_winner_algebra (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (∀ n m : ℕ, possibleWinners (threshold a b c n m).value =
      if n < m then {a,b} else if n = m then {a,b,c} else {a,c}) ∧
    (∀ n m : ℕ, (threshold a b c n m).BooleanMenus) ∧
    (∀ (Carrier : Type v) [Finite Carrier], ¬Nonempty (WinnerSummary a c Carrier)) :=
  ⟨fun n m => Scalar.possibleWinners_threshold a b c hab hac n m (playerOrder Role),
    booleanMenus_threshold a b c,fun _ _ => no_finite_summary a b c hab hac hbc⟩

omit [Fintype Role] [DecidableEq Role] in
theorem two_player_degeneracies (labels : Fin 2 ≃ Role) :
    (∀ A B : WinnerSet Role, A.reset B = B) ∧
    (∀ (r : Role) (X Y Z : WinnerSet Role), WinnerSet.guardedChoice r X Y Z = X) ∧
    (∀ {Var : Type v} (t : Term Role Var), t.AtomPreserving) ∧
    (¬∃ t : Term Role (Fin 2), ∀ x : Fin 2 → WinnerSet Role, t.eval x = (x 0).union (x 1)) ∧
    (∃ t : Term Role (Fin 2), t.Idempotent ∧ ¬∃ s : Term Role (Fin 2), s.IsCore ∧ s.Equivalent t) :=
  ⟨KFOL.TwoPlayers.reset_projection labels,KFOL.TwoPlayers.guardedChoice_projection labels,
    fun {Var} (term : Term Role Var) => KFOL.TwoPlayers.atom_preserving labels term,KFOL.TwoPlayers.union_not_definable labels,
    KFOL.TwoPlayers.idempotent_not_core labels⟩

omit [Fintype Role] [DecidableEq Role] in
theorem two_player_basis (labels : Fin 2 ≃ Role) :
    letI := KFOL.TwoPlayers.Kleene.winnerStructure labels
    KFOL.TwoPlayers.Kleene.basis.Finite ∧
      Equational.IsBasis (WinnerSet Role) KFOL.TwoPlayers.Kleene.basis :=
  ⟨KFOL.TwoPlayers.Kleene.basis_finite,KFOL.TwoPlayers.Kleene.basis_winner labels⟩

theorem two_player_round_support (sizes : Fin 2 → ℕ)
    (next : ((i : Fin 2) → Fin (sizes i+1)) → Rounds.Game (Fin 2)) :
    ∃ g : ((i : Fin 2) → Fin (sizes i+1)) → WinnerSet (Fin 2),
      (∀ a, (g a).val = possibleWinners (next a).value) ∧
      possibleWinners (Rounds.Game.round sizes next).value =
        ((TwoPlayers.serialZero sizes g).union (TwoPlayers.serialOne sizes g)).val := by
  obtain ⟨g,hg,folded,_⟩ := KFOL.Results.two_player_round_support sizes next (playerOrder (Fin 2))
  exact ⟨g,hg,folded⟩

theorem two_player_round_contexts :
    (∀ (left right : Rounds.Game (Fin 2)), possibleWinners left.value = possibleWinners right.value →
      SameContextualWinners left right) ∧
    possibleWinners (diagonal (0 : Fin 2) 1 (.leaf 0) (.leaf 0)).value = {0,1} :=
  KFOL.Results.two_player_round_contexts (playerOrder (Fin 2))

omit [Fintype Role] [DecidableEq Role] in
theorem well_founded_quantifier_fold [Fintype Role] [Nontrivial Role]
    (game : Strategic.QuantifiedTree.{u,v} Role) :
    ∃ (pruned : Strategic.QuantifiedTree.{u,v} Role) (binary : Strategic.Tree Role)
      (pruning : Strategic.QuantifiedTree.Prunes (Fintype.card Role-1) game pruned),
      pruning.PreservesValues ∧ (∃ depth, Strategic.QuantifiedTree.DepthLE depth pruned) ∧
      Strategic.QuantifiedTree.Compiles pruned binary ∧
      Strategic.possibleWinners binary = Strategic.QuantifiedTree.possibleWinners game := by
  obtain ⟨pruned,binary,pruning,preserved,compiled,represented⟩ :=
    Strategic.QuantifiedTree.exists_value_preserving_pruning_binary_fold game
  exact ⟨pruned,binary,pruning,preserved,pruning.exists_depthLE,compiled,
    represented.trans preserved.possibleWinners_eq⟩

omit [Fintype Role] [DecidableEq Role] in
theorem finite_depth_quantifier_fold [Fintype Role] [Nontrivial Role]
    (depth : ℕ) (game : Strategic.QuantifiedTree.{u,v} Role)
    (bounded : Strategic.QuantifiedTree.DepthLE depth game) :
    (∃ plan : Strategic.QuantifiedTree.Profile game, Strategic.QuantifiedTree.IsSubgamePerfect plan) ∧
    ∃ (pruned : Strategic.QuantifiedTree.{u,v} Role) (binary : Strategic.Tree Role)
      (pruning : Strategic.QuantifiedTree.Prunes (Fintype.card Role-1) game pruned),
      pruning.PreservesValues ∧ Strategic.QuantifiedTree.DepthLE depth pruned ∧
      Strategic.QuantifiedTree.Compiles pruned binary ∧
      Strategic.possibleWinners binary = Strategic.QuantifiedTree.possibleWinners game := by
  obtain ⟨pruned,binary,pruning,preserved,bounded',compiled,represented⟩ :=
    Strategic.QuantifiedTree.exists_value_preserving_pruning_binary_fold_of_depthLE game depth bounded
  exact ⟨Strategic.QuantifiedTree.exists_spe game,pruned,binary,pruning,preserved,bounded',compiled,
    represented.trans preserved.possibleWinners_eq⟩

theorem reset_circuit_large_tables (n : ℕ) :
    ∃ (circuit : Circuit.Equation Reset.Symbol (Bool ⊕ (ℕ × Bool)))
      (term : Reset.Term (Bool ⊕ (ℕ × Bool))),
      circuit.WellFormed ∧ circuit.gates.length = 6*n+3 ∧
      circuit.unfold = some (term,term) ∧ 2^n ≤ (term.table (.inl true)).card := by
  obtain ⟨circuit,term,wellformed,size,_,_,unfolded,large⟩ := KFOL.Results.reset_circuit_exponential_tables n
  exact ⟨circuit,term,wellformed,size,unfolded,large⟩

end KFOL.Results.Games
