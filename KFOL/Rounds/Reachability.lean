module

public import KFOL.Rounds.Tree
public import GameTheory.Protocol.SubgamePerfect

/-! # Every legal public prefix is a proper execution history -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game
open GameTheory.Protocol
universe u
variable {Role : Type u}

/-- A nonempty prefix has a last legal joint tuple, with its actual preceding
prefix. Repeated continuation trees remain different source occurrences. -/
theorem Position.root_or_append {game : Game Role} (p : Position game) :
    p = .root ∨ ∃ (q : Position game) (a : Role → ℕ)
      (hv : ∀ i, a i ≤ q.current.size i) (ha : ¬ q.current.Terminal),
      q.append a hv ha = p := by
  induction p with
  | root => exact Or.inl rfl
  | @down sizes next a tail ih =>
    right
    rcases ih with he | ⟨q,b,hv,ha,he⟩
    · subst tail
      exact ⟨.root,fun i => (a i).val,(fun i => Nat.le_of_lt_succ (a i).isLt),
        (by intro hf; exact hf),by congr 1⟩
    · refine ⟨.down a q,b,hv,ha,?_⟩
      exact congrArg (Position.down a) he

/-- All intrinsic public prefixes are reachable under legal play, with no
assumption about the probability assigned by a particular strategy. -/
theorem reachable_position (game : Game Role) (p : Position game) :
    game.execution.Reachable p := by
  have h : ∀ d : ℕ, ∀ p : Position game, p.depth = d → game.execution.Reachable p := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro p hd
      rcases p.root_or_append with he | ⟨q,a,hv,ha,he⟩
      · subst p
        exact ⟨.start⟩
      · have hdepth : q.depth < d := by
          rw [← hd,← he,Position.depth_append]
          omega
        obtain ⟨trace⟩ := ih q.depth hdepth q rfl
        have legal : game.execution.Legal q (fun i => some (a i)) :=
          ⟨ha,fun i => ⟨ha,hv i⟩⟩
        refine ⟨.extend trace _ legal ?_⟩
        rw [PMF.mem_support_pure_iff]
        simpa only [Option.getD_some] using he.symm
  exact h p.depth p rfl

/-- The complete history carrier and the actual public-prefix carrier agree. -/
def historyEquivPosition (game : Game Role) : game.execution.History ≃ Position game :=
  game.execution.historyEquivReachableState game.tree_shaped |>.trans
    { toFun := Subtype.val
      invFun := fun p => ⟨p,game.reachable_position p⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Full public observation makes every legal prefix an information-set-closed
subgame root, including histories with probability zero under a profile. -/
theorem every_history_subgame_root (game : Game Role) (root : game.execution.History) :
    game.information.IsSubgameRoot root := by
  intro i inside outside hinside _ _ _ _ he
  rw [information_eq_position,information_eq_position] at he
  have hh : inside = outside := (game.historyEquivPosition).injective he
  subst outside
  exact hinside

end KFOL.Rounds.Game
