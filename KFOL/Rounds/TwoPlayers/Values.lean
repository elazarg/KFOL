module

public import KFOL.Rounds.TwoPlayers.Stage
public import KFOL.Rounds.Correspondence

/-! # Constant-sum uniqueness for every finite game using a designated pair -/
@[expose] public section
noncomputable section
namespace KFOL.Rounds.Game.TwoPlayers
open GameTheory GameTheory.Math.Probability
open GameTheory.Languages.Bridges.FOSGToEFG
universe u
variable {Role : Type u} [DecidableEq Role] [Fintype Role]

/-- Every finite game whose only effective players and winners are a fixed
pair has one complete equilibrium winner distribution. -/
theorem observedValues_singleton (a b : Role) (hab : a ≠ b) (game : Game Role) :
    game.UsesOnly a b → ∃ law : PMF Role,
      (∀ who, who ≠ a → who ≠ b → law who = 0) ∧ game.observedValues = {law} := by
  induction game with
  | leaf r =>
    intro uses
    rcases uses with rfl | rfl
    · exact ⟨PMF.pure r,(by intro who ha _; simp [ha]),Observed.observedValues_leaf r⟩
    · exact ⟨PMF.pure r,(by intro who _ hb; simp [hb]),Observed.observedValues_leaf r⟩
  | round sizes next ih =>
    rintro ⟨inactive,uses⟩
    choose p support childValues using fun actions => ih actions (uses actions)
    obtain ⟨profile,nash⟩ := Observed.stage_exists_nash sizes p
    refine ⟨(independentProduct profile).bind p,stage_support a b sizes p support profile,?_⟩
    rw [Observed.observedValues_round]
    have he : (fun actions => (next actions).observedValues) = fun actions => {p actions} :=
      funext childValues
    rw [he]
    apply Set.Subset.antisymm
    · rintro value ⟨q,hq,other,otherNash,hvalue⟩
      have heq : q = p := funext fun actions => hq actions
      subst q
      exact hvalue.trans (nash_winner_law_unique a b hab sizes inactive p support
        other profile otherNash nash)
    · intro value hv
      obtain rfl := hv
      exact ⟨p,(fun _ => rfl),profile,nash,rfl⟩

/-- The singleton law is an actual two-winner probability distribution; this
is the constant-sum scalar interface for arbitrary finite actual menus. -/
theorem sequentialValues_scalar (a b : Role) (hab : a ≠ b) (game : Game Role)
    (uses : game.UsesOnly a b) (order : ExplicitOrder Role) :
    ∃ (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1),
      game.sequentialValues order = {Scalar.distribution a b x h0 h1} := by
  obtain ⟨law,support,values⟩ := observedValues_singleton a b hab game uses
  refine ⟨(law a).toReal,ENNReal.toReal_nonneg,pmf_toReal_apply_le_one law a,?_⟩
  rw [sequentialValues_eq_observedValues,values]
  exact congrArg (fun p : PMF Role => ({p} : Set (PMF Role)))
    (Scalar.eq_distribution a b hab law support)

/-- With exactly two roles every actual game satisfies the pair restriction;
no special two-player syntax or padded action convention is needed. -/
theorem finTwo_usesOnly (game : Game (Fin 2)) : game.UsesOnly 0 1 := by
  induction game with
  | leaf r => fin_cases r <;> simp [UsesOnly]
  | round sizes next ih =>
    refine ⟨?_,ih⟩
    intro i h0 h1
    fin_cases i <;> contradiction

end KFOL.Rounds.Game.TwoPlayers
