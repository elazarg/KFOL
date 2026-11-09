module

public import KFOL.Rounds.Scalar.Infinite

/-! # Actual round contexts and the infinite possible-winner observation index -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game.Scalar

open GameTheory GameTheory.Math.Probability
open GameTheory.Languages.Bridges.FOSGToEFG

universe u v
variable {Role : Type u}

/-- Embed a closed game into the already defined hole context syntax. -/
def closedContext : Game Role → Context Role
  | .leaf who => .leaf who
  | .round sizes next => .round sizes (fun actions => closedContext (next actions))

@[simp] theorem closedContext_fill (game input : Game Role) :
    (closedContext game).fill input = game := by
  induction game with
  | leaf who => rfl
  | round sizes next ih =>
    simp only [closedContext,Context.fill]
    congr 1
    funext actions
    exact ih actions

variable [DecidableEq Role] [Fintype Role]

/-- Equality of the independently defined canonical SE value sets is preserved
by every actual finite round context, including independent repeated holes. -/
theorem sequentialValues_context_congr (context : Context Role) (left right : Game Role)
    (order : ExplicitOrder Role) (heq : left.sequentialValues order = right.sequentialValues order) :
    (context.fill left).sequentialValues order = (context.fill right).sequentialValues order := by
  induction context with
  | hole => exact heq
  | leaf who => rfl
  | round sizes next ih =>
    simp only [Context.fill,sequentialValues_round]
    congr 1
    funext actions
    exact ih actions

/-- The actual threshold context has one hole and a completely closed rival. -/
def thresholdContext (a c : Role) (m : ℕ) : Context Role :=
  .round (fun i => if i = a then 1 else 0) fun actions =>
    if (actions a).val = 0 then .hole else closedContext (reciprocal a c (m+1))

omit [Fintype Role] in
@[simp] theorem thresholdContext_fill (a b c : Role) (n m : ℕ) :
    (thresholdContext a c m).fill (reciprocal a b (n+1)) = threshold a b c n m := by
  unfold thresholdContext threshold publicChoice
  simp only [Context.fill]
  congr 1
  funext actions
  split <;> simp only [Context.fill,closedContext_fill]

/-- No finite carrier can be both compositional for the paper's actual public
threshold contexts and adequate for the third role's possible SE victory.
This conclusion uses actual game constructors and the proved canonical SE
threshold theorem; adequacy is not an unconnected arithmetic probe premise. -/
theorem no_finite_winner_algebra (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (order : ExplicitOrder Role) {Summary : Type v} [Finite Summary]
    (encode : Game Role → Summary)
    (choice_congr : ∀ (left right rival : Game Role), encode left = encode right →
      encode (publicChoice a left rival) = encode (publicChoice a right rival))
    (adequate : ∀ (left right : Game Role), encode left = encode right →
      (c ∈ possibleWinners (left.sequentialValues order) ↔
        c ∈ possibleWinners (right.sequentialValues order))) : False := by
  let code : ℕ → Summary := fun n => encode (reciprocal a b (n+1))
  have hinj : Function.Injective code := by
    intro n k he
    have threshold_eq (m : ℕ) : m ≤ n ↔ m ≤ k := by
      have he' := choice_congr (reciprocal a b (n+1)) (reciprocal a b (k+1))
        (reciprocal a c (m+1)) he
      have ho := adequate _ _ he'
      exact (third_possible_threshold_iff a b c hab hac hbc n m order).symm.trans
        (ho.trans (third_possible_threshold_iff a b c hab hac hbc k m order))
    exact le_antisymm ((threshold_eq n).mp le_rfl) ((threshold_eq k).mpr le_rfl)
  exact Finite.false (Finite.of_injective code hinj)

/-- The contextual formulation makes every two distinct reciprocal inputs
observationally different in the actual three-role language. -/
theorem no_finite_contextual_summary (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (order : ExplicitOrder Role) {Summary : Type v} [Finite Summary]
    (encode : Game Role → Summary)
    (adequate : ∀ (left right : Game Role), encode left = encode right → ∀ context : Context Role,
      (c ∈ possibleWinners ((context.fill left).sequentialValues order) ↔
        c ∈ possibleWinners ((context.fill right).sequentialValues order))) : False := by
  let code : ℕ → Summary := fun n => encode (reciprocal a b (n+1))
  have hinj : Function.Injective code := by
    intro n k he
    have threshold_eq (m : ℕ) : m ≤ n ↔ m ≤ k := by
      have ho := adequate _ _ he (thresholdContext a c m)
      simp only [thresholdContext_fill] at ho
      exact (third_possible_threshold_iff a b c hab hac hbc n m order).symm.trans
        (ho.trans (third_possible_threshold_iff a b c hab hac hbc k m order))
    exact le_antisymm ((threshold_eq n).mp le_rfl) ((threshold_eq k).mpr le_rfl)
  exact Finite.false (Finite.of_injective code hinj)

end KFOL.Rounds.Game.Scalar
