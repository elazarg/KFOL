module
public import KFOL.Rounds.Scalar.Contexts
public import KFOL.Rounds.Scalar.Fragment
/-! # Infinite winner observation already on the Boolean-menu fragment

The encoding domain and the available contexts are restricted syntactically.
No extension of a Boolean-fragment semantics to other games is assumed.
-/
@[expose] public section
noncomputable section
namespace KFOL.Rounds.Game
open GameTheory.Languages.Bridges.FOSGToEFG
universe u v
variable {Role : Type u}

theorem Context.BooleanMenus.fill {context : Context Role} (hc : context.BooleanMenus)
    {game : Game Role} (hg : game.BooleanMenus) : (context.fill game).BooleanMenus := by
  induction context with
  | hole => exact hg
  | leaf who => trivial
  | round sizes next ih => exact ⟨hc.1,fun actions => ih actions (hc.2 actions)⟩

theorem Scalar.closedContext_booleanMenus {game : Game Role} (hg : game.BooleanMenus) :
    (Scalar.closedContext game).BooleanMenus := by
  induction game with
  | leaf who => trivial
  | round sizes next ih => exact ⟨hg.1,fun actions => ih actions (hg.2 actions)⟩

variable [DecidableEq Role]
theorem Scalar.thresholdContext_booleanMenus (a c : Role) (m : ℕ) :
    (Scalar.thresholdContext a c m).BooleanMenus := by
  constructor
  · intro who
    change (if who = a then 1 else 0) ≤ 1
    split <;> omega
  · intro actions
    change (if (actions a).val = 0 then Context.hole else
      Scalar.closedContext (reciprocal a c (m+1))).BooleanMenus
    split
    · trivial
    · exact Scalar.closedContext_booleanMenus (booleanMenus_reciprocal a c (m+1))

variable [Fintype Role]

/-- A semantics defined ONLY on the actual Boolean-menu fragment cannot have
finite carrier, even when compositionality is required only for public choice
and adequacy observes only one designated third role. -/
theorem Scalar.no_finite_boolean_winner_algebra
    (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (order : ExplicitOrder Role) {Summary : Type v} [Finite Summary]
    (encode : {game : Game Role // game.BooleanMenus} → Summary)
    (choice_congr : ∀ (left right rival : {game : Game Role // game.BooleanMenus}),
      encode left = encode right →
      encode ⟨publicChoice a left.val rival.val,left.property.publicChoice rival.property⟩ =
        encode ⟨publicChoice a right.val rival.val,right.property.publicChoice rival.property⟩)
    (adequate : ∀ (left right : {game : Game Role // game.BooleanMenus}),
      encode left = encode right →
      (c ∈ possibleWinners (left.val.sequentialValues order) ↔
        c ∈ possibleWinners (right.val.sequentialValues order))) : False := by
  let code : ℕ → Summary := fun n => encode
    ⟨reciprocal a b (n+1),booleanMenus_reciprocal a b (n+1)⟩
  have hinj : Function.Injective code := by
    intro n k he
    have threshold_eq (m : ℕ) : m ≤ n ↔ m ≤ k := by
      have he' := choice_congr
        ⟨reciprocal a b (n+1),booleanMenus_reciprocal a b (n+1)⟩
        ⟨reciprocal a b (k+1),booleanMenus_reciprocal a b (k+1)⟩
        ⟨reciprocal a c (m+1),booleanMenus_reciprocal a c (m+1)⟩ he
      have ho := adequate _ _ he'
      change c ∈ possibleWinners ((threshold a b c n m).sequentialValues order) ↔
        c ∈ possibleWinners ((threshold a b c k m).sequentialValues order) at ho
      exact (Scalar.third_possible_threshold_iff a b c hab hac hbc n m order).symm.trans
        (ho.trans (Scalar.third_possible_threshold_iff a b c hab hac hbc k m order))
    exact le_antisymm ((threshold_eq n).mp le_rfl) ((threshold_eq k).mpr le_rfl)
  exact Finite.false (Finite.of_injective code hinj)

/-- The corresponding contextual impossibility also quantifies only over
Boolean games and Boolean contexts. Filling a hole is certified by syntax. -/
theorem Scalar.no_finite_boolean_contextual_summary
    (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (order : ExplicitOrder Role) {Summary : Type v} [Finite Summary]
    (encode : {game : Game Role // game.BooleanMenus} → Summary)
    (adequate : ∀ (left right : {game : Game Role // game.BooleanMenus}),
      encode left = encode right → ∀ context : Context Role, context.BooleanMenus →
      (c ∈ possibleWinners ((context.fill left.val).sequentialValues order) ↔
        c ∈ possibleWinners ((context.fill right.val).sequentialValues order))) : False := by
  let code : ℕ → Summary := fun n => encode
    ⟨reciprocal a b (n+1),booleanMenus_reciprocal a b (n+1)⟩
  have hinj : Function.Injective code := by
    intro n k he
    have threshold_eq (m : ℕ) : m ≤ n ↔ m ≤ k := by
      have ho := adequate
        ⟨reciprocal a b (n+1),booleanMenus_reciprocal a b (n+1)⟩
        ⟨reciprocal a b (k+1),booleanMenus_reciprocal a b (k+1)⟩ he
        (Scalar.thresholdContext a c m) (Scalar.thresholdContext_booleanMenus a c m)
      simp only [Scalar.thresholdContext_fill] at ho
      exact (Scalar.third_possible_threshold_iff a b c hab hac hbc n m order).symm.trans
        (ho.trans (Scalar.third_possible_threshold_iff a b c hab hac hbc k m order))
    exact le_antisymm ((threshold_eq n).mp le_rfl) ((threshold_eq k).mpr le_rfl)
  exact Finite.false (Finite.of_injective code hinj)
end KFOL.Rounds.Game
