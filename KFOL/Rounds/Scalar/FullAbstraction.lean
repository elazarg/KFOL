module

public import KFOL.Rounds.Scalar.Synthesis
public import KFOL.Rounds.Scalar.Contexts

/-! # Scalar full abstraction for actual possible sequential winners -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game.Scalar

open GameTheory GameTheory.Math.Probability
open GameTheory.Languages.Bridges.FOSGToEFG

universe u
variable {Role : Type u} [DecidableEq Role]

/-- A literal public comparison context with one independently instantiated
hole and a closed rival; no contextual-equivalence condition is built in. -/
def comparisonContext (owner : Role) (rival : Game Role) : Context Role :=
  .round (fun i => if i = owner then 1 else 0) fun actions =>
    if (actions owner).val = 0 then .hole else closedContext rival

@[simp] theorem comparisonContext_fill (owner : Role) (rival input : Game Role) :
    (comparisonContext owner rival).fill input = publicChoice owner input rival := by
  unfold comparisonContext publicChoice
  simp only [Context.fill]
  congr 1
  funext actions
  split <;> simp only [Context.fill,closedContext_fill]

variable [Fintype Role]

/-- A rational midpoint is synthesized as an actual rival component on the
third role. The resulting actual public context distinguishes any two ordered
scalar values by that third role's possible canonical SE victory. -/
theorem scalar_separator (left right : ScalarTerm) (a b c : Role)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (order : ExplicitOrder Role)
    (hlt : left.rate < right.rate) :
    ∃ context : Context Role,
      c ∈ possibleWinners ((context.fill (left.game a b)).sequentialValues order) ∧
      c ∉ possibleWinners ((context.fill (right.game a b)).sequentialValues order) := by
  let q : ℚ := (left.rate+right.rate)/2
  have hlq : left.rate < q := by dsimp [q]; linarith
  have hqr : q < right.rate := by dsimp [q]; linarith
  have hq0 : 0 < q := lt_of_le_of_lt (ScalarTerm.rate_valid left).1 hlq
  have hq1 : q < 1 := lt_of_lt_of_le hqr (ScalarTerm.rate_valid right).2
  obtain ⟨probe,_,hprobe⟩ := exists_rational_game a c hac q hq0.le hq1.le order
  let rival := probe.game a c
  have hleft : (publicChoice a (left.game a b) rival).sequentialValues order =
      {distribution a c (q:ℝ) (by exact_mod_cast hq0.le) (by exact_mod_cast hq1.le)} := by
    apply publicChoice_singletons_of_lt a _ _ order _ _
      (sequentialValues_scalarTerm left a b hab order) hprobe
    simp only [distribution_a a b hab,distribution_a a c hac]
    exact_mod_cast hlq
  have hright : (publicChoice a (right.game a b) rival).sequentialValues order =
      {distribution a b (right.rate:ℝ) right.rate_nonneg_real right.rate_le_one_real} := by
    apply publicChoice_singletons_of_gt a _ _ order _ _
      (sequentialValues_scalarTerm right a b hab order) hprobe
    simp only [distribution_a a b hab,distribution_a a c hac]
    exact_mod_cast hqr
  refine ⟨comparisonContext a rival,?_,?_⟩
  · rw [comparisonContext_fill,hleft]
    have he := possibleWinners_distribution a c hac (q:ℝ)
      (by exact_mod_cast hq0) (by exact_mod_cast hq1)
    rw [he]
    exact Or.inr rfl
  · rw [comparisonContext_fill,hright]
    rintro ⟨law,hlaw,hwho⟩
    have he : law = distribution a b (right.rate:ℝ) right.rate_nonneg_real right.rate_le_one_real := hlaw
    rw [he] at hwho
    exact hwho (distribution_other a b c hac.symm hbc.symm _ _ _)

/-- The third role's possible victory alone is fully abstract for scalar
values, quantified over every actual finite round context, repeated holes
included. The scalar semantics is the actual canonical serial-SE value set. -/
theorem scalar_third_full_abstraction (left right : ScalarTerm) (a b c : Role)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (order : ExplicitOrder Role) :
    left.rate = right.rate ↔ ∀ context : Context Role,
      (c ∈ possibleWinners ((context.fill (left.game a b)).sequentialValues order) ↔
        c ∈ possibleWinners ((context.fill (right.game a b)).sequentialValues order)) := by
  constructor
  · intro heq context
    have hv : (left.game a b).sequentialValues order = (right.game a b).sequentialValues order := by
      rw [sequentialValues_scalarTerm left a b hab,sequentialValues_scalarTerm right a b hab]
      simp only [heq]
    rw [sequentialValues_context_congr context _ _ order hv]
  · intro equivalent
    rcases lt_trichotomy left.rate right.rate with hlt | heq | hgt
    · obtain ⟨context,hl,hr⟩ := scalar_separator left right a b c hab hac hbc order hlt
      exact (hr ((equivalent context).mp hl)).elim
    · exact heq
    · obtain ⟨context,hr,hl⟩ := scalar_separator right left a b c hab hac hbc order hgt
      exact (hl ((equivalent context).mpr hr)).elim

/-- Complete scalar full abstraction for possible winners in the three-role
round language; the stronger single-observer statement is above. -/
theorem scalar_full_abstraction (left right : ScalarTerm) (a b c : Role)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (order : ExplicitOrder Role) :
    left.rate = right.rate ↔ ∀ context : Context Role,
      possibleWinners ((context.fill (left.game a b)).sequentialValues order) =
        possibleWinners ((context.fill (right.game a b)).sequentialValues order) := by
  constructor
  · intro heq context
    have hv : (left.game a b).sequentialValues order = (right.game a b).sequentialValues order := by
      rw [sequentialValues_scalarTerm left a b hab,sequentialValues_scalarTerm right a b hab]
      simp only [heq]
    rw [sequentialValues_context_congr context _ _ order hv]
  · intro equivalent
    apply (scalar_third_full_abstraction left right a b c hab hac hbc order).2
    intro context
    rw [equivalent context]

end KFOL.Rounds.Game.Scalar
