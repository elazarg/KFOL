module

public import KFOL.Rounds.Scalar.Synthesis
public import KFOL.Rounds.Scalar.BooleanInfinite
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Tactic.DeriveCountable

/-! # Scalar full abstraction for actual possible sequential winners -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game

deriving instance Countable for ScalarTerm

end KFOL.Rounds.Game

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

omit [Fintype Role] in
/-- A comparison uses only Boolean menus whenever its closed rival does. -/
theorem comparisonContext_booleanMenus (owner : Role) {rival : Game Role}
    (hrival : rival.BooleanMenus) : (comparisonContext owner rival).BooleanMenus := by
  constructor
  · intro who
    change (if who = owner then 1 else 0) ≤ 1
    split <;> omega
  · intro actions
    change (if (actions owner).val = 0 then Context.hole else
      closedContext rival).BooleanMenus
    split
    · trivial
    · exact closedContext_booleanMenus hrival

/-- Distinct real-valued singleton laws of arbitrary actual games admit a
one-hole Boolean public comparison. Only the closed rational rival uses the
scalar syntax; the compared games have no syntactic restriction. -/
theorem singleton_scalar_separator (left right : Game Role) (a b c : Role)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (order : ExplicitOrder Role)
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hleft : left.sequentialValues order = {distribution a b x hx0 hx1})
    (hright : right.sequentialValues order = {distribution a b y hy0 hy1})
    (hlt : x < y) :
    ∃ probe : ScalarTerm, probe.UnaryGenerated ∧
      (comparisonContext a (probe.game a c)).BooleanMenus ∧
      c ∈ possibleWinners (((comparisonContext a (probe.game a c)).fill left).sequentialValues order) ∧
      c ∉ possibleWinners (((comparisonContext a (probe.game a c)).fill right).sequentialValues order) := by
  obtain ⟨q,hlq,hqr⟩ := exists_rat_btwn hlt
  have hq0 : (0 : ℚ) < q := by exact_mod_cast lt_of_le_of_lt hx0 hlq
  have hq1 : q < 1 := by exact_mod_cast lt_of_lt_of_le hqr hy1
  obtain ⟨probe,hgenerated,hprobe⟩ := exists_rational_game a c hac q hq0.le hq1.le order
  have hl : (publicChoice a left (probe.game a c)).sequentialValues order =
      {distribution a c (q:ℝ) (by exact_mod_cast hq0.le) (by exact_mod_cast hq1.le)} := by
    apply publicChoice_singletons_of_lt a _ _ order _ _ hleft hprobe
    simpa only [distribution_a a b hab,distribution_a a c hac] using hlq
  have hr : (publicChoice a right (probe.game a c)).sequentialValues order =
      {distribution a b y hy0 hy1} := by
    apply publicChoice_singletons_of_gt a _ _ order _ _ hright hprobe
    simpa only [distribution_a a b hab,distribution_a a c hac] using hqr
  refine ⟨probe,hgenerated,comparisonContext_booleanMenus a (probe.booleanMenus_game a c),?_,?_⟩
  · rw [comparisonContext_fill,hl,possibleWinners_distribution a c hac (q:ℝ)
      (by exact_mod_cast hq0) (by exact_mod_cast hq1)]
    exact Or.inr rfl
  · rw [comparisonContext_fill,hr]
    rintro ⟨law,hlaw,hwho⟩
    have he : law = distribution a b y hy0 hy1 := hlaw
    rw [he] at hwho
    exact hwho (distribution_other a b c hac.symm hbc.symm _ _ _)

/-- Boolean contexts and one third-role support observation recover the exact
real coordinate of arbitrary actual games with singleton two-winner laws. -/
theorem singleton_third_boolean_full_abstraction (left right : Game Role) (a b c : Role)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (order : ExplicitOrder Role)
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hleft : left.sequentialValues order = {distribution a b x hx0 hx1})
    (hright : right.sequentialValues order = {distribution a b y hy0 hy1}) :
    x = y ↔ ∀ context : Context Role, context.BooleanMenus →
      (c ∈ possibleWinners ((context.fill left).sequentialValues order) ↔
        c ∈ possibleWinners ((context.fill right).sequentialValues order)) := by
  constructor
  · intro heq context _
    have hv : left.sequentialValues order = right.sequentialValues order := by
      subst y
      exact hleft.trans hright.symm
    rw [sequentialValues_context_congr context _ _ order hv]
  · intro equivalent
    rcases lt_trichotomy x y with hlt | heq | hgt
    · obtain ⟨probe,_,hc,hl,hr⟩ := singleton_scalar_separator left right a b c hab hac hbc
        order x y hx0 hx1 hy0 hy1 hleft hright hlt
      exact (hr ((equivalent _ hc).mp hl)).elim
    · exact heq
    · obtain ⟨probe,_,hc,hr,hl⟩ := singleton_scalar_separator right left a b c hab hac hbc
        order y x hy0 hy1 hx0 hx1 hright hleft hgt
      exact (hl ((equivalent _ hc).mpr hr)).elim

/-- Full winner-set observations in Boolean contexts are already sufficient. -/
theorem singleton_boolean_full_abstraction (left right : Game Role) (a b c : Role)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (order : ExplicitOrder Role)
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hleft : left.sequentialValues order = {distribution a b x hx0 hx1})
    (hright : right.sequentialValues order = {distribution a b y hy0 hy1}) :
    x = y ↔ ∀ context : Context Role, context.BooleanMenus →
      possibleWinners ((context.fill left).sequentialValues order) =
        possibleWinners ((context.fill right).sequentialValues order) := by
  constructor
  · intro heq context _
    have hv : left.sequentialValues order = right.sequentialValues order := by
      subst y
      exact hleft.trans hright.symm
    rw [sequentialValues_context_congr context _ _ order hv]
  · intro equivalent
    apply (singleton_third_boolean_full_abstraction left right a b c hab hac hbc
      order x y hx0 hx1 hy0 hy1 hleft hright).2
    intro context hc
    rw [equivalent context hc]

/-- A public rival with third-role mass tests the closed upper cut of the
first component's exact real value, including equality at the threshold. -/
theorem third_possible_comparison_iff (left rival : Game Role) (a b c : Role)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (order : ExplicitOrder Role)
    (x z : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hz0 : 0 ≤ z) (hz1 : z < 1)
    (hleft : left.sequentialValues order = {distribution a b x hx0 hx1})
    (hrival : rival.sequentialValues order = {distribution a c z hz0 hz1.le}) :
    c ∈ possibleWinners ((publicChoice a left rival).sequentialValues order) ↔ x ≤ z := by
  have hc : distribution a c z hz0 hz1.le c ≠ 0 := by
    intro he
    have hh := distribution_b a c hac z hz0 hz1.le
    rw [he] at hh
    simp only [ENNReal.toReal_zero] at hh
    linarith
  rcases lt_trichotomy x z with hlt | heq | hgt
  · have hv := publicChoice_singletons_of_lt a left rival order _ _ hleft hrival
      (by simpa only [distribution_a a b hab,distribution_a a c hac] using hlt)
    rw [hv]
    exact ⟨fun _ => hlt.le,fun _ => ⟨_,rfl,hc⟩⟩
  · have hv := possibleWinners_publicChoice_of_eq a left rival order _ _ hleft hrival
      (by simpa only [distribution_a a b hab,distribution_a a c hac] using heq)
    rw [hv]
    exact ⟨fun _ => heq.le,fun _ => Or.inr ⟨_,rfl,hc⟩⟩
  · have hv := publicChoice_singletons_of_gt a left rival order _ _ hleft hrival
      (by simpa only [distribution_a a b hab,distribution_a a c hac] using hgt)
    rw [hv]
    constructor
    · rintro ⟨law,hlaw,hwho⟩
      have he : law = distribution a b x hx0 hx1 := hlaw
      rw [he] at hwho
      exact (hwho (distribution_other a b c hac.symm hbc.symm _ _ _)).elim
    · exact fun h => (not_le_of_gt hgt h).elim

/-- The countable family of Boolean rational public rivals reconstructs the
order of arbitrary singleton two-winner laws. Larger values have fewer
third-role victories against these common rivals. -/
theorem singleton_scalar_le_iff_rational_tests (left right : Game Role) (a b c : Role)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (order : ExplicitOrder Role)
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hleft : left.sequentialValues order = {distribution a b x hx0 hx1})
    (hright : right.sequentialValues order = {distribution a b y hy0 hy1}) :
    x ≤ y ↔ ∀ probe : ScalarTerm, probe.UnaryGenerated → probe.rate < 1 →
      (c ∈ possibleWinners ((publicChoice a right (probe.game a c)).sequentialValues order) →
        c ∈ possibleWinners ((publicChoice a left (probe.game a c)).sequentialValues order)) := by
  constructor
  · intro hxy probe _ hp1
    have hpr : (probe.rate:ℝ) < 1 := by exact_mod_cast hp1
    have hp := sequentialValues_scalarTerm probe a c hac order
    rw [third_possible_comparison_iff right _ a b c hab hac hbc order y (probe.rate:ℝ)
      hy0 hy1 probe.rate_nonneg_real hpr hright hp,
      third_possible_comparison_iff left _ a b c hab hac hbc order x (probe.rate:ℝ)
      hx0 hx1 probe.rate_nonneg_real hpr hleft hp]
    exact le_trans hxy
  · intro tests
    by_contra hxy
    have hyx : y < x := lt_of_not_ge hxy
    obtain ⟨q,hyq,hqx⟩ := exists_rat_btwn hyx
    have hq0 : (0:ℚ) ≤ q := by exact_mod_cast (lt_of_le_of_lt hy0 hyq).le
    have hq1 : q < 1 := by exact_mod_cast lt_of_lt_of_le hqx hx1
    obtain ⟨probe,hgenerated,hvalue⟩ := ScalarTerm.synthesize q hq0 hq1.le
    have hp1 : probe.rate < 1 := by simpa only [hvalue] using hq1
    have hp := sequentialValues_scalarTerm probe a c hac order
    have hpr : (probe.rate:ℝ) < 1 := by exact_mod_cast hp1
    have hrightWin := (third_possible_comparison_iff right _ a b c hab hac hbc order
      y (probe.rate:ℝ) hy0 hy1 probe.rate_nonneg_real hpr hright hp).2
        (by simpa only [hvalue] using hyq.le)
    have hleftBound := (third_possible_comparison_iff left _ a b c hab hac hbc order
      x (probe.rate:ℝ) hx0 hx1 probe.rate_nonneg_real hpr hleft hp).1
        (tests probe hgenerated hp1 hrightWin)
    exact (not_le_of_gt hqx) (by simpa only [hvalue] using hleftBound)

/-- The same countable one-hole probe family reconstructs equality. Arbitrary
Boolean contexts and repeated holes are unnecessary for separation. -/
theorem singleton_scalar_eq_iff_rational_tests (left right : Game Role) (a b c : Role)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (order : ExplicitOrder Role)
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hleft : left.sequentialValues order = {distribution a b x hx0 hx1})
    (hright : right.sequentialValues order = {distribution a b y hy0 hy1}) :
    x = y ↔ ∀ probe : ScalarTerm, probe.UnaryGenerated →
      (c ∈ possibleWinners ((publicChoice a left (probe.game a c)).sequentialValues order) ↔
        c ∈ possibleWinners ((publicChoice a right (probe.game a c)).sequentialValues order)) := by
  constructor
  · intro heq probe _
    have hv : left.sequentialValues order = right.sequentialValues order := by
      subst y
      exact hleft.trans hright.symm
    have hc := sequentialValues_context_congr (comparisonContext a (probe.game a c))
      left right order hv
    simp only [comparisonContext_fill] at hc
    rw [hc]
  · intro tests
    apply le_antisymm
    · apply (singleton_scalar_le_iff_rational_tests left right a b c hab hac hbc order
        x y hx0 hx1 hy0 hy1 hleft hright).2
      exact fun probe hgenerated _ => (tests probe hgenerated).mpr
    · apply (singleton_scalar_le_iff_rational_tests right left a b c hab hac hbc order
        y x hy0 hy1 hx0 hx1 hright hleft).2
      exact fun probe hgenerated _ => (tests probe hgenerated).mp

/-- A rational intermediate value is synthesized as an actual rival component on the
third role. The resulting actual public context distinguishes any two ordered
scalar values by that third role's possible canonical SE victory. -/
theorem scalar_separator (left right : ScalarTerm) (a b c : Role)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (order : ExplicitOrder Role)
    (hlt : left.rate < right.rate) :
    ∃ context : Context Role,
      c ∈ possibleWinners ((context.fill (left.game a b)).sequentialValues order) ∧
      c ∉ possibleWinners ((context.fill (right.game a b)).sequentialValues order) := by
  obtain ⟨probe,_,_,hl,hr⟩ := singleton_scalar_separator
    (left.game a b) (right.game a b) a b c hab hac hbc order
    (left.rate:ℝ) (right.rate:ℝ) left.rate_nonneg_real left.rate_le_one_real
    right.rate_nonneg_real right.rate_le_one_real
    (sequentialValues_scalarTerm left a b hab order)
    (sequentialValues_scalarTerm right a b hab order) (by exact_mod_cast hlt)
  exact ⟨comparisonContext a (probe.game a c),hl,hr⟩

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
    have he := (singleton_third_boolean_full_abstraction (left.game a b) (right.game a b)
      a b c hab hac hbc order (left.rate:ℝ) (right.rate:ℝ)
      left.rate_nonneg_real left.rate_le_one_real right.rate_nonneg_real right.rate_le_one_real
      (sequentialValues_scalarTerm left a b hab order)
      (sequentialValues_scalarTerm right a b hab order)).2 (fun context _ => equivalent context)
    exact_mod_cast he

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
