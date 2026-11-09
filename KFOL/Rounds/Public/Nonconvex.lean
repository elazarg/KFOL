module

public import KFOL.Rounds.Public.Support

/-! # Exact public nonconvexity and distribution-level nonidempotence -/
@[expose] public section
noncomputable section
namespace KFOL.Rounds.Game.Public
open GameTheory.Math.Probability
open GameTheory.Languages.Bridges.FOSGToEFG
universe u
variable {Role : Type u} [DecidableEq Role] [Fintype Role]

omit [DecidableEq Role] [Fintype Role] in
theorem left_mem_segment (p q : PMF Role) : p ∈ segment p q :=
  ⟨1,by norm_num,le_rfl,(mix_one p q).symm⟩

omit [DecidableEq Role] [Fintype Role] in
theorem right_mem_segment (p q : PMF Role) : q ∈ segment p q :=
  ⟨0,le_rfl,by norm_num,(mix_zero p q).symm⟩

/-- An owner absent from both leaf winners is indifferent at every mixing
weight, and these are all the equilibrium distributions. -/
theorem leaf_choice_values (owner a b : Role) (ha : a ≠ owner) (hb : b ≠ owner)
    (order : ExplicitOrder Role) :
    (publicChoice owner (.leaf a) (.leaf b)).sequentialValues order =
      segment (PMF.pure a) (PMF.pure b) := by
  ext value
  rw [sequentialValues_publicChoice_iff]
  constructor
  · rintro ⟨p,hp,q,hq,α,h0,h1,_prefer0,_prefer1,he⟩
    rw [sequentialValues_leaf,Set.mem_singleton_iff] at hp hq
    exact ⟨α,h0,h1,by simpa only [hp,hq] using he⟩
  · rintro ⟨α,h0,h1,he⟩
    refine ⟨PMF.pure a,by rw [sequentialValues_leaf]; rfl,
      PMF.pure b,by rw [sequentialValues_leaf]; rfl,α,h0,h1,?_,?_,he⟩ <;>
      simp [Ne.symm ha,Ne.symm hb]

/-- Exact union of two segments for the paper's public example. -/
theorem example_values (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (order : ExplicitOrder Role) :
    (nonconvexTree a b c).sequentialValues order =
      segment (PMF.pure a) (PMF.pure b) ∪ segment (PMF.pure b) (PMF.pure c) := by
  ext value
  change value ∈ (publicChoice a (publicChoice c (.leaf a) (.leaf b)) (.leaf c)).sequentialValues order ↔ _
  rw [sequentialValues_publicChoice_iff]
  have inner := leaf_choice_values c a b hac hbc order
  constructor
  · rintro ⟨p,hp,q,hq,α,h0,h1,_prefer0,prefer1,hvalue⟩
    rw [sequentialValues_leaf,Set.mem_singleton_iff] at hq
    subst q
    rw [inner] at hp
    obtain ⟨x,hx0,hx1,hp⟩ := hp
    by_cases hx : x = 0
    · right
      have he : p = PMF.pure b := by simpa only [hx,mix_zero] using hp
      exact ⟨α,h0,h1,by simpa only [he] using hvalue⟩
    · left
      have hpcoord : (p a).toReal = x := by
        rw [hp,mix_apply_toReal]
        simp [hab]
      have hα : α = 1 := by
        by_contra hne
        have hlt := lt_of_le_of_ne h1 hne
        have hle := prefer1 hlt
        have hz : ((PMF.pure c) a).toReal = 0 := by simp [hac]
        rw [hpcoord,hz] at hle
        exact hx (le_antisymm hle hx0)
      have he : value = p := by simpa only [hα,mix_one] using hvalue
      exact ⟨x,hx0,hx1,he.trans hp⟩
  · intro hv
    rcases hv with ⟨x,hx0,hx1,hvalue⟩ | ⟨α,h0,h1,hvalue⟩
    · let p := mix x hx0 hx1 (PMF.pure a) (PMF.pure b)
      refine ⟨p,?_,PMF.pure c,by rw [sequentialValues_leaf]; rfl,1,by norm_num,le_rfl,?_,?_,?_⟩
      · rw [inner]
        exact ⟨x,hx0,hx1,rfl⟩
      · intro _
        simp only [PMF.pure_apply,hac,ite_false,ENNReal.toReal_zero]
        exact ENNReal.toReal_nonneg
      · norm_num
      · simpa only [mix_one] using hvalue
    · refine ⟨PMF.pure b,?_,PMF.pure c,by rw [sequentialValues_leaf]; rfl,α,h0,h1,?_,?_,hvalue⟩
      · rw [inner]
        exact right_mem_segment _ _
      · simp [hab,hac]
      · simp [hab,hac]

/-- The midpoint omitted by the example's two-segment value set. -/
theorem midpoint_not_mem_example (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (order : ExplicitOrder Role) :
    mix (1/2 : ℝ) (by norm_num) (by norm_num) (PMF.pure a) (PMF.pure c) ∉
      (nonconvexTree a b c).sequentialValues order := by
  rw [example_values a b c hab hac hbc]
  rintro (⟨α,h0,h1,he⟩ | ⟨α,h0,h1,he⟩)
  · have hc := congrArg (fun law : PMF Role => (law c).toReal) he
    simp only [mix_apply_toReal,PMF.pure_apply] at hc
    norm_num [Ne.symm hac,Ne.symm hbc] at hc
  · have ha := congrArg (fun law : PMF Role => (law a).toReal) he
    simp only [mix_apply_toReal,PMF.pure_apply] at ha
    norm_num [hab,hac] at ha

/-- Independent continuation equilibria in the two equal copies let the
indifferent root mix their `a` and `c` Dirac laws. -/
theorem midpoint_mem_repeated_example (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (order : ExplicitOrder Role) :
    mix (1/2 : ℝ) (by norm_num) (by norm_num) (PMF.pure a) (PMF.pure c) ∈
      (publicChoice b (nonconvexTree a b c) (nonconvexTree a b c)).sequentialValues order := by
  apply (sequentialValues_publicChoice_iff b _ _ order _).mpr
  refine ⟨PMF.pure a,?_,PMF.pure c,?_,1/2,by norm_num,by norm_num,?_,?_,rfl⟩
  · rw [example_values a b c hab hac hbc]
    exact Or.inl (left_mem_segment _ _)
  · rw [example_values a b c hab hac hbc]
    exact Or.inr (right_mem_segment _ _)
  · simp [Ne.symm hab,hbc]
  · simp [Ne.symm hab,hbc]

end KFOL.Rounds.Game.Public
