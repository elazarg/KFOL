module

public import GameTheory.Analysis.Protocol.AssessmentCompactness
public import GameTheory.Analysis.Protocol.BehavioralBayes
public import GameTheory.Analysis.Protocol.Sequential
public import GameTheory.Math.Probability.FiniteUniform
public import GameTheory.Protocol.FiniteInformation

/-! # Consistent beliefs for arbitrary finite-protocol behavioral strategies -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds
open GameTheory.Protocol GameTheory.Math.Probability Filter
universe uι us ua up uq uk

/-- Every behavioral profile of a finite protocol admits Kreps-Wilson
consistent beliefs. Uniform trembles approximate the supplied strategy; only
the beliefs require a compactness subsequence. No optimality is assumed. -/
theorem exists_consistent_assessment {Role : Type uι} [Countable Role]
    {E : ExecutionProtocol.{uι,us,ua} Role} [E.FiniteMovers] [Finite E.History]
    (M : InformationModel.{uι,us,ua,up,uq,uk} E)
    (antichain : M.DecisionInformationAntichain)
    (strategy : (i : Role) → M.BehavioralPolicy i) :
    ∃ assessment : M.BehavioralAssessment,
      assessment.strategy = strategy ∧ assessment.IsSequentiallyConsistent antichain := by
  classical
  let weight (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)
  have hpositive (n : ℕ) : 0 < weight n := by
    exact one_div_pos.mpr (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) (by norm_num))
  have hone (n : ℕ) : weight n ≤ 1 := by
    apply (div_le_one (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) (by norm_num))).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hzero : Tendsto weight atTop (nhds 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
    convert h using 1
    funext n
    simp [weight,Nat.cast_add]
    ring
  let tremble (n : ℕ) (i : Role) : M.BehavioralPolicy i := fun info =>
    if hi : M.IsDecisionInfo i info then
      let site : M.InformationSite i := ⟨info,hi⟩
      letI : Finite (M.Choice i info) := InformationModel.InformationSite.finite_choice (M := M) i site
      letI : Nonempty (M.Choice i info) := InformationModel.InformationSite.nonempty_choice (M := M) site
      mix (weight n) (hpositive n).le (hone n)
        (@uniformLaw _ (Fintype.ofFinite (M.Choice i site.val)) inferInstance) (strategy i info)
    else strategy i info
  have hfull (n : ℕ) (i : Role) (site : M.InformationSite i) (choice : M.Choice i site.val) :
      choice ∈ (tremble n i site.val).support := by
    dsimp only [tremble]
    rw [dite_eq_left site.property]
    exact mem_support_mix_left _ _ _ (hpositive n)
      (@mem_support_uniformLaw _ (Fintype.ofFinite (M.Choice i site.val)) inferInstance choice)
  let sequence (n : ℕ) := M.bayesAssessment (tremble n) (hfull n) antichain
  have hstrategy (i : Role) (site : M.InformationSite i) :
      PMFConvergesPointwise (fun n => (sequence n).strategy i site.val) (strategy i site.val) := by
    change PMFConvergesPointwise (fun n => tremble n i site.val) _
    dsimp only [tremble]
    simp only [dite_eq_left site.property]
    exact pmfConvergesPointwise_mix_zero weight (fun n => (hpositive n).le) hone hzero _ _
  obtain ⟨limit,subsequence,hsub,hlimit⟩ :=
    M.exists_subseq_behavioralAssessmentConvergesPointwise_atSites_of_uniformlyTight sequence
      (fun _ _ => uniformlyTight_of_finite _) (fun _ _ => uniformlyTight_of_finite _)
  let assessment : M.BehavioralAssessment := ⟨strategy,limit.belief⟩
  refine ⟨assessment,rfl,fun n => sequence (subsequence n),?_,?_⟩
  · intro n
    exact ⟨hfull _,M.bayesAssessment_isBayesConsistent _ _ antichain⟩
  · constructor
    · intro i site
      exact (hstrategy i site).subseq hsub
    · intro i site
      exact hlimit.belief i site

end KFOL.Rounds
