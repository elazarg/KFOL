module

public import KFOL.Rounds.Public.Menus

/-! # Exact public-choice mixed Nash inequalities -/
@[expose] public section
noncomputable section
namespace KFOL.Rounds.Game.Public
open GameTheory GameTheory.Math.Probability
universe u
variable {Role : Type u} [DecidableEq Role] [Fintype Role]

def weight (owner : Role) (profile : (i : Role) → PMF (Fin (sizes owner i+1))) : ℝ :=
  (((profile owner).map (menuBit owner)) 0).toReal

omit [Fintype Role] in
theorem weight_nonneg (owner : Role) (profile : (i : Role) → PMF (Fin (sizes owner i+1))) :
    0 ≤ weight owner profile := ENNReal.toReal_nonneg

omit [Fintype Role] in
theorem weight_le_one (owner : Role) (profile : (i : Role) → PMF (Fin (sizes owner i+1))) :
    weight owner profile ≤ 1 := pmf_toReal_apply_le_one _ _

/-- Only the active owner's two actual pure replacements need checking;
other roles cannot change any actual action tuple coordinate. -/
theorem stage_nash_iff_endpoints (owner : Role)
    (p : ((i : Role) → Fin (sizes owner i+1)) → PMF Role)
    (profile : (i : Role) → PMF (Fin (sizes owner i+1))) :
    IsNash (stageForm (sizes owner) p).mixed
      (euPreference (fun winner i => winnerPayoff id i winner)) profile ↔
    ((p (action owner 0)) owner).toReal ≤ (((stageForm (sizes owner) p).mixed.play profile) owner).toReal ∧
    ((p (action owner 1)) owner).toReal ≤ (((stageForm (sizes owner) p).mixed.play profile) owner).toReal := by
  rw [Observed.stage_nash_iff]
  change (∀ who alternative,
    (((stageForm (sizes owner) p).mixed.play (Profile.update (sig := {Strategy := fun i => PMF (Fin (sizes owner i+1)), Outcome := Role}) profile who alternative)) who).toReal ≤
      (((stageForm (sizes owner) p).mixed.play profile) who).toReal) ↔ _
  have playLaw (μ : (i : Role) → PMF (Fin (sizes owner i+1))) :
      (independentProduct μ).bind p =
        mix (weight owner μ) (weight_nonneg owner μ) (weight_le_one owner μ)
          (p (action owner 0)) (p (action owner 1)) := stage_law owner p μ
  change (∀ who alternative,
    (((independentProduct (Profile.update (sig := {Strategy := fun i => PMF (Fin (sizes owner i+1)), Outcome := Role}) profile who alternative)).bind p) who).toReal ≤
      (((independentProduct profile).bind p) who).toReal) ↔
    ((p (action owner 0)) owner).toReal ≤ (((independentProduct profile).bind p) owner).toReal ∧
    ((p (action owner 1)) owner).toReal ≤ (((independentProduct profile).bind p) owner).toReal
  have pureLaw (b : Fin 2) :
      (independentProduct
        (Profile.update (sig := {Strategy := fun i => PMF (Fin (sizes owner i+1)), Outcome := Role}) profile owner (PMF.pure (menuChoice owner b)))).bind p = p (action owner b) := by
    rw [playLaw]
    simp only [weight,Profile.update_same,PMF.pure_map,menuBit_choice]
    fin_cases b <;> simp
  constructor
  · intro optimal
    exact ⟨by simpa only [pureLaw] using optimal owner (PMF.pure (menuChoice owner 0)),
      by simpa only [pureLaw] using optimal owner (PMF.pure (menuChoice owner 1))⟩
  · rintro ⟨h0,h1⟩ who alternative
    by_cases he : who = owner
    · subst who
      rw [playLaw,mix_apply_toReal]
      have hβ0 := weight_nonneg owner (Profile.update (sig := {Strategy := fun i => PMF (Fin (sizes owner i+1)), Outcome := Role}) profile owner alternative)
      have hβ1 := weight_le_one owner (Profile.update (sig := {Strategy := fun i => PMF (Fin (sizes owner i+1)), Outcome := Role}) profile owner alternative)
      change weight owner (Profile.update (sig := {Strategy := fun i => PMF (Fin (sizes owner i+1)), Outcome := Role}) profile owner alternative) * _ +
        (1 - weight owner (Profile.update (sig := {Strategy := fun i => PMF (Fin (sizes owner i+1)), Outcome := Role}) profile owner alternative)) * _ ≤ _
      nlinarith [mul_nonneg hβ0 (sub_nonneg.mpr h0),
        mul_nonneg (sub_nonneg.mpr hβ1) (sub_nonneg.mpr h1)]
    · have same : (Profile.update (sig := {Strategy := fun i => PMF (Fin (sizes owner i+1)), Outcome := Role}) profile who alternative) owner = profile owner :=
        Profile.update_of_ne _ _ (Ne.symm he)
      rw [playLaw,playLaw]
      simp only [weight,same]
      exact le_rfl

/-- The owner's mixing conditions use the continuation coordinates, with
weak inequalities at pure endpoints and equality whenever both are used. -/
theorem stage_nash_iff (owner : Role)
    (p : ((i : Role) → Fin (sizes owner i+1)) → PMF Role)
    (profile : (i : Role) → PMF (Fin (sizes owner i+1))) :
    IsNash (stageForm (sizes owner) p).mixed
      (euPreference (fun winner i => winnerPayoff id i winner)) profile ↔
    (0 < weight owner profile → ((p (action owner 1)) owner).toReal ≤ ((p (action owner 0)) owner).toReal) ∧
    (weight owner profile < 1 → ((p (action owner 0)) owner).toReal ≤ ((p (action owner 1)) owner).toReal) := by
  rw [stage_nash_iff_endpoints]
  change (_ ≤ (((independentProduct profile).bind p) owner).toReal) ∧
    (_ ≤ (((independentProduct profile).bind p) owner).toReal) ↔ _
  have playLaw : (independentProduct profile).bind p =
      mix (weight owner profile) (weight_nonneg owner profile) (weight_le_one owner profile)
        (p (action owner 0)) (p (action owner 1)) := stage_law owner p profile
  rw [playLaw,mix_apply_toReal]
  change (_ ≤ weight owner profile * _ + (1-weight owner profile) * _) ∧
    (_ ≤ weight owner profile * _ + (1-weight owner profile) * _) ↔ _
  have h0 := weight_nonneg owner profile
  have h1 := weight_le_one owner profile
  constructor
  · rintro ⟨hx,hy⟩
    constructor
    · intro hpos
      nlinarith
    · intro hlt
      nlinarith
  · rintro ⟨hp,hq⟩
    by_cases ha : weight owner profile = 0
    · simp only [ha,zero_mul,sub_zero,one_mul,zero_add]
      exact ⟨hq (by linarith),le_rfl⟩
    by_cases hb : weight owner profile = 1
    · simp only [hb,one_mul,sub_self,zero_mul,add_zero]
      exact ⟨le_rfl,hp (by linarith)⟩
    · have he := le_antisymm (hp (lt_of_le_of_ne h0 (Ne.symm ha)))
        (hq (lt_of_le_of_ne h1 hb))
      rw [he]
      constructor <;> linarith

/-- A chosen mixing weight is realized by independent laws on the exact
menus; every other role uses its unique legal action. -/
def profile (owner : Role) (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    (i : Role) → PMF (Fin (sizes owner i+1)) :=
  fun i => (mix α h0 h1 (PMF.pure (action owner 0 i)) (PMF.pure (action owner 1 i)))

omit [Fintype Role] in
@[simp] theorem weight_profile (owner : Role) (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    weight owner (profile owner α h0 h1) = α := by
  rw [weight,profile,mix_map]
  simp [action,menuBit,h0]

end KFOL.Rounds.Game.Public
