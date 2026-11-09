module

public import KFOL.Rounds.Scalar.Distribution
public import KFOL.Rounds.Observed.Existence

/-! # Unique winner laws in finite stages with two effective players -/
@[expose] public section
noncomputable section
namespace KFOL.Rounds.Game.TwoPlayers
open GameTheory GameTheory.Math.Probability
universe u
variable {Role : Type u} [DecidableEq Role] [Fintype Role]

omit [DecidableEq Role] in
/-- A stage law inherits the continuation support, without any positive-reach
or pure-strategy restriction on the independent mixed menu laws. -/
theorem stage_support (a b : Role) (sizes : Role → Nat)
    (p : ((i : Role) → Fin (sizes i+1)) → PMF Role)
    (support : ∀ actions who, who ≠ a → who ≠ b → p actions who = 0)
    (profile : (i : Role) → PMF (Fin (sizes i+1)))
    (who : Role) (ha : who ≠ a) (hb : who ≠ b) :
    ((independentProduct profile).bind p) who = 0 := by
  simp only [PMF.bind_apply,support _ who ha hb,mul_zero,tsum_zero]

omit [DecidableEq Role] [Fintype Role] in
/-- In a two-winner law, increasing one coordinate decreases the other. -/
theorem coordinate_sum (a b : Role) (hab : a ≠ b) (law : PMF Role)
    (support : ∀ who, who ≠ a → who ≠ b → law who = 0) :
    (law a).toReal + (law b).toReal = 1 := by
  rw [← ENNReal.toReal_add (law.apply_ne_top _) (law.apply_ne_top _),
    Scalar.pair_mass_add a b hab law support]
  norm_num

omit [Fintype Role] in
/-- Crossed profiles agree literally when every other role has its unique
legal action. Thus arbitrary ambient roles add no strategic degrees of freedom. -/
theorem profile_cross (a b : Role) (hab : a ≠ b) (sizes : Role → Nat)
    (inactive : ∀ i, i ≠ a → i ≠ b → sizes i = 0)
    (first second : (i : Role) → PMF (Fin (sizes i+1))) :
    Profile.update (sig := {Strategy := fun i => PMF (Fin (sizes i+1)),Outcome := Role}) first b (second b) =
      Profile.update (sig := {Strategy := fun i => PMF (Fin (sizes i+1)),Outcome := Role}) second a (first a) := by
  funext i
  by_cases ha : i = a
  · subst i
    simp [hab]
  by_cases hb : i = b
  · subst i
    simp [Ne.symm hab]
  · rw [Profile.update_of_ne _ _ hb,Profile.update_of_ne _ _ ha]
    let : Subsingleton (Fin (sizes i+1)) := ⟨fun x y => Fin.ext (by
      have hx := x.isLt
      have hy := y.isLt
      have hz := inactive i ha hb
      omega)⟩
    exact (eq_pure_of_subsingleton (first i) 0).trans
      (eq_pure_of_subsingleton (second i) 0).symm

/-- All mixed Nash equilibria of a fixed stage give the same actual winner
law whenever the only effective players and winners are the designated pair. -/
theorem nash_winner_law_unique (a b : Role) (hab : a ≠ b) (sizes : Role → Nat)
    (inactive : ∀ i, i ≠ a → i ≠ b → sizes i = 0)
    (p : ((i : Role) → Fin (sizes i+1)) → PMF Role)
    (support : ∀ actions who, who ≠ a → who ≠ b → p actions who = 0)
    (first second : (i : Role) → PMF (Fin (sizes i+1)))
    (hfirst : IsNash (stageForm sizes p).mixed
      (euPreference (fun winner i => winnerPayoff id i winner)) first)
    (hsecond : IsNash (stageForm sizes p).mixed
      (euPreference (fun winner i => winnerPayoff id i winner)) second) :
    (independentProduct first).bind p = (independentProduct second).bind p := by
  have optimalFirst := (Observed.stage_nash_iff sizes p first).mp hfirst
  have optimalSecond := (Observed.stage_nash_iff sizes p second).mp hsecond
  have crossFirst := coordinate_sum a b hab
    ((independentProduct (Profile.update (sig := {Strategy := fun i => PMF (Fin (sizes i+1)),Outcome := Role}) first b (second b))).bind p)
    (stage_support a b sizes p support _)
  have crossSecond := coordinate_sum a b hab
    ((independentProduct (Profile.update (sig := {Strategy := fun i => PMF (Fin (sizes i+1)),Outcome := Role}) second b (first b))).bind p)
    (stage_support a b sizes p support _)
  have sumFirst := coordinate_sum a b hab ((independentProduct first).bind p) (stage_support a b sizes p support first)
  have sumSecond := coordinate_sum a b hab ((independentProduct second).bind p) (stage_support a b sizes p support second)
  have f_b := optimalFirst b (second b)
  have s_b := optimalSecond b (first b)
  have f_a := optimalFirst a (second a)
  have s_a := optimalSecond a (first a)
  rw [← profile_cross a b hab sizes inactive first second] at s_a
  rw [← profile_cross a b hab sizes inactive second first] at f_a
  have ha : (((independentProduct first).bind p) a).toReal =
      (((independentProduct second).bind p) a).toReal := by linarith
  have hf := Scalar.eq_distribution a b hab ((independentProduct first).bind p)
    (stage_support a b sizes p support first)
  have hs := Scalar.eq_distribution a b hab ((independentProduct second).bind p)
    (stage_support a b sizes p support second)
  rw [hf,hs]
  simp only [ha]

end KFOL.Rounds.Game.TwoPlayers
