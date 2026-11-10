module
public import KFOL.Rounds.Scalar.Nash
/-! # Explicit security mixtures in the actual diagonal commitment stage

Each displayed law is on the designated player's actual two-action menu.
Replacing only that role's current law fixes the winner probability against
every independent law of its opponent; no equilibrium hypothesis is used.
-/
@[expose] public section
noncomputable section
namespace KFOL.Rounds.Game.Scalar
open GameTheory GameTheory.Math.Probability
universe u
variable {Role : Type u} [DecidableEq Role] [Fintype Role]

/-- A literal mixture of indices zero and one of an actual designated menu. -/
def menuMixture (a b who : Role) (hwho : who = a ∨ who = b)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : PMF (Fin (binarySizes a b who+1)) :=
  mix q hq0 hq1 (PMF.pure 0) (PMF.pure (oneAction a b who hwho))

omit [Fintype Role] in
theorem zeroProbability_update_mixture (a b who : Role) (hwho : who = a ∨ who = b)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (profile : (i : Role) → PMF (Fin (binarySizes a b i+1))) :
    zeroProbability (Profile.update
      (sig := {Strategy := fun i => PMF (Fin (binarySizes a b i+1)),Outcome := Role})
      profile who (menuMixture a b who hwho q hq0 hq1)) who = q := by
  simp only [zeroProbability,Profile.update_same,menuMixture,mix_map,PMF.pure_map]
  rw [mix_apply_toReal]
  simp [zeroBit,oneAction]

/-- Both actual security laws put y/(x+y) on menu zero and fix a's actual
winner probability at the parallel sum against every opposing mixed law. -/
theorem diagonal_security (a b : Role) (hab : a ≠ b) (x y : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hs : 0 < x+y) :
    ∃ (row : PMF (Fin (binarySizes a b a+1)))
      (col : PMF (Fin (binarySizes a b b+1))),
      (row 0).toReal = y/(x+y) ∧
      (col 0).toReal = y/(x+y) ∧
      ∀ profile : (i : Role) → PMF (Fin (binarySizes a b i+1)),
        ((stageForm (binarySizes a b) (diagonalTable a b
          (distribution a b x hx0 hx1) (distribution a b y hy0 hy1))).mixed.play
            (Profile.update (sig := {Strategy := fun i => PMF (Fin (binarySizes a b i+1)),Outcome := Role})
              profile a row) a).toReal = x*y/(x+y) ∧
        ((stageForm (binarySizes a b) (diagonalTable a b
          (distribution a b x hx0 hx1) (distribution a b y hy0 hy1))).mixed.play
            (Profile.update (sig := {Strategy := fun i => PMF (Fin (binarySizes a b i+1)),Outcome := Role})
              profile b col) a).toReal = x*y/(x+y) := by
  have hq0 : 0 ≤ y/(x+y) := div_nonneg hy0 hs.le
  have hq1 : y/(x+y) ≤ 1 := (div_le_one hs).mpr (by linarith)
  let row := menuMixture a b a (Or.inl rfl) (y/(x+y)) hq0 hq1
  let col := menuMixture a b b (Or.inr rfl) (y/(x+y)) hq0 hq1
  have hrow (profile : (i : Role) → PMF (Fin (binarySizes a b i+1))) :
      zeroProbability (Profile.update
        (sig := {Strategy := fun i => PMF (Fin (binarySizes a b i+1)),Outcome := Role})
        profile a row) a = y/(x+y) := zeroProbability_update_mixture a b a _ _ _ _ profile
  have hcol (profile : (i : Role) → PMF (Fin (binarySizes a b i+1))) :
      zeroProbability (Profile.update
        (sig := {Strategy := fun i => PMF (Fin (binarySizes a b i+1)),Outcome := Role})
        profile b col) b = y/(x+y) := zeroProbability_update_mixture a b b _ _ _ _ profile
  refine ⟨row,col,?_,?_,?_⟩
  · change (menuMixture a b a (Or.inl rfl) (y/(x+y)) hq0 hq1 0).toReal = _
    rw [menuMixture,mix_apply_toReal]
    simp [oneAction]
  · change (menuMixture a b b (Or.inr rfl) (y/(x+y)) hq0 hq1 0).toReal = _
    rw [menuMixture,mix_apply_toReal]
    simp [oneAction]
  · intro profile
    constructor
    · rw [diagonal_stage_coordinate a b hab x y hx0 hx1 hy0 hy1,hrow,
        zeroProbability_update_other a b a b hab.symm]
      field_simp
      ring
    · rw [diagonal_stage_coordinate a b hab x y hx0 hx1 hy0 hy1,hcol,
        zeroProbability_update_other a b b a hab]
      field_simp
      ring
end KFOL.Rounds.Game.Scalar
