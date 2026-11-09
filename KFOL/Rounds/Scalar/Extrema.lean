module

public import KFOL.Rounds.Scalar.Threshold

/-! # Public scalar choice denotes the actual maximum or minimum law -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game.Scalar

open GameTheory GameTheory.Math.Probability
open GameTheory.Languages.Bridges.FOSGToEFG

universe u
variable {Role : Type u} [DecidableEq Role] [Fintype Role]

/-- Independently realized equal singleton continuations remain the same
actual distribution under every admissible root mixture. -/
theorem publicChoice_singletons_eq (owner : Role) (left right : Game Role)
    (order : ExplicitOrder Role) (p : PMF Role)
    (hp : left.sequentialValues order = {p}) (hq : right.sequentialValues order = {p}) :
    (publicChoice owner left right).sequentialValues order = {p} := by
  ext law
  rw [sequentialValues_publicChoice_iff]
  constructor
  · rintro ⟨p',hp',q',hq',α,h0,h1,_,_,rfl⟩
    have hep : p' = p := by simpa only [hp,Set.mem_singleton_iff] using hp'
    have heq : q' = p := by simpa only [hq,Set.mem_singleton_iff] using hq'
    subst p'; subst q'
    simp only [mix_self,Set.mem_singleton_iff]
  · intro hlaw
    have he : law = p := hlaw
    rw [he]
    exact ⟨p,hp.symm ▸ Set.mem_singleton p,p,hq.symm ▸ Set.mem_singleton p,
      1,(by norm_num),le_rfl,(fun _ => le_rfl),(fun _ => le_rfl),(mix_one p p).symm⟩

/-- A public choice by the row role computes the maximum of actual scalar
continuation values, including the tie boundary. -/
theorem sequentialValues_public_max (a b : Role) (hab : a ≠ b) (left right : Game Role)
    (order : ExplicitOrder Role) (x y : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hleft : left.sequentialValues order = {distribution a b x hx0 hx1})
    (hright : right.sequentialValues order = {distribution a b y hy0 hy1}) :
    (publicChoice a left right).sequentialValues order =
      {distribution a b (max x y) (le_max_of_le_left hx0) (max_le hx1 hy1)} := by
  rcases lt_trichotomy x y with h | h | h
  · have he := publicChoice_singletons_of_lt a left right order _ _ hleft hright
      (by simpa only [distribution_a a b hab] using h)
    simpa only [max_eq_right h.le] using he
  · subst y
    simpa only [max_self] using publicChoice_singletons_eq a left right order _ hleft hright
  · have he := publicChoice_singletons_of_gt a left right order _ _ hleft hright
      (by simpa only [distribution_a a b hab] using h)
    simpa only [max_eq_left h.le] using he

/-- A public choice by the column role computes the minimum of actual scalar
continuation values, since its actual winner mass is the complement. -/
theorem sequentialValues_public_min (a b : Role) (hab : a ≠ b) (left right : Game Role)
    (order : ExplicitOrder Role) (x y : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hleft : left.sequentialValues order = {distribution a b x hx0 hx1})
    (hright : right.sequentialValues order = {distribution a b y hy0 hy1}) :
    (publicChoice b left right).sequentialValues order =
      {distribution a b (min x y) (le_min hx0 hy0) ((min_le_left x y).trans hx1)} := by
  rcases lt_trichotomy x y with h | h | h
  · have hcomp : (distribution a b y hy0 hy1 b).toReal <
        (distribution a b x hx0 hx1 b).toReal := by
      rw [distribution_b a b hab,distribution_b a b hab]
      linarith
    simpa only [min_eq_left h.le] using
      publicChoice_singletons_of_gt b left right order _ _ hleft hright hcomp
  · subst y
    simpa only [min_self] using publicChoice_singletons_eq b left right order _ hleft hright
  · have hcomp : (distribution a b x hx0 hx1 b).toReal <
        (distribution a b y hy0 hy1 b).toReal := by
      rw [distribution_b a b hab,distribution_b a b hab]
      linarith
    simpa only [min_eq_right h.le] using
      publicChoice_singletons_of_lt b left right order _ _ hleft hright hcomp

end KFOL.Rounds.Game.Scalar
