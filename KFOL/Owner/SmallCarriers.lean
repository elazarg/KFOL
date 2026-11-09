module

public import KFOL.Owner.SmallModels
public import Mathlib.Data.Fintype.EquivFin

/-! # Transport of small reset reducts and the ternary obstruction -/

@[expose] public section

namespace KFOL.Owner

universe u

/-- Idempotence forces associativity on a two-element carrier. Enumeration
ranges over every binary operation, not a supplied table certificate. -/
theorem idempotent_two_assoc : ∀ f : Fin 2 → Fin 2 → Fin 2,
    (∀ x, f x x = x) → ∀ x y z, f (f x y) z = f x (f y z) := by decide

private theorem associative_transfer {M : Type u} {n : ℕ} (e : M ≃ Fin n) (f : M → M → M)
    (h : let g : Fin n → Fin n → Fin n := fun x y => e (f (e.symm x) (e.symm y))
      ∀ x y z, g (g x y) z = g x (g y z)) :
    ∀ x y z, f (f x y) z = f x (f y z) := by
  dsimp only at h
  intro x y z
  apply e.injective
  simpa only [Equiv.symm_apply_apply] using h (e x) (e y) (e z)

/-- Every idempotent binary operation on any finite carrier of size at most
two is associative. This also supplies the small reset-generator exclusion. -/
theorem idempotent_assoc_of_card_le_two {M : Type u} [Fintype M]
    (f : M → M → M) (hi : ∀ x, f x x = x) (hc : Fintype.card M ≤ 2) :
    ∀ x y z, f (f x y) z = f x (f y z) := by
  classical
  have transfer (n : ℕ) (e : M ≃ Fin n)
      (hf : ∀ g : Fin n → Fin n → Fin n,
        (∀ x, g x x = x) → ∀ x y z, g (g x y) z = g x (g y z)) :
      ∀ x y z, f (f x y) z = f x (f y z) := by
    let g : Fin n → Fin n → Fin n := fun x y => e (f (e.symm x) (e.symm y))
    have hg : ∀ x, g x x = x := by intro x; simp only [g, hi, Equiv.apply_symm_apply]
    exact associative_transfer e f (hf g hg)
  have hcases : Fintype.card M = 0 ∨ Fintype.card M = 1 ∨ Fintype.card M = 2 := by omega
  rcases hcases with h | h | h
  · apply transfer 0 (Fintype.equivFinOfCardEq h)
    intro g _ x
    exact x.elim0
  · apply transfer 1 (Fintype.equivFinOfCardEq h)
    exact fun _ _ _ _ _ => Subsingleton.elim _ _
  · exact transfer 2 (Fintype.equivFinOfCardEq h) idempotent_two_assoc

private def chainReset (x y : Fin 3) : Fin 3 := if y = 1 then if x = 2 then 2 else 1 else y

private def MinorLaws (h : Fin 3 → Fin 3 → Fin 3 → Fin 3) : Prop :=
  ∀ x y z, h x y y = chainReset y x ∧ h y y z = chainReset z y ∧ h x y x = chainReset y x
private def FirstLaw (h : Fin 3 → Fin 3 → Fin 3 → Fin 3) : Prop :=
  ∀ x y z, chainReset (h x y z) (chainReset (chainReset z y) x) = chainReset (chainReset z y) x
private def SecondLaw (h : Fin 3 → Fin 3 → Fin 3 → Fin 3) : Prop :=
  ∀ x y z, chainReset (chainReset z x) (h x y z) = h x y z

private theorem three_absorption_bounds (h : Fin 3 → Fin 3 → Fin 3 → Fin 3)
    (ha : ∀ x y z, chainReset (h x y z) x = h x y z ∧ chainReset x (h x y z) = h x y z) :
    (∀ y z, h 0 y z = 0) ∧ (∀ y z, h 2 y z = 2) ∧
      (∀ y z, h 1 y z = 1 ∨ h 1 y z = 2) := by
  refine ⟨fun y z => ?_, (fun y z => ?_), fun y z => ?_⟩
  · have hh := (ha 0 y z).1
    simpa [chainReset] using hh.symm
  · have hh := ha 2 y z
    by_cases he : h 2 y z = 1
    · simp [chainReset, he] at hh
    · simpa [chainReset, he] using hh.1.symm
  · have hh := (ha 1 y z).1
    simp only [chainReset, ↓reduceIte] at hh
    split at hh <;> omega

private theorem three_state_obstruction (h : Fin 3 → Fin 3 → Fin 3 → Fin 3)
    (hz : ∀ y z, h 0 y z = 0) (ht : ∀ y z, h 2 y z = 2)
    (hu : ∀ y z, h 1 y z = 1 ∨ h 1 y z = 2) (hm : MinorLaws h) :
    FirstLaw h ∨ SecondLaw h := by
  have cases3 (x : Fin 3) : x = 0 ∨ x = 1 ∨ x = 2 := by omega
  have hd (x y : Fin 3) := (hm x y y).1
  have hl (y z : Fin 3) := (hm y y z).2.1
  have hr (x y : Fin 3) := (hm x y x).2.2
  by_cases he : h 1 0 2 = 1
  · left
    intro x y z
    rcases cases3 x with rfl | rfl | rfl <;>
      rcases cases3 y with rfl | rfl | rfl <;>
      rcases cases3 z with rfl | rfl | rfl <;>
      simp_all [chainReset]
  · have he' : h 1 0 2 = 2 := (hu 0 2).resolve_left he
    right
    intro x y z
    rcases cases3 x with rfl | rfl | rfl <;>
      rcases cases3 y with rfl | rfl | rfl <;>
      rcases cases3 z with rfl | rfl | rfl <;>
      simp_all [chainReset]

private theorem reset_three_equiv (f : Fin 3 → Fin 3 → Fin 3) (hf : Reset.Laws f)
    (hna : ¬∀ x y z, f (f x y) z = f x (f y z)) :
    ∃ e : Fin 3 ≃ Fin 3, ∀ x y, e (f x y) = chainReset (e x) (e y) := by
  rcases reset_three_classification f hf.idem hf.absorb hf.repeat_right hf.nested hf.exchange hf.left_comm with h | h
  · exact False.elim (hna h)
  · obtain ⟨a, b, c, hab, hac, hbc, haa, hab', hac', hba, hbb, hbc', hca, hcb, hcc⟩ := h
    have cases3 (x : Fin 3) : x = a ∨ x = b ∨ x = c := by omega
    let e : Fin 3 ≃ Fin 3 := {
      toFun := fun x => if x = a then 0 else if x = b then 1 else 2
      invFun := fun i => if i = 0 then a else if i = 1 then b else c
      left_inv := by
        intro x
        rcases cases3 x with rfl | rfl | rfl <;> simp [hab.symm, hac.symm, hbc.symm]
      right_inv := by
        intro i
        have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        rcases hi with rfl | rfl | rfl <;> simp [hab.symm, hac.symm, hbc.symm] }
    have hea : e a = 0 := by simp [e]
    have heb : e b = 1 := by simp [e, hab.symm]
    have hec : e c = 2 := by simp [e, hac.symm, hbc.symm]
    refine ⟨e, ?_⟩
    intro x y
    rcases cases3 x with rfl | rfl | rfl <;> rcases cases3 y with rfl | rfl | rfl <;>
      simp only [haa, hab', hac', hba, hbb, hbc', hca, hcb, hcc, hea, heb, hec] <;> rfl

private theorem reset_equiv_of_card_three {M : Type u} [Fintype M] (f : M → M → M)
    (hc : Fintype.card M = 3) (hf : Reset.Laws f)
    (hna : ¬∀ x y z, f (f x y) z = f x (f y z)) :
    ∃ e : M ≃ Fin 3, ∀ x y, e (f x y) = chainReset (e x) (e y) := by
  classical
  let e := Fintype.equivFinOfCardEq hc
  let g : Fin 3 → Fin 3 → Fin 3 := fun x y => e (f (e.symm x) (e.symm y))
  have hg : Reset.Laws g := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x
      simp only [g, hf.idem, Equiv.apply_symm_apply]
    · intro x y
      simpa only [g, Equiv.symm_apply_apply] using congrArg e (hf.absorb (e.symm x) (e.symm y))
    · intro x y
      simpa only [g, Equiv.symm_apply_apply] using congrArg e (hf.repeat_right (e.symm x) (e.symm y))
    · intro x y z
      simpa only [g, Equiv.symm_apply_apply] using congrArg e (hf.nested (e.symm x) (e.symm y) (e.symm z))
    · intro x y z
      simpa only [g, Equiv.symm_apply_apply] using congrArg e (hf.exchange (e.symm x) (e.symm y) (e.symm z))
    · intro x y z
      simpa only [g, Equiv.symm_apply_apply] using congrArg e (hf.left_comm (e.symm x) (e.symm y) (e.symm z))
  have hgnot : ¬∀ x y z, g (g x y) z = g x (g y z) := fun h => hna (associative_transfer e f h)
  obtain ⟨d, hd⟩ := reset_three_equiv g hg hgnot
  refine ⟨e.trans d, ?_⟩
  intro x y
  simpa only [g, Equiv.symm_apply_apply, Equiv.trans_apply] using hd (e x) (e y)

/-- Every expansion of a reset algebra on at most three elements satisfying
these minor/absorption identities obeys an additional identity which the
four-element generator refutes. No external order-algebra theorem is used. -/
theorem small_expansion_obstruction {M : Type u} [Fintype M]
    (f : M → M → M) (h : M → M → M → M) (hc : Fintype.card M ≤ 3) (hf : Reset.Laws f)
    (hminor : ∀ x y z, h x y y = f y x ∧ h y y z = f z y ∧ h x y x = f y x)
    (habs : ∀ x y z, f (h x y z) x = h x y z ∧ f x (h x y z) = h x y z) :
    (∀ x y z, f (f x y) z = f x (f y z)) ∨
    (∀ x y z, f (h x y z) (f (f z y) x) = f (f z y) x) ∨
    (∀ x y z, f (f z x) (h x y z) = h x y z) := by
  classical
  by_cases ha : ∀ x y z, f (f x y) z = f x (f y z)
  · exact Or.inl ha
  · have hn : Fintype.card M = 3 := by
      by_contra hn
      have hsmall : Fintype.card M ≤ 2 := by omega
      exact ha (idempotent_assoc_of_card_le_two f hf.idem hsmall)
    obtain ⟨e, he⟩ := reset_equiv_of_card_three f hn hf ha
    let g : Fin 3 → Fin 3 → Fin 3 → Fin 3 := fun x y z => e (h (e.symm x) (e.symm y) (e.symm z))
    have hgm : MinorLaws g := by
      intro x y z
      have hm := hminor (e.symm x) (e.symm y) (e.symm z)
      refine ⟨?_, ?_, ?_⟩
      · simpa only [g, he, Equiv.apply_symm_apply] using congrArg e hm.1
      · simpa only [g, he, Equiv.apply_symm_apply] using congrArg e hm.2.1
      · simpa only [g, he, Equiv.apply_symm_apply] using congrArg e hm.2.2
    have hga : ∀ x y z, chainReset (g x y z) x = g x y z ∧ chainReset x (g x y z) = g x y z := by
      intro x y z
      have hh := habs (e.symm x) (e.symm y) (e.symm z)
      constructor
      · simpa only [he, Equiv.apply_symm_apply, g] using congrArg e hh.1
      · simpa only [he, Equiv.apply_symm_apply, g] using congrArg e hh.2
    obtain ⟨hz, ht, hu⟩ := three_absorption_bounds g hga
    rcases three_state_obstruction g hz ht hu hgm with hfirst | hsecond
    · right; left
      intro x y z
      apply e.injective
      simpa only [he, g, Equiv.symm_apply_apply] using hfirst (e x) (e y) (e z)
    · right; right
      intro x y z
      apply e.injective
      simpa only [he, g, Equiv.symm_apply_apply] using hsecond (e x) (e y) (e z)

end KFOL.Owner
