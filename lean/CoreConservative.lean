/- Generic structure of conservative core models. The final passage from
dissemilattices to the core variety uses the external generation theorem
cited in appendix-core-basis.tex; that passage is not an axiom here. -/
import CoreModels

set_option autoImplicit false
namespace MinimalChoice.CoreConservative
open Std

structure ChainJoin (α : Type) where
  add : α → α → α
  idem : ∀ x, add x x = x
  comm : ∀ x y, add x y = add y x
  assoc : ∀ x y z, add (add x y) z = add x (add y z)
  conservative : ∀ x y, add x y = x ∨ add x y = y

def ChainJoin.le {α : Type} (s : ChainJoin α) (x y : α) : Prop := s.add x y = y

theorem ChainJoin.refl {α : Type} (s : ChainJoin α) (x : α) : s.le x x := s.idem x

theorem ChainJoin.antisymm {α : Type} (s : ChainJoin α) {x y : α}
    (hxy : s.le x y) (hyx : s.le y x) : x = y := by
  dsimp [le] at *
  calc x = s.add y x := hyx.symm
       _ = s.add x y := s.comm y x
       _ = y := hxy

theorem ChainJoin.trans {α : Type} (s : ChainJoin α) {x y z : α}
    (hxy : s.le x y) (hyz : s.le y z) : s.le x z := by
  dsimp [le] at *
  calc s.add x z = s.add x (s.add y z) := by rw [hyz]
       _ = s.add (s.add x y) z := (s.assoc x y z).symm
       _ = z := by rw [hxy, hyz]

theorem ChainJoin.total {α : Type} (s : ChainJoin α) (x y : α) :
    s.le x y ∨ s.le y x := by
  rcases s.conservative x y with h | h
  · exact Or.inr ((s.comm y x).trans h)
  · exact Or.inl h

theorem monotone_left {α : Type} (s : ChainJoin α) (f : α → α → α)
    (comm : ∀ x y, f x y = f y x)
    (dist : ∀ x y z, f x (s.add y z) = s.add (f x y) (f x z))
    {x y : α} (hxy : s.le x y) (z : α) : s.le (f x z) (f y z) := by
  change s.add (f x z) (f y z) = f y z
  rw [comm x z, comm y z, ← dist, hxy]

theorem monotone_right {α : Type} (s : ChainJoin α) (f : α → α → α)
    (dist : ∀ x y z, f x (s.add y z) = s.add (f x y) (f x z))
    {x y : α} (hxy : s.le x y) (z : α) : s.le (f z x) (f z y) := by
  change s.add (f z x) (f z y) = f z y
  rw [← dist, hxy]

/-- Any non-join conservative commutative operation reverses a strict pair. -/
theorem inversion {α : Type} (s : ChainJoin α) (f : α → α → α)
    (comm : ∀ x y, f x y = f y x)
    (cons : ∀ x y, f x y = x ∨ f x y = y) (hne : f ≠ s.add) :
    ∃ x y, s.le x y ∧ x ≠ y ∧ f x y = x := by
  classical
  have hex : ∃ x y, f x y ≠ s.add x y := by
    apply Classical.byContradiction
    intro hn
    apply hne
    funext x y
    exact Classical.byContradiction (fun h => hn ⟨x, y, h⟩)
  obtain ⟨x, y, h⟩ := hex
  rcases s.total x y with hxy | hyx
  · have hf : f x y = x := (cons x y).resolve_right (fun he => h (he.trans hxy.symm))
    refine ⟨x, y, hxy, ?_, hf⟩
    intro he
    exact h (hf.trans (he.trans hxy.symm))
  · have hf : f y x ≠ s.add y x := by simpa [comm y x, s.comm y x] using h
    have he : f y x = y := (cons y x).resolve_right (fun he => hf (he.trans hyx.symm))
    refine ⟨y, x, hyx, ?_, he⟩
    intro hy
    exact hf (he.trans (hy.trans hyx.symm))

/-- An inversion extends to every nonempty lower rectangle beneath it. -/
theorem lower_inversion {α : Type} (s : ChainJoin α) (f : α → α → α)
    (cons : ∀ x y, f x y = x ∨ f x y = y)
    (monoL : ∀ {x y}, s.le x y → ∀ z, s.le (f x z) (f y z))
    (monoR : ∀ {x y}, s.le x y → ∀ z, s.le (f z x) (f z y))
    {x y a b : α} (hxy : s.le x y) (hne : x ≠ y) (hf : f x y = x)
    (hax : s.le a x) (hby : s.le b y) (hab : s.le a b) : f a b = a := by
  have hay : f a y = a := by
    rcases cons a y with h | h
    · exact h
    · have hlow := monoL hax y
      rw [h, hf] at hlow
      exact False.elim (hne (s.antisymm hxy hlow))
  have hlow := monoR hby a
  rw [hay] at hlow
  rcases cons a b with h | h
  · exact h
  · rw [h] at hlow
    exact h.trans (s.antisymm hlow hab)

/-- Two distinct owners cannot both differ from join in a conservative model. -/
theorem one_of_pair_is_join {α : Type} (s : ChainJoin α) (f g : α → α → α)
    (fc : ∀ x y, f x y = f y x) (gc : ∀ x y, g x y = g y x)
    (fs : ∀ x y, f x y = x ∨ f x y = y)
    (gs : ∀ x y, g x y = x ∨ g x y = y)
    (fd : ∀ x y z, f x (s.add y z) = s.add (f x y) (f x z))
    (gd : ∀ x y z, g x (s.add y z) = s.add (g x y) (g x z))
    (cover : ∀ x y, s.add (f x y) (g x y) = s.add x y) :
    f = s.add ∨ g = s.add := by
  classical
  by_cases hf : f = s.add
  · exact Or.inl hf
  apply Or.inr
  apply Classical.byContradiction
  intro hg
  obtain ⟨x, y, hxy, hne, hfxy⟩ := inversion s f fc fs hf
  obtain ⟨u, v, huv, hne', hguv⟩ := inversion s g gc gs hg
  have low (a b : α) : ∃ c, s.le c a ∧ s.le c b ∧ (c = a ∨ c = b) := by
    rcases s.total a b with h | h
    · exact ⟨a, s.refl a, h, Or.inl rfl⟩
    · exact ⟨b, h, s.refl b, Or.inr rfl⟩
  obtain ⟨a, hax, hau, _⟩ := low x u
  obtain ⟨b, hby, hbv, hb⟩ := low y v
  have hab : s.le a b := by
    rcases hb with rfl | rfl
    · exact s.trans hax hxy
    · exact s.trans hau huv
  have habne : a ≠ b := by
    intro he
    rcases hb with rfl | rfl
    · exact hne (s.antisymm hxy (he ▸ hax))
    · exact hne' (s.antisymm huv (he ▸ hau))
  have hfa := lower_inversion s f fs (monotone_left s f fc fd)
    (monotone_right s f fd) hxy hne hfxy hax hby hab
  have hga := lower_inversion s g gs (monotone_left s g gc gd)
    (monotone_right s g gd) huv hne' hguv hau hbv hab
  have h := cover a b
  rw [hfa, hga, s.idem, hab] at h
  exact habne h

end MinimalChoice.CoreConservative

#print axioms MinimalChoice.CoreConservative.one_of_pair_is_join
