module

public import KFOL.Definitions.CoalitionMaps
public import KFOL.Algebra.Basic

/-! # Exact descent classification for role coalescing -/

@[expose] public section

namespace KFOL.CoalitionMaps

universe u v

variable {Role : Type u} {Team : Type v}

@[simp] theorem image_singleton (f : Role → Team) (r : Role) :
    image f (WinnerSet.singleton r) = WinnerSet.singleton (f r) := by
  apply Subtype.ext
  exact Set.image_singleton

@[simp] theorem image_union (f : Role → Team) (A B : WinnerSet Role) :
    image f (WinnerSet.union A B) = WinnerSet.union (image f A) (image f B) := by
  apply Subtype.ext
  exact Set.image_union _ _ _

theorem image_eq_singleton_iff (f : Role → Team) (hf : Function.Injective f)
    (A : WinnerSet Role) (r : Role) :
    image f A = WinnerSet.singleton (f r) ↔ A = WinnerSet.singleton r := by
  constructor
  · intro h
    apply WinnerSet.eq_singleton_of_subset
    intro x hx
    apply hf
    have hfx : f x ∈ (image f A).val := ⟨x, hx, rfl⟩
    simpa [h] using hfx
  · rintro rfl
    exact image_singleton f r

theorem image_intertwines (f : Role → Team) (hf : Function.Injective f) :
    Intertwines f (image f) := by
  classical
  refine ⟨image_singleton f, ?_⟩
  intro r A B
  have hA := image_eq_singleton_iff f hf A r
  have hB := image_eq_singleton_iff f hf B r
  by_cases h : A = WinnerSet.singleton r ∨ B = WinnerSet.singleton r
  · have ht := (or_congr hA hB).mpr h
    simp [WinnerSet.choice, h, ht]
  · have ht : ¬(image f A = WinnerSet.singleton (f r) ∨
        image f B = WinnerSet.singleton (f r)) := fun ht => h ((or_congr hA hB).mp ht)
    simp [WinnerSet.choice, h, ht]

theorem constant_intertwines (f : Role → Team) (q : Team) (hf : ∀ r, f r = q) :
    Intertwines f (fun _ => WinnerSet.singleton q) := by
  refine ⟨fun r => by rw [hf r], ?_⟩
  intro r A B
  rw [hf r, WinnerSet.choice_self]

theorem collapse_intertwines (f : Role → Team) (c : Role) (q : Team)
    (hc : f c ≠ q) (hothers : ∀ r, r ≠ c → f r = q) :
    Intertwines f (collapse c q (f c)) := by
  classical
  refine ⟨?_, ?_⟩
  · intro r
    by_cases hrc : r = c
    · subst r
      simp [collapse]
    · simp [collapse, WinnerSet.singleton_inj, hrc, hothers r hrc]
  · intro r A B
    by_cases hrc : r = c
    · subst r
      simp only [collapse, WinnerSet.choice_eq_owner_iff]
      by_cases ha : A = WinnerSet.singleton c <;>
        by_cases hb : B = WinnerSet.singleton c
      all_goals simp_all [WinnerSet.choice]
    · have hr := hothers r hrc
      have he := WinnerSet.choice_eq_other_iff A B r hrc
      simp only [collapse, he, hr]
      by_cases ha : A = WinnerSet.singleton c <;>
        by_cases hb : B = WinnerSet.singleton c
      all_goals simp_all [WinnerSet.choice]

/-- On two distinct winner atoms, an owner selects the first atom precisely
when it is that atom's owner. -/
theorem choice_pair_eq_left_iff (q s t : Team) (hqs : q ≠ s) :
    WinnerSet.choice t (WinnerSet.singleton q) (WinnerSet.singleton s) =
      WinnerSet.singleton q ↔ t = q := by
  constructor
  · intro h
    by_contra ht
    have hh := (WinnerSet.choice_eq_other_iff
      (WinnerSet.singleton q) (WinnerSet.singleton s) t ht).mp h
    exact hqs (WinnerSet.singleton_inj.mp hh.2).symm
  · rintro rfl
    simp [WinnerSet.choice]

/-- A single pair of equal-image roles and one different image forces
every role outside the latter's singleton block into the common team. -/
theorem singleton_block_of_collision (f : Role → Team)
    (h : Descends f) {a b c : Role} (hab : a ≠ b)
    (hfab : f a = f b) (hc : f c ≠ f a) :
    ∀ r, r ≠ c → f r = f a := by
  classical
  obtain ⟨hmap, hatom, hchoice⟩ := h
  have hac : a ≠ c := fun he => hc (congrArg f he.symm)
  have hbc : b ≠ c := fun he => hc ((congrArg f he.symm).trans hfab.symm)
  have hleft : WinnerSet.choice a (WinnerSet.singleton b) (WinnerSet.singleton c) =
      WinnerSet.union (WinnerSet.singleton b) (WinnerSet.singleton c) := by
    simp [WinnerSet.choice, hab.symm, hac.symm]
  have hvalue : hmap (WinnerSet.union (WinnerSet.singleton b) (WinnerSet.singleton c)) =
      WinnerSet.singleton (f a) := by
    rw [← hleft, hchoice, hatom, hatom, ← hfab]
    simp [WinnerSet.choice]
  intro r hrc
  by_cases hrb : r = b
  · simpa [hrb] using hfab.symm
  have hright : WinnerSet.choice r (WinnerSet.singleton b) (WinnerSet.singleton c) =
      WinnerSet.union (WinnerSet.singleton b) (WinnerSet.singleton c) := by
    simp [WinnerSet.choice, Ne.symm hrb, Ne.symm hrc]
  have htarget : WinnerSet.choice (f r) (WinnerSet.singleton (f a))
      (WinnerSet.singleton (f c)) = WinnerSet.singleton (f a) := by
    have hh := hchoice r (WinnerSet.singleton b) (WinnerSet.singleton c)
    rw [hright, hvalue, hatom, hatom, ← hfab] at hh
    exact hh.symm
  exact (choice_pair_eq_left_iff (f a) (f c) (f r) hc.symm).mp htarget

/-- Exact algebraic classification, without any finiteness hypothesis. -/
theorem descends_iff (f : Role → Team) : Descends f ↔ Admissible f := by
  classical
  constructor
  · intro h
    by_cases hi : Function.Injective f
    · exact Or.inl hi
    · right
      obtain ⟨a, b, hab, hfab⟩ : ∃ a b, a ≠ b ∧ f a = f b := by
        have hh : ∃ a b, f a = f b ∧ a ≠ b := by
          by_contra hn
          apply hi
          intro a b he
          by_contra hab
          exact hn ⟨a, b, he, hab⟩
        obtain ⟨a, b, he, hn⟩ := hh
        exact ⟨a, b, hn, he⟩
      by_cases hc : ∀ c, f c = f a
      · exact Or.inl ⟨f a, hc⟩
      · obtain ⟨c, hc⟩ := not_forall.mp hc
        exact Or.inr ⟨c, f a, hc, singleton_block_of_collision f h hab hfab hc⟩
  · rintro (hi | ⟨q, hq⟩ | ⟨c, q, hc, hr⟩)
    · exact ⟨image f, image_intertwines f hi⟩
    · exact ⟨fun _ => WinnerSet.singleton q, constant_intertwines f q hq⟩
    · exact ⟨collapse c q (f c), collapse_intertwines f c q hc hr⟩

end KFOL.CoalitionMaps
