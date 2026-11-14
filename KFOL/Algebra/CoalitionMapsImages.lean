module

public import KFOL.Algebra.CoalitionMaps

/-! # Direct images and depth-one obstructions for role coalescing -/

@[expose] public section

namespace KFOL.CoalitionMaps

universe u v

variable {Role : Type u} {Team : Type v}

theorem image_of_constant (f : Role → Team) (q : Team) (hf : ∀ r, f r = q)
    (A : WinnerSet Role) : image f A = WinnerSet.singleton q := by
  apply WinnerSet.eq_singleton_of_subset
  rintro _ ⟨r, _, rfl⟩
  exact hf r

/-- Direct image preserves all owned choices exactly for embeddings and
the map forming one single team. -/
theorem image_intertwines_iff (f : Role → Team) :
    Intertwines f (image f) ↔ Function.Injective f ∨ IsConstant f := by
  classical
  constructor
  · rintro ⟨hatom, hchoice⟩
    by_cases hi : Function.Injective f
    · exact Or.inl hi
    right
    obtain ⟨a, b, hab, hfab⟩ : ∃ a b, a ≠ b ∧ f a = f b := by
      by_contra hn
      apply hi
      intro a b he
      by_contra hab
      exact hn ⟨a, b, hab, he⟩
    refine ⟨f a, ?_⟩
    intro c
    by_contra hc
    have hac : a ≠ c := fun he => hc (congrArg f he.symm)
    have hleft : WinnerSet.choice a (WinnerSet.singleton b) (WinnerSet.singleton c) =
        WinnerSet.union (WinnerSet.singleton b) (WinnerSet.singleton c) := by
      simp [WinnerSet.choice, hab.symm, hac.symm]
    have hv : image f (WinnerSet.union (WinnerSet.singleton b) (WinnerSet.singleton c)) =
        WinnerSet.singleton (f a) := by
      rw [← hleft, hchoice, hatom, hatom, ← hfab]
      simp [WinnerSet.choice]
    have hm : f c ∈ (image f
        (WinnerSet.union (WinnerSet.singleton b) (WinnerSet.singleton c))).val :=
      ⟨c, Or.inr rfl, rfl⟩
    exact hc (by simpa [hv] using hm)
  · rintro (hi | ⟨q, hq⟩)
    · exact image_intertwines f hi
    · have himage : image f = fun _ => WinnerSet.singleton q :=
        funext (image_of_constant f q hq)
      rw [himage]
      exact constant_intertwines f q hq

/-- Recomputing a choice after coalescing roles can discard old possible
teams, but cannot create a team absent from both old continuations. -/
theorem choice_subset_image (f : Role → Team) (r : Role)
    (A B : WinnerSet Role) (A' B' : WinnerSet Team)
    (ha : A'.val ⊆ (image f A).val) (hb : B'.val ⊆ (image f B).val) :
    (WinnerSet.choice (f r) A' B').val ⊆
      (image f (WinnerSet.choice r A B)).val := by
  classical
  by_cases h : A = WinnerSet.singleton r ∨ B = WinnerSet.singleton r
  · have hold : WinnerSet.choice r A B = WinnerSet.singleton r := by
      simp [WinnerSet.choice, h]
    rw [hold, image_singleton]
    rcases h with hA | hB
    · have he : A' = WinnerSet.singleton (f r) :=
        WinnerSet.eq_singleton_of_subset A' (f r) (by simpa [hA] using ha)
      simp [he, WinnerSet.choice]
    · have he : B' = WinnerSet.singleton (f r) :=
        WinnerSet.eq_singleton_of_subset B' (f r) (by simpa [hB] using hb)
      simp [he, WinnerSet.choice]
  · have hold : WinnerSet.choice r A B = WinnerSet.union A B := by
      simp [WinnerSet.choice, h]
    rw [hold, image_union]
    exact (WinnerSet.choice_subset_union (f r) A' B').trans
      (Set.union_subset (ha.trans Set.subset_union_left) (hb.trans Set.subset_union_right))

/-- Every failure of descent is visible in two depth-one games with the
same two terminal winners and different owners. -/
theorem exists_two_leaf_obstruction (f : Role → Team) (hf : ¬Descends f) :
    ∃ a b c d,
      WinnerSet.choice a (WinnerSet.singleton b) (WinnerSet.singleton c) =
        WinnerSet.choice d (WinnerSet.singleton b) (WinnerSet.singleton c) ∧
      WinnerSet.choice (f a) (WinnerSet.singleton (f b)) (WinnerSet.singleton (f c)) ≠
        WinnerSet.choice (f d) (WinnerSet.singleton (f b)) (WinnerSet.singleton (f c)) := by
  classical
  have hbad : ¬Admissible f := fun h => hf ((descends_iff f).mpr h)
  have hni : ¬Function.Injective f := fun h => hbad (Or.inl h)
  obtain ⟨a, b, hab, hfab⟩ : ∃ a b, a ≠ b ∧ f a = f b := by
    by_contra hn
    apply hni
    intro a b he
    by_contra hab
    exact hn ⟨a, b, hab, he⟩
  have hnc : ¬∀ c, f c = f a := fun h => hbad (Or.inr (Or.inl ⟨f a, h⟩))
  obtain ⟨c, hc⟩ := not_forall.mp hnc
  have hnb : ¬∀ d, d ≠ c → f d = f a :=
    fun h => hbad (Or.inr (Or.inr ⟨c, f a, hc, h⟩))
  obtain ⟨d, hd⟩ := not_forall.mp hnb
  have hdc : d ≠ c := by
    intro he
    exact hd (fun hn => False.elim (hn he))
  have hfd : f d ≠ f a := fun he => hd (fun _ => he)
  have hac : a ≠ c := fun he => hc (congrArg f he.symm)
  have hdb : d ≠ b := fun he => hfd ((congrArg f he).trans hfab.symm)
  refine ⟨a, b, c, d, ?_, ?_⟩
  · simp [WinnerSet.choice, hab.symm, hac.symm, hdb.symm, hdc.symm]
  · rw [← hfab]
    have ha : WinnerSet.choice (f a) (WinnerSet.singleton (f a))
        (WinnerSet.singleton (f c)) = WinnerSet.singleton (f a) := by
      simp [WinnerSet.choice]
    rw [ha]
    exact fun he => hfd ((choice_pair_eq_left_iff (f a) (f c) (f d) (Ne.symm hc)).mp he.symm)

end KFOL.CoalitionMaps
