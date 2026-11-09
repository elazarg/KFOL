module

public import KFOL.Policies.PolicyExpr
public import Mathlib.Order.Minimal

/-! Direct finite incidence construction for the hard policy families. -/

@[expose] public section

namespace KFOL.Policies

universe u v

variable {Role : Type u} {Label : Type v}

/-- A missing meet has a minimal strict extension and another extension that
omits a label of that minimum. The pattern collection itself need not be finite. -/
theorem exists_pattern_split [DecidableEq Label] (P : Set (Finset Label))
    (s p q : Finset Label) (hp : p ∈ P) (hq : q ∈ P) (hs : p ∩ q = s)
    (hmissing : s ∉ P) :
    ∃ m ∈ P, s ⊆ m ∧ (∀ v ∈ P, s ⊆ v → v ⊆ m → m ⊆ v) ∧
      ∃ t ∈ P, s ⊆ t ∧ ¬m ⊆ t := by
  obtain ⟨m, hm, hmin⟩ := exists_minimal_of_wellFoundedLT
    (fun v : Finset Label => v ∈ P ∧ s ⊆ v)
    ⟨p, hp, hs ▸ Finset.inter_subset_left⟩
  refine ⟨m, hm.1, hm.2, fun v hv hsv hvm => hmin ⟨hv, hsv⟩ hvm, ?_⟩
  have hnot : ¬(m ⊆ p ∧ m ⊆ q) := by
    rintro ⟨hmp, hmq⟩
    have hms : m ⊆ s := hs ▸ Finset.subset_inter hmp hmq
    exact hmissing ((Finset.Subset.antisymm hm.2 hms) ▸ hm.1)
  by_cases hmp : m ⊆ p
  · exact ⟨q, hq, hs ▸ Finset.inter_subset_right, fun hmq => hnot ⟨hmp, hmq⟩⟩
  · exact ⟨p, hp, hs ▸ Finset.inter_subset_left, hmp⟩

end KFOL.Policies

namespace KFOL.Policies

universe u v w x

variable {Role : Type u} {Label : Type v}

/-- Non-easy incidence data is either a missing meet in the complete role set,
or a missing meet after deleting the unique role representing that meet. -/
theorem missing_meet_of_not_easy [Fintype Role] [DecidableEq Role] [DecidableEq Label]
    (pattern : Role → Finset Label)
    (hchain : ¬∀ r s, pattern r ⊆ pattern s ∨ pattern s ⊆ pattern r)
    (heasy : ¬((∀ r s, ∃ t, pattern t = pattern r ∩ pattern s) ∧
      ∃ r s, r ≠ s ∧ pattern r = pattern s)) :
    ∃ (J : Finset Role) (s : Finset Label) (p q : Role),
      p ∈ J ∧ q ∈ J ∧ pattern p ∩ pattern q = s ∧
      (∀ r ∈ J, pattern r ≠ s) ∧
      (J = Finset.univ ∨ ∃ k, J = Finset.univ.erase k ∧ Function.Injective pattern) := by
  classical
  by_cases hc : ∀ r s, ∃ t, pattern t = pattern r ∩ pattern s
  · have hinj : Function.Injective pattern := by
      intro r s hrs
      by_contra hne
      exact heasy ⟨hc, r, s, hne, hrs⟩
    push Not at hchain
    obtain ⟨p, q, hpq, hqp⟩ := hchain
    obtain ⟨k, hk⟩ := hc p q
    refine ⟨Finset.univ.erase k, pattern k, p, q, ?_, ?_, hk.symm, ?_, Or.inr ⟨k, rfl, hinj⟩⟩
    · simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      intro hpk
      subst p
      exact hpq (hk ▸ Finset.inter_subset_right)
    · simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      intro hqk
      subst q
      exact hqp (hk ▸ Finset.inter_subset_left)
    · intro r hr heq
      exact (Finset.mem_erase.mp hr).1 (hinj heq)
  · push Not at hc
    obtain ⟨p, q, hpq⟩ := hc
    exact ⟨Finset.univ, pattern p ∩ pattern q, p, q,
      Finset.mem_univ _, Finset.mem_univ _, rfl, fun r _ => hpq r, Or.inl rfl⟩

end KFOL.Policies

namespace KFOL.Policies

universe u v w x

variable {Role : Type u} {Label : Type v}

private theorem not_mem_union_difference [DecidableEq Label]
    (D : Label → Set Role) (pattern : Role → Finset Label)
    (hpattern : ∀ r d, d ∈ pattern r ↔ r ∉ D d)
    (r : Role) (s t : Finset Label) (hs : s ⊆ pattern r) :
    r ∉ (PolicyExpr.unionLabels (t \ s).toList).eval D ↔ t ⊆ pattern r := by
  rw [PolicyExpr.not_mem_eval_unionLabels]
  constructor
  · intro h d hd
    by_cases hds : d ∈ s
    · exact hs hds
    · exact (hpattern r d).mpr (h d (by simpa using Finset.mem_sdiff.mpr ⟨hd, hds⟩))
  · intro h d hd
    exact (hpattern r d).mp (h (Finset.mem_sdiff.mp (by simpa using hd)).1)

/-- The two blocking policies required by the hard reduction are native lattice
macros. No external generation theorem or missing-meet oracle is assumed. -/
theorem exists_hard_policy_macros [DecidableEq Role] [DecidableEq Label]
    (D : Label → Set Role) (pattern : Role → Finset Label)
    (hpattern : ∀ r d, d ∈ pattern r ↔ r ∉ D d)
    (J : Finset Role) (s : Finset Label) (p q : Role)
    (hp : p ∈ J) (hq : q ∈ J) (hs : pattern p ∩ pattern q = s)
    (hmissing : ∀ r ∈ J, pattern r ≠ s) :
    ∃ (a b : Role) (E F : PolicyExpr Label),
      a ∈ J ∧ b ∈ J ∧ a ≠ b ∧
      a ∉ (PolicyExpr.unionLabels s.toList).eval D ∧
      b ∉ (PolicyExpr.unionLabels s.toList).eval D ∧
      a ∈ E.eval D ∧ a ∉ F.eval D ∧ b ∉ E.eval D ∧ b ∈ F.eval D ∧
      ∀ r ∈ J, r ∉ (PolicyExpr.unionLabels s.toList).eval D →
        r ∉ E.eval D ∨ r ∉ F.eval D := by
  classical
  let P : Set (Finset Label) := {v | ∃ r ∈ J, pattern r = v}
  have hpP : pattern p ∈ P := ⟨p, hp, rfl⟩
  have hqP : pattern q ∈ P := ⟨q, hq, rfl⟩
  have hsP : s ∉ P := by
    rintro ⟨r, hr, he⟩
    exact hmissing r hr he
  obtain ⟨m, hmP, hsm, hmin, t, htP, hst, hmt⟩ :=
    exists_pattern_split P s (pattern p) (pattern q) hpP hqP hs hsP
  obtain ⟨b, hbJ, rfl⟩ := hmP
  obtain ⟨a, haJ, rfl⟩ := htP
  let E : PolicyExpr Label := PolicyExpr.unionLabels (pattern b \ s).toList
  let others := J.filter (fun r => s ⊆ pattern r ∧ ¬pattern b ⊆ pattern r)
  let F : PolicyExpr Label := PolicyExpr.meetAll
    (others.toList.map (fun r => PolicyExpr.unionLabels (pattern r \ s).toList))
  have hU (r : Role) : r ∉ (PolicyExpr.unionLabels s.toList).eval D ↔ s ⊆ pattern r := by
    simp only [PolicyExpr.not_mem_eval_unionLabels, Finset.mem_toList]
    exact ⟨fun h d hd => (hpattern r d).mpr (h d hd),
      fun h d hd => (hpattern r d).mp (h hd)⟩
  have hE (r : Role) (hr : s ⊆ pattern r) : r ∉ E.eval D ↔ pattern b ⊆ pattern r :=
    not_mem_union_difference D pattern hpattern r s (pattern b) hr
  have hFnot (r : Role) (hr : r ∈ others) : r ∉ F.eval D := by
    intro hmem
    have htest := (PolicyExpr.mem_eval_meetAll D r _).mp hmem
      (PolicyExpr.unionLabels (pattern r \ s).toList)
      (List.mem_map.mpr ⟨r, Finset.mem_toList.mpr hr, rfl⟩)
    exact (not_mem_union_difference D pattern hpattern r s (pattern r)
      (Finset.mem_filter.mp hr).2.1).mpr Finset.Subset.rfl htest
  have haOthers : a ∈ others := Finset.mem_filter.mpr ⟨haJ, hst, hmt⟩
  have hbF : b ∈ F.eval D := by
    apply (PolicyExpr.mem_eval_meetAll D b _).mpr
    intro E hE
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hE
    have hr' := Finset.mem_filter.mp (Finset.mem_toList.mp hr)
    by_contra hnot
    have hrb : pattern r ⊆ pattern b :=
      (not_mem_union_difference D pattern hpattern b s (pattern r) hsm).mp hnot
    exact hr'.2.2 (hmin (pattern r) ⟨r, hr'.1, rfl⟩ hr'.2.1 hrb)
  refine ⟨a, b, E, F, haJ, hbJ, ?_, (hU a).mpr hst, (hU b).mpr hsm,
    ?_, hFnot a haOthers, (hE b hsm).mpr Finset.Subset.rfl, hbF, ?_⟩
  · intro hab
    exact hmt (hab ▸ Finset.Subset.rfl)
  · by_contra hnot
    exact hmt ((hE a hst).mp hnot)
  · intro r hr hru
    have hsr := (hU r).mp hru
    by_cases hbr : pattern b ⊆ pattern r
    · exact Or.inl ((hE r hsr).mpr hbr)
    · exact Or.inr (hFnot r (Finset.mem_filter.mpr ⟨hr, hsr, hbr⟩))

end KFOL.Policies
