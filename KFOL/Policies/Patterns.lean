module

public import KFOL.Definitions.Policies
public import Mathlib.Data.Set.Finite.Basic

/-! Passing-pattern incidence, the exact finite criterion checker, and
intersection closure for observer-restricted role patterns. -/

@[expose] public section

namespace KFOL.Policies

universe u v

variable {Role : Type u} {Label : Type v}

@[simp] theorem mem_passingPattern (D : Label → Set Role) (r : Role) (d : Label) :
    d ∈ passingPattern D r ↔ r ∉ D d := Iff.rfl

theorem passingPattern_eq_iff (D : Label → Set Role) (r s : Role) :
    passingPattern D r = passingPattern D s ↔ ∀ d, r ∈ D d ↔ s ∈ D d := by
  classical
  constructor
  · intro he d
    have hn : r ∉ D d ↔ s ∉ D d := by
      change d ∈ passingPattern D r ↔ d ∈ passingPattern D s
      rw [he]
    tauto
  · intro h
    ext d
    exact not_congr (h d)

/-- Row comparability of the passing matrix is exactly column comparability
of the policy family. No finiteness assumptions are hidden here. -/
theorem patternChain_iff_policies_chain (D : Label → Set Role) :
    PatternChain D ↔ ∀ i j, D i ⊆ D j ∨ D j ⊆ D i := by
  classical
  constructor
  · intro h i j
    by_cases hij : D i ⊆ D j
    · exact Or.inl hij
    · right
      by_contra hji
      have hi : ∃ r, r ∈ D i ∧ r ∉ D j := by simpa only [Set.not_subset] using hij
      have hj : ∃ r, r ∈ D j ∧ r ∉ D i := by simpa only [Set.not_subset] using hji
      obtain ⟨r, hri, hrj⟩ := hi
      obtain ⟨s, hsj, hsi⟩ := hj
      rcases h r s with hrs | hsr
      · exact (hrs hrj) hsj
      · exact (hsr hsi) hri
  · intro h r s
    by_cases hrs : passingPattern D r ⊆ passingPattern D s
    · exact Or.inl hrs
    · right
      intro i hsi
      by_contra hri
      have hri' : r ∈ D i := by simpa only [mem_passingPattern, not_not] using hri
      have hsi' : s ∉ D i := hsi
      have hfail : ∃ j, r ∉ D j ∧ s ∈ D j := by
        simpa only [Set.not_subset, mem_passingPattern, not_not] using hrs
      obtain ⟨j, hrj, hsj⟩ := hfail
      rcases h i j with hij | hji
      · exact hrj (hij hri')
      · exact hsi' (hji hsj)

@[simp] theorem coe_passingFinset [DecidableEq Role] [DecidableEq Label]
    (D : Label → Finset Role) (labels : List Label) (hlabels : ∀ d, d ∈ labels) (r : Role) :
    (passingFinset D labels r : Set Label) = passingPattern (fun d => (D d : Set Role)) r := by
  ext d
  simp only [Finset.mem_coe, passingFinset, List.mem_toFinset, List.mem_filter, decide_eq_true_eq,
    hlabels d, true_and, mem_passingPattern]

/-- The explicit criterion program is correct for complete input dictionaries,
including empty families, endpoint policies and repeated policy symbols. -/
theorem familyEasyB_correct [DecidableEq Role] [DecidableEq Label]
    (D : Label → Finset Role) (roles : List Role) (labels : List Label)
    (hroles : ∀ r, r ∈ roles) (hlabels : ∀ d, d ∈ labels) :
    familyEasyB D roles labels = true ↔ FamilyEasy (fun d => (D d : Set Role)) := by
  have hsubset (r s : Role) : passingFinset D labels r ⊆ passingFinset D labels s ↔
      passingPattern (fun d => (D d : Set Role)) r ⊆ passingPattern (fun d => (D d : Set Role)) s := by
    change ((passingFinset D labels r : Set Label) ⊆ (passingFinset D labels s : Set Label)) ↔ _
    rw [coe_passingFinset D labels hlabels, coe_passingFinset D labels hlabels]
  have heq (r s : Role) : passingFinset D labels r = passingFinset D labels s ↔
      passingPattern (fun d => (D d : Set Role)) r = passingPattern (fun d => (D d : Set Role)) s := by
    rw [← Finset.coe_inj, coe_passingFinset D labels hlabels, coe_passingFinset D labels hlabels]
  have hinter (r s t : Role) : passingFinset D labels t = passingFinset D labels r ∩ passingFinset D labels s ↔
      passingPattern (fun d => (D d : Set Role)) t =
        passingPattern (fun d => (D d : Set Role)) r ∩ passingPattern (fun d => (D d : Set Role)) s := by
    rw [← Finset.coe_inj, Finset.coe_inter, coe_passingFinset D labels hlabels,
      coe_passingFinset D labels hlabels, coe_passingFinset D labels hlabels]
  simp only [familyEasyB, patternChainB, Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    decide_eq_true_eq, hsubset, heq, hinter, FamilyEasy, PatternChain, PatternIntersectionClosed, RepeatedPattern,
    hroles, true_implies, true_and]

theorem patternChainB_correct [DecidableEq Role] [DecidableEq Label]
    (D : Label → Finset Role) (roles : List Role) (labels : List Label)
    (hroles : ∀ r, r ∈ roles) (hlabels : ∀ d, d ∈ labels) :
    patternChainB D roles labels = true ↔ PatternChain (fun d => (D d : Set Role)) := by
  have hsubset (r s : Role) : passingFinset D labels r ⊆ passingFinset D labels s ↔
      passingPattern (fun d => (D d : Set Role)) r ⊆ passingPattern (fun d => (D d : Set Role)) s := by
    change ((passingFinset D labels r : Set Label) ⊆ (passingFinset D labels s : Set Label)) ↔ _
    rw [coe_passingFinset D labels hlabels, coe_passingFinset D labels hlabels]
  simp only [patternChainB, List.all_eq_true, decide_eq_true_eq, hsubset, PatternChain, hroles, true_implies]

/-- A repeated observer's removal preserves all represented passing patterns. -/
theorem exists_ne_observer_of_repeated (D : Label → Set Role) (k spare : Role)
    (hne : spare ≠ k) (hpattern : passingPattern D spare = passingPattern D k) (r : Role) :
    ∃ s, s ≠ k ∧ passingPattern D s = passingPattern D r := by
  by_cases hr : r = k
  · exact ⟨spare, hne, hpattern.trans (congrArg (passingPattern D) hr).symm⟩
  · exact ⟨r, hr, rfl⟩

/-- Global intersection closure plus a spare observer representative gives
binary intersection closure entirely outside that observer. -/
theorem intersection_closed_off_observer (D : Label → Set Role) (hclosed : PatternIntersectionClosed D)
    (k spare : Role) (hne : spare ≠ k) (hpattern : passingPattern D spare = passingPattern D k)
    (r s : Role) :
    ∃ t, t ≠ k ∧ passingPattern D t = passingPattern D r ∩ passingPattern D s := by
  obtain ⟨t, ht⟩ := hclosed r s
  obtain ⟨t', hne', ht'⟩ := exists_ne_observer_of_repeated D k spare hne hpattern t
  exact ⟨t', hne', ht'.trans ht⟩

/-- Chains remain closed under intersection after removing any observer. -/
theorem chain_intersection_off_observer (D : Label → Set Role) (hchain : PatternChain D)
    (k r s : Role) (hr : r ≠ k) (hs : s ≠ k) :
    ∃ t, t ≠ k ∧ passingPattern D t = passingPattern D r ∩ passingPattern D s := by
  rcases hchain r s with hrs | hsr
  · refine ⟨r, hr, ?_⟩
    ext d
    exact ⟨fun hd => ⟨hd, hrs hd⟩, fun hd => hd.1⟩
  · refine ⟨s, hs, ?_⟩
    ext d
    exact ⟨fun hd => ⟨hsr hd, hd⟩, fun hd => hd.2⟩

@[simp] theorem mem_blockingUnion [DecidableEq Role] (D : Label → Finset Role) (labels : List Label) (r : Role) :
    r ∈ blockingUnion D labels ↔ ∃ d ∈ labels, r ∈ D d := by
  induction labels with
  | nil => simp [blockingUnion]
  | cons d rest ih =>
    simp only [blockingUnion, Finset.mem_union, ih, List.mem_cons]
    constructor
    · rintro (hr | ⟨e, he, hr⟩)
      · exact ⟨d, Or.inl rfl, hr⟩
      · exact ⟨e, Or.inr he, hr⟩
    · rintro ⟨e, he | he, hr⟩
      · subst e; exact Or.inl hr
      · exact Or.inr ⟨e, he, hr⟩

theorem blockingUnion_subset [DecidableEq Role] (D : Label → Finset Role) (top : Finset Role)
    (hD : ∀ d, D d ⊆ top) (labels : List Label) : blockingUnion D labels ⊆ top := by
  intro r hr
  obtain ⟨d, _, hd⟩ := (mem_blockingUnion D labels r).mp hr
  exact hD d hd

/-- Binary represented intersections suffice to represent every nonempty
finite meet, retaining a representative different from the observer. -/
private theorem finite_meet_off_observer (D : Label → Set Role) (k : Role)
    (hclosed : ∀ r, r ≠ k → ∀ s, s ≠ k →
      ∃ t, t ≠ k ∧ passingPattern D t = passingPattern D r ∩ passingPattern D s)
    (roles : List Role) (hne : roles ≠ []) (hoff : ∀ r ∈ roles, r ≠ k) :
    ∃ t, t ≠ k ∧ ∀ d, d ∈ passingPattern D t ↔ ∀ r ∈ roles, d ∈ passingPattern D r := by
  induction roles with
  | nil => exact False.elim (hne rfl)
  | cons r rest ih =>
    have hr := hoff r (List.mem_cons_self ..)
    by_cases he : rest = []
    · subst rest
      exact ⟨r, hr, fun d => by simp⟩
    · obtain ⟨s, hs, hmeet⟩ := ih he (fun t ht => hoff t (List.mem_cons_of_mem _ ht))
      obtain ⟨t, ht, hts⟩ := hclosed r hr s hs
      refine ⟨t, ht, ?_⟩
      intro d
      rw [hts]
      change (d ∈ passingPattern D r ∧ d ∈ passingPattern D s) ↔ _
      rw [hmeet d]
      simp only [List.mem_cons, forall_eq_or_imp]

/-- The exact least-atom property needed by normalized guard comparison.
The union is proper among the observer's other roles, so no empty meet is used. -/
theorem exists_least_atom [DecidableEq Role] (D : Label → Finset Role)
    (k : Role) (roles : List Role) (hroles : ∀ r, r ∈ roles)
    (hD : ∀ d, D d ⊆ roles.toFinset.erase k)
    (hclosed : ∀ r, r ≠ k → ∀ s, s ≠ k →
      ∃ t, t ≠ k ∧ passingPattern (fun d => (D d : Set Role)) t =
        passingPattern (fun d => (D d : Set Role)) r ∩ passingPattern (fun d => (D d : Set Role)) s)
    (labels : List Label) (hproper : blockingUnion D labels ≠ roles.toFinset.erase k) :
    ∃ t, t ≠ k ∧ t ∉ blockingUnion D labels ∧
      ∀ d, t ∉ D d ↔ D d ⊆ blockingUnion D labels := by
  classical
  let U := blockingUnion D labels
  have hU : U ⊆ roles.toFinset.erase k := blockingUnion_subset D _ hD labels
  have hout : ∃ r, r ∈ roles.toFinset.erase k ∧ r ∉ U := by
    by_contra! hn
    exact hproper (Finset.Subset.antisymm hU hn)
  let outside := roles.filter (fun r => r ≠ k ∧ r ∉ U)
  have hmem (r : Role) : r ∈ outside ↔ r ≠ k ∧ r ∉ U := by
    simp only [outside, List.mem_filter, decide_eq_true_eq, hroles r, true_and]
  have hne : outside ≠ [] := by
    obtain ⟨r, hr, hrU⟩ := hout
    have hm := (hmem r).mpr ⟨(Finset.mem_erase.mp hr).1, hrU⟩
    intro he
    rw [he] at hm
    exact List.not_mem_nil hm
  obtain ⟨t, htk, hmeet⟩ := finite_meet_off_observer (fun d => (D d : Set Role)) k hclosed outside hne
    (fun r hr => ((hmem r).mp hr).1)
  have htU : t ∉ U := by
    intro ht
    obtain ⟨d, hd, htd⟩ := (mem_blockingUnion D labels t).mp ht
    have hpass : d ∈ passingPattern (fun d => (D d : Set Role)) t := (hmeet d).mpr (by
      intro r hr hdR
      exact ((hmem r).mp hr).2 ((mem_blockingUnion D labels r).mpr ⟨d, hd, hdR⟩))
    exact hpass htd
  refine ⟨t, htk, htU, ?_⟩
  intro d
  constructor
  · intro htd r hrd
    by_contra hrU
    have hrk : r ≠ k := (Finset.mem_erase.mp (hD d hrd)).1
    have hrOutside := (hmem r).mpr ⟨hrk, hrU⟩
    exact (hmeet d).mp htd r hrOutside hrd
  · intro hd htd
    exact htU (hd htd)

@[simp] theorem passingPattern_erase_observer [DecidableEq Role] (D : Label → Finset Role)
    (k r : Role) (hr : r ≠ k) :
    passingPattern (fun d => (D d |>.erase k : Set Role)) r = passingPattern (fun d => (D d : Set Role)) r := by
  ext d
  simp only [mem_passingPattern, Finset.mem_coe, Finset.mem_erase]
  exact ⟨fun h hd => h ⟨hr, hd⟩, fun h hd => h hd.2⟩

private theorem erase_subset_role_dictionary [DecidableEq Role] (D : Label → Finset Role)
    (k : Role) (roles : List Role) (hroles : ∀ r, r ∈ roles) (d : Label) :
    (D d).erase k ⊆ roles.toFinset.erase k := by
  intro r hr
  exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hr).1, List.mem_toFinset.mpr (hroles r)⟩

/-- The chain case supplies least atoms at every observer. -/
theorem hasLeastAtoms_of_chain [DecidableEq Role] (D : Label → Finset Role)
    (hchain : PatternChain (fun d => (D d : Set Role))) (k : Role) (roles : List Role)
    (hroles : ∀ r, r ∈ roles) :
    HasLeastAtoms (fun d => (D d).erase k) (roles.toFinset.erase k) k := by
  intro labels hp
  apply exists_least_atom (fun d => (D d).erase k) k roles hroles (erase_subset_role_dictionary D k roles hroles) ?_ labels hp
  intro r hr s hs
  obtain ⟨t, ht, he⟩ := chain_intersection_off_observer (fun d => (D d : Set Role)) hchain k r s hr hs
  refine ⟨t, ht, ?_⟩
  rw [passingPattern_erase_observer D k t ht, passingPattern_erase_observer D k r hr,
    passingPattern_erase_observer D k s hs]
  exact he

/-- Intersection closure supplies least atoms at every repeated-pattern observer. -/
theorem hasLeastAtoms_of_intersection_closed [DecidableEq Role] (D : Label → Finset Role)
    (hclosed : PatternIntersectionClosed (fun d => (D d : Set Role)))
    (k spare : Role) (hne : spare ≠ k)
    (hpattern : passingPattern (fun d => (D d : Set Role)) spare = passingPattern (fun d => (D d : Set Role)) k)
    (roles : List Role) (hroles : ∀ r, r ∈ roles) :
    HasLeastAtoms (fun d => (D d).erase k) (roles.toFinset.erase k) k := by
  intro labels hp
  apply exists_least_atom (fun d => (D d).erase k) k roles hroles (erase_subset_role_dictionary D k roles hroles) ?_ labels hp
  intro r hr s hs
  obtain ⟨t, ht, he⟩ := intersection_closed_off_observer (fun d => (D d : Set Role)) hclosed k spare hne hpattern r s
  refine ⟨t, ht, ?_⟩
  rw [passingPattern_erase_observer D k t ht, passingPattern_erase_observer D k r hr,
    passingPattern_erase_observer D k s hs]
  exact he

/-- Both alternatives of the stated family criterion provide the required
least-vector interface, with an explicit repeated observer in the second. -/
theorem familyEasy_least_atoms [DecidableEq Role] (D : Label → Finset Role)
    (roles : List Role) (hroles : ∀ r, r ∈ roles)
    (heasy : FamilyEasy (fun d => (D d : Set Role))) :
    (∀ k, HasLeastAtoms (fun d => (D d).erase k) (roles.toFinset.erase k) k) ∨
      ∃ k spare, spare ≠ k ∧
        passingPattern (fun d => (D d : Set Role)) spare = passingPattern (fun d => (D d : Set Role)) k ∧
        HasLeastAtoms (fun d => (D d).erase k) (roles.toFinset.erase k) k := by
  rcases heasy with hc | ⟨hi, k, spare, hk, he⟩
  · exact Or.inl (fun k => hasLeastAtoms_of_chain D hc k roles hroles)
  · exact Or.inr ⟨k, spare, Ne.symm hk, he.symm,
      hasLeastAtoms_of_intersection_closed D hi k spare (Ne.symm hk) he.symm roles hroles⟩

@[simp] theorem blockingUnion_erase [DecidableEq Role] (D : Label → Finset Role) (k : Role) (labels : List Label) :
    blockingUnion (fun d => (D d).erase k) labels = (blockingUnion D labels).erase k := by
  ext r
  simp only [mem_blockingUnion, Finset.mem_erase]
  constructor
  · rintro ⟨d, hd, hrk, hr⟩
    exact ⟨hrk, d, hd, hr⟩
  · rintro ⟨hrk, d, hd, hr⟩
    exact ⟨d, hd, hrk, hr⟩

private theorem blockingUnion_same_pattern [DecidableEq Role] (D : Label → Finset Role)
    (k spare : Role)
    (hpattern : passingPattern (fun d => (D d : Set Role)) spare = passingPattern (fun d => (D d : Set Role)) k)
    (labels : List Label) : spare ∈ blockingUnion D labels ↔ k ∈ blockingUnion D labels := by
  have h := (passingPattern_eq_iff (fun d => (D d : Set Role)) spare k).mp hpattern
  simp only [mem_blockingUnion]
  constructor
  · rintro ⟨d, hd, hr⟩
    exact ⟨d, hd, (h d).mp hr⟩
  · rintro ⟨d, hd, hr⟩
    exact ⟨d, hd, (h d).mpr hr⟩

/-- At a repeated observer, deleting that observer cannot create an inclusion
between unions of policy sets that was not already true for all roles. -/
theorem erase_union_subset_iff_of_repeated [DecidableEq Role] (D : Label → Finset Role)
    (k spare : Role) (hne : spare ≠ k)
    (hpattern : passingPattern (fun d => (D d : Set Role)) spare = passingPattern (fun d => (D d : Set Role)) k)
    (left right : List Label) :
    blockingUnion (fun d => (D d).erase k) left ⊆ blockingUnion (fun d => (D d).erase k) right ↔
      blockingUnion D left ⊆ blockingUnion D right := by
  rw [blockingUnion_erase, blockingUnion_erase]
  constructor
  · intro h r hr
    by_cases hrk : r = k
    · subst r
      have hsL := (blockingUnion_same_pattern D k spare hpattern left).mpr hr
      have hsR := Finset.mem_erase.mp (h (Finset.mem_erase.mpr ⟨hne, hsL⟩))
      exact (blockingUnion_same_pattern D k spare hpattern right).mp hsR.2
    · exact (Finset.mem_erase.mp (h (Finset.mem_erase.mpr ⟨hrk, hr⟩))).2
  · intro h r hr
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hr).1, h (Finset.mem_erase.mp hr).2⟩

/-- Full-test collisions at a repeated observer are exactly the original
full-role collisions used by the observer-independent compiler. -/
theorem erase_union_full_iff_of_repeated [DecidableEq Role] (D : Label → Finset Role)
    (k spare : Role) (hne : spare ≠ k)
    (hpattern : passingPattern (fun d => (D d : Set Role)) spare = passingPattern (fun d => (D d : Set Role)) k)
    (roles : List Role) (hroles : ∀ r, r ∈ roles) (labels : List Label) :
    blockingUnion (fun d => (D d).erase k) labels = roles.toFinset.erase k ↔ blockingUnion D labels = roles.toFinset := by
  rw [blockingUnion_erase]
  constructor
  · intro he
    apply Finset.Subset.antisymm
    · intro r _; exact List.mem_toFinset.mpr (hroles r)
    · intro r _
      by_cases hr : r = k
      · subst r
        have hs : spare ∈ (blockingUnion D labels).erase k := by
          rw [he]
          exact Finset.mem_erase.mpr ⟨hne, List.mem_toFinset.mpr (hroles spare)⟩
        exact (blockingUnion_same_pattern D k spare hpattern labels).mp (Finset.mem_erase.mp hs).2
      · have hm : r ∈ (blockingUnion D labels).erase k := by
          rw [he]
          exact Finset.mem_erase.mpr ⟨hr, List.mem_toFinset.mpr (hroles r)⟩
        exact (Finset.mem_erase.mp hm).2
  · intro he
    rw [he]

/-- A complete role dictionary denotes the full role universe. -/
theorem coe_role_dictionary [DecidableEq Role] (roles : List Role) (hroles : ∀ r, r ∈ roles) :
    (roles.toFinset : Set Role) = Set.univ := by
  ext r
  simp only [Finset.mem_coe, List.mem_toFinset, hroles r, Set.mem_univ]

/-- Deleting the observer still covers every atom relevant to passing. -/
theorem coe_erased_role_dictionary_cover [DecidableEq Role] (roles : List Role) (hroles : ∀ r, r ∈ roles) (k : Role) :
    (roles.toFinset.erase k : Set Role) ∪ {k} = Set.univ := by
  ext r
  constructor
  · intro _; exact Set.mem_univ r
  · intro _
    by_cases hr : r = k
    · exact Or.inr hr
    · exact Or.inl (Finset.mem_erase.mpr ⟨hr, List.mem_toFinset.mpr (hroles r)⟩)

/-- The repeated observer upgrades the observer-relative least atoms to the
original policies and full-role universe. Thus one common normalized compiler
and comparison is sound for every observer. -/
theorem hasLeastAtoms_original_of_intersection_closed [DecidableEq Role] (D : Label → Finset Role)
    (hclosed : PatternIntersectionClosed (fun d => (D d : Set Role)))
    (k spare : Role) (hne : spare ≠ k)
    (hpattern : passingPattern (fun d => (D d : Set Role)) spare = passingPattern (fun d => (D d : Set Role)) k)
    (roles : List Role) (hroles : ∀ r, r ∈ roles) : HasLeastAtoms D roles.toFinset k := by
  intro labels hp
  have hperase : blockingUnion (fun d => (D d).erase k) labels ≠ roles.toFinset.erase k := by
    intro he
    exact hp ((erase_union_full_iff_of_repeated D k spare hne hpattern roles hroles labels).mp he)
  obtain ⟨t, htk, htU, htest⟩ := hasLeastAtoms_of_intersection_closed D hclosed k spare hne hpattern roles hroles labels hperase
  have htU' : t ∉ blockingUnion D labels := by
    intro ht
    apply htU
    rw [blockingUnion_erase]
    exact Finset.mem_erase.mpr ⟨htk, ht⟩
  refine ⟨t, htk, htU', ?_⟩
  intro d
  have hsub := erase_union_subset_iff_of_repeated D k spare hne hpattern [d] labels
  simp only [blockingUnion, Finset.union_empty] at hsub
  constructor
  · intro ht
    have ht' : t ∉ (D d).erase k := fun h => ht (Finset.mem_erase.mp h).2
    exact hsub.mp ((htest d).mp ht')
  · intro hd ht
    exact htU' (hd ht)

end KFOL.Policies
