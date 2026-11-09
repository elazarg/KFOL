module

public import KFOL.Policies.Coverage

/-! Executable normalized guard comparison and the polynomial family's
complete semantic checker. Machine runtime certification remains separate. -/

@[expose] public section

namespace KFOL.Policies

universe u v w

variable {Role : Type u} {Label : Type w} {Var : Type v} [DecidableEq Role] [DecidableEq Var]

theorem dominatesB_correct (D : Label → Finset Role) (weak strong : Guard Label Var) :
    dominatesB D weak strong = true ↔ weak.Dominates D strong := by
  simp [dominatesB, Guard.Dominates, Bool.and_eq_true, List.all_eq_true, and_assoc]

theorem coversB_correct (D : Label → Finset Role) (left right : List (Guard Label Var)) :
    coversB D left right = true ↔ Covers D left right := by
  simp [coversB, Covers, List.all_eq_true, List.any_eq_true, dominatesB_correct]

namespace Term

/-- Exact observer comparison under the proved least-atom condition. -/
theorem familyObservationB_correct (D : Label → Finset Role) (top : Finset Role)
    (k a b : Role) (hka : k ≠ a) (hkb : k ≠ b) (hab : a ≠ b)
    (hTop : (top : Set Role) ∪ {k} = Set.univ) (htop : top.Nonempty) (hleast : HasLeastAtoms D top k)
    (left right : Term Label Var) :
    familyObservationB D top left right = true ↔ ∀ v : Var → WinnerSet Role,
      k ∈ (left.eval (fun d => (D d : Set Role)) v).val ↔ k ∈ (right.eval (fun d => (D d : Set Role)) v).val := by
  rw [familyObservationB, Bool.and_eq_true, coversB_correct, coversB_correct]
  constructor
  · rintro ⟨hLR, hRL⟩ v
    exact ⟨fun hv => (right.normal_guard_semantics D top k hTop v).mpr
        (covers_sound D _ _ hLR k v ((left.normal_guard_semantics D top k hTop v).mp hv)),
      fun hv => (left.normal_guard_semantics D top k hTop v).mpr
        (covers_sound D _ _ hRL k v ((right.normal_guard_semantics D top k hTop v).mp hv))⟩
  · intro hobs
    constructor
    · apply (covers_iff D top k a b hka hkb hab hleast _ _ (left.normalGuards_normalized D top htop)).mpr
      intro v hv
      exact (right.normal_guard_semantics D top k hTop v).mp
        ((hobs v).mp ((left.normal_guard_semantics D top k hTop v).mpr hv))
    · apply (covers_iff D top k a b hka hkb hab hleast _ _ (right.normalGuards_normalized D top htop)).mpr
      intro v hv
      exact (left.normal_guard_semantics D top k hTop v).mp
        ((hobs v).mpr ((right.normal_guard_semantics D top k hTop v).mpr hv))

/-- On the repeated-pattern branch the same comparison decides the full
algebra at the chosen observer, and coverage remains sound for every observer. -/
theorem familyObservationB_equation_complete (D : Label → Finset Role) (top : Finset Role)
    (k a b : Role) (hka : k ≠ a) (hkb : k ≠ b) (hab : a ≠ b)
    (hTop : (top : Set Role) = Set.univ) (htop : top.Nonempty) (hleast : HasLeastAtoms D top k)
    (left right : Term Label Var) :
    familyObservationB D top left right = true ↔
      ∀ v : Var → WinnerSet Role, left.eval (fun d => (D d : Set Role)) v = right.eval (fun d => (D d : Set Role)) v := by
  have hcover (q : Role) : (top : Set Role) ∪ {q} = Set.univ := by rw [hTop, Set.univ_union]
  constructor
  · intro hb v
    have hc := hb
    rw [familyObservationB, Bool.and_eq_true, coversB_correct, coversB_correct] at hc
    apply Subtype.ext
    ext observer
    exact ⟨fun hv => (right.normal_guard_semantics D top observer (hcover observer) v).mpr
        (covers_sound D _ _ hc.1 observer v ((left.normal_guard_semantics D top observer (hcover observer) v).mp hv)),
      fun hv => (left.normal_guard_semantics D top observer (hcover observer) v).mpr
        (covers_sound D _ _ hc.2 observer v ((right.normal_guard_semantics D top observer (hcover observer) v).mp hv))⟩
  · intro he
    apply (familyObservationB_correct D top k a b hka hkb hab (hcover k) htop hleast left right).mpr
    intro v
    rw [he v]

/-- Full correctness of the actual native checker in both stated tractable
cases. The family criterion and the equation program are independent definitions. -/
theorem familyEquationB_correct [DecidableEq Label] (three : Fin 3 ↪ Role)
    (D : Label → Finset Role) (roles : List Role) (labels : List Label)
    (hroles : ∀ r, r ∈ roles) (hlabels : ∀ d, d ∈ labels)
    (heasy : FamilyEasy (fun d => (D d : Set Role))) (left right : Term Label Var) :
    familyEquationB D roles labels left right = true ↔
      ∀ v : Var → WinnerSet Role, left.eval (fun d => (D d : Set Role)) v = right.eval (fun d => (D d : Set Role)) v := by
  have hothers (k : Role) : ∃ a b, k ≠ a ∧ k ≠ b ∧ a ≠ b := by
    obtain ⟨a, hak, _⟩ := exists_role_outside_pair three k k
    obtain ⟨b, hbk, hba⟩ := exists_role_outside_pair three k a
    exact ⟨a, b, Ne.symm hak, Ne.symm hbk, Ne.symm hba⟩
  unfold familyEquationB
  split
  next hc =>
    have hchain := (patternChainB_correct D roles labels hroles hlabels).mp hc
    have hobs (k : Role) : familyObservationB (fun d => (D d).erase k) (roles.toFinset.erase k) left right = true ↔
        ∀ v : Var → WinnerSet Role,
          k ∈ (left.eval (fun d => (D d : Set Role)) v).val ↔ k ∈ (right.eval (fun d => (D d : Set Role)) v).val := by
      obtain ⟨a, b, hka, hkb, hab⟩ := hothers k
      have htop : (roles.toFinset.erase k).Nonempty :=
        ⟨a, Finset.mem_erase.mpr ⟨Ne.symm hka, List.mem_toFinset.mpr (hroles a)⟩⟩
      have hcheck := familyObservationB_correct (fun d => (D d).erase k) (roles.toFinset.erase k) k a b hka hkb hab
        (coe_erased_role_dictionary_cover roles hroles k) htop (hasLeastAtoms_of_chain D hchain k roles hroles) left right
      simpa only [← observation_erase D k] using hcheck
    rw [List.all_eq_true]
    constructor
    · intro h v
      apply Subtype.ext
      ext k
      exact (hobs k).mp (h k (hroles k)) v
    · intro he k _
      apply (hobs k).mpr
      intro v
      rw [he v]
  next hc =>
    have hnchain : ¬PatternChain (fun d => (D d : Set Role)) := fun h => hc ((patternChainB_correct D roles labels hroles hlabels).mpr h)
    obtain ⟨hclosed, k, spare, hne, hpattern⟩ := heasy.resolve_left hnchain
    obtain ⟨a, b, hka, hkb, hab⟩ := hothers k
    have htop : roles.toFinset.Nonempty := ⟨a, List.mem_toFinset.mpr (hroles a)⟩
    exact familyObservationB_equation_complete D roles.toFinset k a b hka hkb hab (coe_role_dictionary roles hroles) htop
      (hasLeastAtoms_original_of_intersection_closed D hclosed k spare (Ne.symm hne) hpattern.symm roles hroles) left right

/-- Every repeated-pattern observer is equation-complete on the
intersection-closed branch, as asserted in the main family theorem. -/
theorem repeated_observer_equation_complete (three : Fin 3 ↪ Role)
    (D : Label → Finset Role) (roles : List Role) (hroles : ∀ r, r ∈ roles)
    (hclosed : PatternIntersectionClosed (fun d => (D d : Set Role)))
    (k spare : Role) (hne : spare ≠ k)
    (hpattern : passingPattern (fun d => (D d : Set Role)) spare = passingPattern (fun d => (D d : Set Role)) k)
    (left right : Term Label Var) :
    (∀ v : Var → WinnerSet Role, left.eval (fun d => (D d : Set Role)) v = right.eval (fun d => (D d : Set Role)) v) ↔
      ∀ v : Var → WinnerSet Role,
        k ∈ (left.eval (fun d => (D d : Set Role)) v).val ↔ k ∈ (right.eval (fun d => (D d : Set Role)) v).val := by
  obtain ⟨a, hak, _⟩ := exists_role_outside_pair three k k
  obtain ⟨b, hbk, hba⟩ := exists_role_outside_pair three k a
  have ht : roles.toFinset.Nonempty := ⟨a, List.mem_toFinset.mpr (hroles a)⟩
  have hT := coe_role_dictionary roles hroles
  have hcover : (roles.toFinset : Set Role) ∪ {k} = Set.univ := by rw [hT, Set.univ_union]
  have hleast := hasLeastAtoms_original_of_intersection_closed D hclosed k spare hne hpattern roles hroles
  exact (familyObservationB_equation_complete D roles.toFinset k a b (Ne.symm hak) (Ne.symm hbk) (Ne.symm hba)
    hT ht hleast left right).symm.trans
      (familyObservationB_correct D roles.toFinset k a b (Ne.symm hak) (Ne.symm hbk) (Ne.symm hba) hcover ht hleast left right)

/-- A failed normalized comparison supplies an actual atom-or-pair valuation
at which the two native observations differ. No unconnected certificate is used. -/
theorem familyObservation_countervaluation (D : Label → Finset Role) (top : Finset Role)
    (k a b : Role) (hka : k ≠ a) (hkb : k ≠ b) (hab : a ≠ b)
    (hTop : (top : Set Role) ∪ {k} = Set.univ) (htop : top.Nonempty) (hleast : HasLeastAtoms D top k)
    (left right : Term Label Var) (hfalse : familyObservationB D top left right = false) :
    ∃ v : Var → WinnerSet Role,
      ((k ∈ (left.eval (fun d => (D d : Set Role)) v).val ∧ k ∉ (right.eval (fun d => (D d : Set Role)) v).val) ∨
        (k ∈ (right.eval (fun d => (D d : Set Role)) v).val ∧ k ∉ (left.eval (fun d => (D d : Set Role)) v).val)) ∧
      (∀ i : Var, ∃ r s : Role, v i = (WinnerSet.singleton r).union (WinnerSet.singleton s)) := by
  classical
  have hn : ¬(Covers D (left.normalGuards D top) (right.normalGuards D top) ∧
      Covers D (right.normalGuards D top) (left.normalGuards D top)) := by
    intro hh
    have ht : familyObservationB D top left right = true := by
      simpa only [familyObservationB, Bool.and_eq_true, coversB_correct] using hh
    cases hfalse.symm.trans ht
  have hdir (s t : Term Label Var) (hst : ¬Covers D (s.normalGuards D top) (t.normalGuards D top)) :
      ∃ v : Var → WinnerSet Role,
        k ∈ (s.eval (fun d => (D d : Set Role)) v).val ∧ k ∉ (t.eval (fun d => (D d : Set Role)) v).val ∧
        (∀ i : Var, ∃ r s : Role, v i = (WinnerSet.singleton r).union (WinnerSet.singleton s)) := by
    have hg : ¬∀ g ∈ s.normalGuards D top, ∃ weak ∈ t.normalGuards D top, weak.Dominates D g := hst
    push Not at hg
    obtain ⟨g, hg, hn⟩ := hg
    obtain ⟨v, hv, hpairs⟩ := g.exists_least_valuation D top k a b hka hkb hab hleast (s.normalGuards_normalized D top htop g hg)
    have hself : g.Dominates D g := by
      refine ⟨rfl, (fun _ h => h), ?_⟩
      rintro ⟨d, i⟩ hp
      exact Or.inr (Or.inr (g.label_subset_blockingAt D d i hp))
    refine ⟨v, (s.normal_guard_semantics D top k hTop v).mpr ⟨g, hg, (hv g).mpr hself⟩, ?_, hpairs⟩
    intro ht
    obtain ⟨weak, hw, hholds⟩ := (t.normal_guard_semantics D top k hTop v).mp ht
    exact hn weak hw ((hv weak).mp hholds)
  by_cases hLR : Covers D (left.normalGuards D top) (right.normalGuards D top)
  · obtain ⟨v, hr, hl, hpairs⟩ := hdir right left (fun hRL => hn ⟨hLR, hRL⟩)
    exact ⟨v, Or.inr ⟨hr, hl⟩, hpairs⟩
  · obtain ⟨v, hl, hr, hpairs⟩ := hdir left right hLR
    exact ⟨v, Or.inl ⟨hl, hr⟩, hpairs⟩

/-- Every rejection by the tractable-family native checker has a concrete
countervaluation with at most two winners at each original input. -/
theorem familyEquation_countervaluation [DecidableEq Label] (three : Fin 3 ↪ Role)
    (D : Label → Finset Role) (roles : List Role) (labels : List Label)
    (hroles : ∀ r, r ∈ roles) (hlabels : ∀ d, d ∈ labels)
    (heasy : FamilyEasy (fun d => (D d : Set Role))) (left right : Term Label Var)
    (hfalse : familyEquationB D roles labels left right = false) :
    ∃ v : Var → WinnerSet Role,
      left.eval (fun d => (D d : Set Role)) v ≠ right.eval (fun d => (D d : Set Role)) v ∧
      (∀ i : Var, ∃ r s : Role, v i = (WinnerSet.singleton r).union (WinnerSet.singleton s)) := by
  classical
  have hothers (k : Role) : ∃ a b, k ≠ a ∧ k ≠ b ∧ a ≠ b := by
    obtain ⟨a, hak, _⟩ := exists_role_outside_pair three k k
    obtain ⟨b, hbk, hba⟩ := exists_role_outside_pair three k a
    exact ⟨a, b, Ne.symm hak, Ne.symm hbk, Ne.symm hba⟩
  unfold familyEquationB at hfalse
  split at hfalse
  next hc =>
    have hchain := (patternChainB_correct D roles labels hroles hlabels).mp hc
    obtain ⟨k, _, hk⟩ := List.all_eq_false.mp hfalse
    have hkfalse := Bool.eq_false_iff.mpr hk
    obtain ⟨a, b, hka, hkb, hab⟩ := hothers k
    have ht : (roles.toFinset.erase k).Nonempty := ⟨a, Finset.mem_erase.mpr ⟨Ne.symm hka, List.mem_toFinset.mpr (hroles a)⟩⟩
    obtain ⟨v, hsep, hpairs⟩ := familyObservation_countervaluation (fun d => (D d).erase k) (roles.toFinset.erase k)
      k a b hka hkb hab (coe_erased_role_dictionary_cover roles hroles k) ht (hasLeastAtoms_of_chain D hchain k roles hroles) left right hkfalse
    refine ⟨v, ?_, hpairs⟩
    intro he
    have hobs : k ∈ (left.eval (fun d => ((D d).erase k : Set Role)) v).val ↔
        k ∈ (right.eval (fun d => ((D d).erase k : Set Role)) v).val := by
      rw [← observation_erase D k, ← observation_erase D k, he]
    rcases hsep with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · exact hr (hobs.mp hl)
    · exact hl (hobs.mpr hr)
  next hc =>
    have hnchain : ¬PatternChain (fun d => (D d : Set Role)) := fun h => hc ((patternChainB_correct D roles labels hroles hlabels).mpr h)
    obtain ⟨hi, k, spare, hne, hpattern⟩ := heasy.resolve_left hnchain
    obtain ⟨a, b, hka, hkb, hab⟩ := hothers k
    have ht : roles.toFinset.Nonempty := ⟨a, List.mem_toFinset.mpr (hroles a)⟩
    have hT : (roles.toFinset : Set Role) ∪ {k} = Set.univ := by rw [coe_role_dictionary roles hroles, Set.univ_union]
    obtain ⟨v, hsep, hpairs⟩ := familyObservation_countervaluation D roles.toFinset k a b hka hkb hab hT ht
      (hasLeastAtoms_original_of_intersection_closed D hi k spare (Ne.symm hne) hpattern.symm roles hroles) left right hfalse
    refine ⟨v, ?_, hpairs⟩
    intro he
    rcases hsep with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · exact hr (he ▸ hl)
    · exact hl (he.symm ▸ hr)

end Term
end KFOL.Policies
