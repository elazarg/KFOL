module

public import KFOL.Core.IntervalRecognition
public import KFOL.Algebra.Monotone

/-! # The greatest core minorant of an interval-mask operation

Path saturation computes the greatest core operation below the prescribed
mask, including comparisons with core operations outside the mask fragment.
-/

@[expose] public section
namespace KFOL.Core.Intervals
universe u v
variable {Role : Type u} {Var : Type v} [Fintype Var] [Nonempty Var]

/-- Every proper mask respects the full union of its inputs. -/
theorem operation_subset_inputUnion (b c : Role)
    (selected : Set (Finset Var × Finset Var)) (hp : Proper selected)
    (values : Var → WinnerSet Role) :
    (operation b c selected values).val ⊆ (inputUnion values).val := by
  classical
  unfold operation
  split_ifs with hsel
  · have hc := (hp _ _ hsel).1
    obtain ⟨j,hj⟩ := hc
    have hjc : values j = WinnerSet.singleton c := by
      simpa only [lowerInputs,Finset.mem_filter,Finset.mem_univ,true_and] using hj
    have hb : ∃ i, values i = WinnerSet.singleton b := by
      by_contra! hn
      apply (hp _ _ hsel).2.2
      apply Finset.eq_univ_iff_forall.mpr
      intro i
      simp [upperInputs,hn i]
    obtain ⟨i,hib⟩ := hb
    intro r hr
    rcases hr with hr | hr
    · exact Set.mem_iUnion.mpr ⟨i,by simpa only [hib] using hr⟩
    · exact Set.mem_iUnion.mpr ⟨j,by simpa only [hjc] using hr⟩
  · exact Set.Subset.rfl

/-- Enlarging the selected family decreases the associated operation. -/
theorem operation_antitone (b c : Role)
    {selected other : Set (Finset Var × Finset Var)} (hsub : selected ⊆ other)
    (hp : Proper other) (values : Var → WinnerSet Role) :
    (operation b c other values).val ⊆ (operation b c selected values).val := by
  classical
  by_cases hs : (lowerInputs c values,upperInputs b values) ∈ selected
  · have ho := hsub hs
    simp only [operation,ite_eq_left hs,ite_eq_left ho]
    exact Set.Subset.rfl
  · simpa only [operation,ite_eq_right hs] using operation_subset_inputUnion b c other hp values

private theorem atomic_saturation_omission (three : Fin 3 ↪ Role)
    (selected : Set (Finset Var × Finset Var)) (hp : Proper selected)
    (t : Term Role Var) (ht : t.IsCore)
    (hle : ∀ values, (t.eval values).val ⊆
      (operation (three 1) (three 2) selected values).val)
    {L U : Finset Var} (hs : (L,U) ∈ saturation selected) :
    three 0 ∉ (t.eval (AtomicObserver.values three L U)).val := by
  let h (L U : Finset Var) : Prop :=
    three 0 ∈ (t.eval (AtomicObserver.values three L U)).val
  have ha : AtomicObserver.Admissible h :=
    (AtomicObserver.admissible_iff_embedding three h).mpr
      ⟨t,ht,fun _ _ _ => Iff.rfl⟩
  have hz (A B : Finset Var) (hm : (A,B) ∈ selected) : ¬h A B := by
    intro hh
    exact ((atomic_mem_operation three selected A B
      (Finset.ssubset_iff_subset_ne.mp (hp A B hm).2.1).1).mp (hle _ hh)).2 hm
  have hmap {A B : Finset Var} (hr : Reach selected A B) :
      AtomicObserver.Reach h A B := by
    induction hr with
    | refl => exact Relation.ReflTransGen.refl
    | @tail T V hAT hTV ih =>
      apply ih.tail
      rcases hTV with hinc | hsel
      · exact Or.inl hinc
      · exact Or.inr ⟨(Finset.ssubset_iff_subset_ne.mp (hp V T hsel).2.1).1,hz V T hsel⟩
  intro hh
  exact ha.2 L U (Finset.ssubset_iff_subset_ne.mp hs.1.2.1).1 hh (hmap hs.2)

private theorem sameView_of_mem (k : Role) (A B : WinnerSet Role)
    (hA : k ∈ A.val) (hB : k ∈ B.val) : WinnerSet.SameView k A B := by
  apply (WinnerSet.view_eq_view_iff k A B).mp
  exact ((WinnerSet.view_eq_possible_iff k A).mpr hA).trans
    ((WinnerSet.view_eq_possible_iff k B).mpr hB).symm

omit [Nonempty Var] in
private theorem omission_of_atomic (three : Fin 3 ↪ Role)
    (t : Term Role Var) (ht : t.IsCore) (values : Var → WinnerSet Role)
    (ha : three 0 ∉ (t.eval (AtomicObserver.values three
      (lowerInputs (three 2) values) (upperInputs (three 1) values))).val) :
    three 0 ∉ (t.eval values).val := by
  classical
  let L := lowerInputs (three 2) values
  let U := upperInputs (three 1) values
  let w (j : Var) : WinnerSet Role :=
    if j ∈ L then WinnerSet.singleton (three 2)
    else if j ∈ U then (values j).union (WinnerSet.singleton (three 0))
    else WinnerSet.singleton (three 1)
  have hsub (j : Var) : (values j).val ⊆ (w j).val := by
    by_cases hjL : j ∈ L
    · have he : values j = WinnerSet.singleton (three 2) := by
        simpa only [L,lowerInputs,Finset.mem_filter,Finset.mem_univ,true_and] using hjL
      simp only [w,ite_eq_left hjL,he]
      exact Set.Subset.rfl
    · by_cases hjU : j ∈ U
      · simp only [w,ite_eq_right hjL,ite_eq_left hjU]
        exact Set.subset_union_left
      · have he : values j = WinnerSet.singleton (three 1) := by
          simpa only [U,upperInputs,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hjU
        simp only [w,ite_eq_right hjL,ite_eq_right hjU,he]
        exact Set.Subset.rfl
  have hv (j : Var) : WinnerSet.SameView (three 0) (w j)
      (AtomicObserver.values three L U j) := by
    by_cases hjL : j ∈ L
    · simp only [w,AtomicObserver.values,ite_eq_left hjL]
      exact ⟨Iff.rfl,fun _ _ => Iff.rfl⟩
    · by_cases hjU : j ∈ U
      · apply sameView_of_mem
        · simp [w,hjL,hjU]
        · simp [AtomicObserver.values,hjL,hjU]
      · simp only [w,AtomicObserver.values,ite_eq_right hjL,ite_eq_right hjU]
        exact ⟨Iff.rfl,fun _ _ => Iff.rfl⟩
  intro hh
  exact ha ((ht.isPublic.eval_sameView (three 0) w _ hv).1.mp ((t.eval_mono hsub) hh))

/-- Every core minorant of a mask is below its path saturation, on full menus. -/
theorem minorant_subset_saturation (three : Fin 3 ↪ Role)
    (selected : Set (Finset Var × Finset Var)) (hp : Proper selected)
    (t : Term Role Var) (ht : t.IsCore)
    (hle : ∀ values, (t.eval values).val ⊆
      (operation (three 1) (three 2) selected values).val) (values : Var → WinnerSet Role) :
    (t.eval values).val ⊆
      (operation (three 1) (three 2) (saturation selected) values).val := by
  classical
  by_cases hs : (lowerInputs (three 2) values,upperInputs (three 1) values) ∈ saturation selected
  · rw [operation,ite_eq_left hs]
    intro k hk
    by_cases hkb : k = three 1
    · exact Or.inl (by simp [hkb])
    · by_cases hkc : k = three 2
      · exact Or.inr (by simp [hkc])
      · let e : Fin 3 ↪ Role := ⟨![k,three 1,three 2],by
          intro i j hij
          fin_cases i <;> fin_cases j <;> simp_all [three.injective.eq_iff]⟩
        have hs' : (lowerInputs (e 2) values,upperInputs (e 1) values) ∈ saturation selected := hs
        have he : ∀ v, (t.eval v).val ⊆ (operation (e 1) (e 2) selected v).val := hle
        exact (omission_of_atomic e t ht values
          (atomic_saturation_omission e selected hp t ht he hs')) hk |>.elim
  · simpa only [operation,ite_eq_right hs] using
      (hle values).trans (operation_subset_inputUnion _ _ selected hp values)

/-- Saturation is the greatest core minorant, even among operations outside
this interval-mask fragment. -/
theorem exists_greatest_minorant [Fintype Role] (three : Fin 3 ↪ Role)
    (selected : Set (Finset Var × Finset Var)) (hp : Proper selected) :
    ∃ t : Term Role Var, t.IsCore ∧
      (∀ values, t.eval values = operation (three 1) (three 2) (saturation selected) values) ∧
      (∀ values, (t.eval values).val ⊆ (operation (three 1) (three 2) selected values).val) ∧
      ∀ s : Term Role Var, s.IsCore →
        (∀ values, (s.eval values).val ⊆ (operation (three 1) (three 2) selected values).val) →
        ∀ values, (s.eval values).val ⊆ (t.eval values).val := by
  obtain ⟨t,ht,he⟩ := exists_saturation_term three selected
  refine ⟨t,ht,he,?_,?_⟩
  · intro values
    rw [he]
    exact operation_antitone _ _ (subset_saturation hp) (proper_saturation selected) values
  · intro s hs hle values
    rw [he]
    exact minorant_subset_saturation three selected hp s hs hle values

omit [Fintype Var] [Nonempty Var] in
private theorem choice_pair_eq_of_subset (b c r : Role) (hbc : b ≠ c)
    (W : WinnerSet Role)
    (hsub : ((WinnerSet.singleton b).union (WinnerSet.singleton c)).val ⊆ W.val) :
    WinnerSet.choice r ((WinnerSet.singleton b).union (WinnerSet.singleton c)) W = W := by
  classical
  have hpair := WinnerSet.ambiguous_of_two_mem
    ((WinnerSet.singleton b).union (WinnerSet.singleton c)) b c hbc (by simp) (by simp)
  have hW := WinnerSet.ambiguous_of_two_mem W b c hbc (hsub (by simp)) (hsub (by simp))
  rw [WinnerSet.choice,ite_eq_right (fun h => h.elim (hpair r) (hW r))]
  exact Subtype.ext (Set.union_eq_right.mpr hsub)

/-- Every owned choice on interval masks is intersection of their mask families. -/
theorem choice_operation (b c r : Role) (hbc : b ≠ c)
    (selected other : Set (Finset Var × Finset Var))
    (hp : Proper selected) (ho : Proper other) (values : Var → WinnerSet Role) :
    WinnerSet.choice r (operation b c selected values) (operation b c other values) =
      operation b c (selected ∩ other) values := by
  classical
  by_cases hs : (lowerInputs c values,upperInputs b values) ∈ selected
  · by_cases ht : (lowerInputs c values,upperInputs b values) ∈ other
    · simp [operation,hs,ht]
    · have hsub : ((WinnerSet.singleton b).union (WinnerSet.singleton c)).val ⊆
          (inputUnion values).val := by
        simpa only [operation,ite_eq_left hs] using operation_subset_inputUnion b c selected hp values
      simpa only [operation,Set.mem_inter_iff,hs,ht,true_and,and_false,ite_true,ite_false] using
        choice_pair_eq_of_subset b c r hbc (inputUnion values) hsub
  · by_cases ht : (lowerInputs c values,upperInputs b values) ∈ other
    · have hsub : ((WinnerSet.singleton b).union (WinnerSet.singleton c)).val ⊆
          (inputUnion values).val := by
        simpa only [operation,ite_eq_left ht] using operation_subset_inputUnion b c other ho values
      rw [WinnerSet.choice_comm]
      simpa only [operation,Set.mem_inter_iff,hs,ht,false_and,ite_true,ite_false] using
        choice_pair_eq_of_subset b c r hbc (inputUnion values) hsub
    · simp [operation,hs,ht]

/-- Pointwise set intersection corresponds to union of the prescribed masks. -/
theorem operation_inter (b c : Role)
    (selected other : Set (Finset Var × Finset Var))
    (hp : Proper selected) (ho : Proper other) (values : Var → WinnerSet Role) :
    (operation b c selected values).val ∩ (operation b c other values).val =
      (operation b c (selected ∪ other) values).val := by
  classical
  by_cases hs : (lowerInputs c values,upperInputs b values) ∈ selected
  · have hsub : ((WinnerSet.singleton b).union (WinnerSet.singleton c)).val ⊆
        (inputUnion values).val := by
      simpa only [operation,ite_eq_left hs] using operation_subset_inputUnion b c selected hp values
    by_cases ht : (lowerInputs c values,upperInputs b values) ∈ other
    · simp [operation,hs,ht]
    · simpa only [operation,Set.mem_union,hs,ht,true_or,ite_true,ite_false] using
        Set.inter_eq_left.mpr hsub
  · by_cases ht : (lowerInputs c values,upperInputs b values) ∈ other
    · have hsub : ((WinnerSet.singleton b).union (WinnerSet.singleton c)).val ⊆
          (inputUnion values).val := by
        simpa only [operation,ite_eq_left ht] using operation_subset_inputUnion b c other ho values
      simpa only [operation,Set.mem_union,hs,ht,false_or,ite_true,ite_false] using
        Set.inter_eq_right.mpr hsub
    · simp [operation,hs,ht]

/-- Saturating the union of two masks gives their greatest common core
minorant, without requiring either prescribed mask to be realizable. -/
theorem exists_greatest_common_minorant [Fintype Role] (three : Fin 3 ↪ Role)
    (selected other : Set (Finset Var × Finset Var))
    (hp : Proper selected) (ho : Proper other) :
    ∃ t : Term Role Var, t.IsCore ∧
      (∀ values, t.eval values =
        operation (three 1) (three 2) (saturation (selected ∪ other)) values) ∧
      (∀ values, (t.eval values).val ⊆ (operation (three 1) (three 2) selected values).val ∧
        (t.eval values).val ⊆ (operation (three 1) (three 2) other values).val) ∧
      ∀ s : Term Role Var, s.IsCore →
        (∀ values, (s.eval values).val ⊆ (operation (three 1) (three 2) selected values).val) →
        (∀ values, (s.eval values).val ⊆ (operation (three 1) (three 2) other values).val) →
        ∀ values, (s.eval values).val ⊆ (t.eval values).val := by
  have hproper : Proper (selected ∪ other) := by
    intro L U h
    exact h.elim (hp L U) (ho L U)
  obtain ⟨t,ht,he,hl,hm⟩ := exists_greatest_minorant three (selected ∪ other) hproper
  refine ⟨t,ht,he,?_,?_⟩
  · intro values
    have hb := hl values
    rw [← operation_inter _ _ selected other hp ho values] at hb
    exact ⟨hb.trans Set.inter_subset_left,hb.trans Set.inter_subset_right⟩
  · intro s hs hselected hother
    apply hm s hs
    intro values
    rw [← operation_inter _ _ selected other hp ho values]
    exact Set.subset_inter (hselected values) (hother values)

end KFOL.Core.Intervals
