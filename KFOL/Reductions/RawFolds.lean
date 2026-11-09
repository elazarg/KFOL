module

public import KFOL.Reductions.ResetUnionCorrectness
public import KFOL.Algebra.Views
public import Mathlib.Data.List.Fold

/-! Value-fold lemmas for the native hard raw binary pairs. -/

@[expose] public section

namespace KFOL.Reductions.RawPair

universe u

variable {Role : Type u}

@[simp] theorem mem_unions (xs : List (WinnerSet Role)) (base : WinnerSet Role) (w : Role) :
    w ∈ (unions xs base).val ↔ w ∈ base.val ∨ ∃ X ∈ xs, w ∈ X.val := by
  induction xs with
  | nil => simp [unions]
  | cons X xs ih =>
    change w ∈ X.val ∨ w ∈ (unions xs base).val ↔ _
    rw [ih]
    simp only [List.mem_cons]
    grind

@[simp] theorem choiceFold_eq_owner (a : Role) (xs : List (WinnerSet Role)) (base : WinnerSet Role) :
    choiceFold a xs base = WinnerSet.singleton a ↔
      base = WinnerSet.singleton a ∨ ∃ X ∈ xs, X = WinnerSet.singleton a := by
  induction xs with
  | nil => simp [choiceFold]
  | cons X xs ih =>
    rw [choiceFold, List.foldr_cons, WinnerSet.choice_eq_owner_iff]
    change X = WinnerSet.singleton a ∨ choiceFold a xs base = WinnerSet.singleton a ↔ _
    rw [ih]
    simp only [List.mem_cons]
    grind

@[simp] theorem choiceFold_eq_other (a r : Role) (har : a ≠ r)
    (xs : List (WinnerSet Role)) (base : WinnerSet Role) :
    choiceFold a xs base = WinnerSet.singleton r ↔
      base = WinnerSet.singleton r ∧ ∀ X ∈ xs, X = WinnerSet.singleton r := by
  induction xs with
  | nil => simp [choiceFold]
  | cons X xs ih =>
    change WinnerSet.choice a X (choiceFold a xs base) = WinnerSet.singleton r ↔ _
    rw [WinnerSet.choice_eq_other_iff (A := X) (B := choiceFold a xs base) (r := a) har]
    rw [ih]
    simp only [List.forall_mem_cons]
    tauto

theorem choiceFold_union (a : Role) (xs : List (WinnerSet Role)) (base : WinnerSet Role)
    (hb : base ≠ WinnerSet.singleton a) (hx : ∀ X ∈ xs, X ≠ WinnerSet.singleton a) :
    choiceFold a xs base = unions xs base := by
  induction xs with
  | nil => rfl
  | cons X xs ih =>
    have ht : ∀ Y ∈ xs, Y ≠ WinnerSet.singleton a := fun Y h => hx Y (List.mem_cons_of_mem _ h)
    have hrest : choiceFold a xs base ≠ WinnerSet.singleton a := by
      intro he
      rcases (choiceFold_eq_owner a xs base).mp he with h | ⟨Y, hY, h⟩
      · exact hb h
      · exact ht Y hY h
    change WinnerSet.choice a X (choiceFold a xs base) = X.union (unions xs base)
    simp only [WinnerSet.choice, hx X (List.mem_cons_self ..), hrest, or_self, ite_false]
    rw [ih ht]

/-- The common subset argument for a raw owner together with native union,
and for two owners after the outer owner's absorbing cases are excluded. -/
theorem raw_absorption (a : Role) (pairs : List (WinnerSet Role × WinnerSet Role))
    (clauses : List (WinnerSet Role)) (M W : WinnerSet Role)
    (hpairs : pairs ≠ []) (hc : ∀ C ∈ clauses, C.val ⊆ W.val)
    (hlogic : (∀ C ∈ clauses, C ≠ WinnerSet.singleton a) →
      ∃ pair ∈ pairs, pair.1 ≠ WinnerSet.singleton a ∧ pair.2 ≠ WinnerSet.singleton a) :
    (choiceFold a clauses M).val ⊆
      (unions (pairs.map (fun pair => WinnerSet.choice a M (WinnerSet.choice a pair.1 pair.2))) W).val := by
  let R := unions (pairs.map (fun pair => WinnerSet.choice a M (WinnerSet.choice a pair.1 pair.2))) W
  have hWR : W.val ⊆ R.val := fun w hw => (mem_unions _ W w).mpr (Or.inl hw)
  have hMR : M ≠ WinnerSet.singleton a → (∀ C ∈ clauses, C ≠ WinnerSet.singleton a) → M.val ⊆ R.val := by
    intro _ hcs w hM
    obtain ⟨pair, hp, hp₁, hp₂⟩ := hlogic hcs
    have hn : WinnerSet.choice a pair.1 pair.2 ≠ WinnerSet.singleton a := by
      intro he
      rcases (WinnerSet.choice_eq_owner_iff pair.1 pair.2 a).mp he with he | he
      · exact hp₁ he
      · exact hp₂ he
    apply (mem_unions _ W w).mpr
    exact Or.inr ⟨_, List.mem_map.mpr ⟨pair, hp, rfl⟩,
      WinnerSet.subset_choice_of_right_ne a M _ hn hM⟩
  by_cases he : choiceFold a clauses M = WinnerSet.singleton a
  · intro w hw
    have hwa : w = a := by simpa only [he, WinnerSet.val_singleton, Set.mem_singleton_iff] using hw
    subst w
    rcases (choiceFold_eq_owner a clauses M).mp he with hM | ⟨C, hC, hCa⟩
    · obtain ⟨pair, hp⟩ := List.exists_mem_of_ne_nil pairs hpairs
      apply (mem_unions _ W a).mpr
      refine Or.inr ⟨_, List.mem_map.mpr ⟨pair, hp, rfl⟩, ?_⟩
      rw [WinnerSet.mem_choice_owner, hM]
      exact Or.inl rfl
    · exact hWR (hc C hC (hCa.symm ▸ (rfl : a ∈ (WinnerSet.singleton a).val)))
  · have hnone := mt (choiceFold_eq_owner a clauses M).mpr he
    have hm : M ≠ WinnerSet.singleton a := fun h => hnone (Or.inl h)
    have hs : ∀ C ∈ clauses, C ≠ WinnerSet.singleton a :=
      fun C hC h => hnone (Or.inr ⟨C, hC, h⟩)
    rw [choiceFold_union a clauses M hm hs]
    intro w hw
    rcases (mem_unions clauses M w).mp hw with hw | ⟨C, hC, hw⟩
    · exact hMR hm hs hw
    · exact hWR (hc C hC hw)

end KFOL.Reductions.RawPair

namespace KFOL.Reductions.RawPair

universe u

@[simp] theorem unions_eq_singleton {Role : Type u} (xs : List (WinnerSet Role))
    (base : WinnerSet Role) (r : Role) :
    unions xs base = WinnerSet.singleton r ↔
      base = WinnerSet.singleton r ∧ ∀ X ∈ xs, X = WinnerSet.singleton r := by
  induction xs with
  | nil => simp [unions]
  | cons X xs ih =>
    change X.union (unions xs base) = WinnerSet.singleton r ↔ _
    rw [WinnerSet.union_eq_singleton_iff, ih]
    simp only [List.forall_mem_cons]
    tauto

end KFOL.Reductions.RawPair

namespace KFOL.Reductions.RawPair

universe u

variable {Role : Type u}

private theorem ambiguous_union_singleton (X : WinnerSet Role) (r : Role) :
    (X.union (WinnerSet.singleton r)).Ambiguous ↔ X ≠ WinnerSet.singleton r := by
  constructor
  · intro h he
    rw [he, WinnerSet.union_self] at h
    exact h r rfl
  · intro h s he
    obtain ⟨hX, hr⟩ := (WinnerSet.union_eq_singleton_iff _ _ s).mp he
    exact h (hX.trans hr.symm)

/-- An ambiguous nonempty owned clause has an ambiguous literal/T guard.
This avoids the false inference that T itself must be atomic. -/
theorem choiceFold_ambiguous_witness (a : Role) (xs : List (WinnerSet Role)) (T : WinnerSet Role)
    (hne : xs ≠ []) (hm : (choiceFold a xs T).Ambiguous) :
    ∃ X ∈ xs, (WinnerSet.choice a X T).Ambiguous := by
  classical
  have hnot : choiceFold a xs T ≠ WinnerSet.singleton a := hm a
  have hT : T ≠ WinnerSet.singleton a := fun he => hnot ((choiceFold_eq_owner a xs T).mpr (Or.inl he))
  have hxs : ∀ X ∈ xs, X ≠ WinnerSet.singleton a :=
    fun X hX he => hnot ((choiceFold_eq_owner a xs T).mpr (Or.inr ⟨X, hX, he⟩))
  rw [choiceFold_union a xs T hT hxs] at hm
  by_cases hTm : T.Ambiguous
  · obtain ⟨X, hX⟩ := List.exists_mem_of_ne_nil xs hne
    refine ⟨X, hX, ?_⟩
    simp only [WinnerSet.choice, hxs X hX, hT, or_self, ite_false]
    rw [WinnerSet.union_comm]
    exact hTm.union_left
  · unfold WinnerSet.Ambiguous at hTm
    push Not at hTm
    obtain ⟨r, hr⟩ := hTm
    have hex : ∃ X ∈ xs, X ≠ WinnerSet.singleton r := by
      by_contra hno
      push Not at hno
      exact hm r ((unions_eq_singleton xs T r).mpr ⟨hr, hno⟩)
    obtain ⟨X, hX, hn⟩ := hex
    refine ⟨X, hX, ?_⟩
    simp only [WinnerSet.choice, hxs X hX, hT, or_self, ite_false]
    rw [hr, ambiguous_union_singleton]
    exact hn

/-- Propositional rails consistency suffices to read a Boolean assignment.
Only names present in the actual CNF support are considered. -/
theorem conflicting_predicates_of_unsatisfiable (formula : CNF) (P N : ℕ → Prop)
    (hu : ¬Satisfiable formula)
    (hclauses : ∀ C ∈ formula, ∃ literal ∈ C, if literal.2 then P literal.1 else N literal.1) :
    ∃ i ∈ ResetUnion.support formula, P i ∧ N i := by
  classical
  by_contra hno
  apply hu
  refine ⟨fun i => decide (P i), ?_⟩
  intro C hc
  obtain ⟨literal, hl, hpred⟩ := hclauses C hc
  refine ⟨literal, hl, ?_⟩
  cases hs : literal.2
  · have hN : N literal.1 := by simpa only [hs, Bool.false_eq_true, ite_false] using hpred
    have hnP : ¬P literal.1 := fun hP => hno
      ⟨literal.1, ResetUnion.literal_mem_support formula C hc literal hl, hP, hN⟩
    simp only [decide_eq_false hnP]
  · have hP : P literal.1 := by simpa only [hs, ite_true] using hpred
    simp only [decide_eq_true hP]

end KFOL.Reductions.RawPair

namespace KFOL.Reductions.RawPair

universe u

variable {Role : Type u}

theorem choiceFold_eq_foldl (a : Role) (xs : List (WinnerSet Role)) (base : WinnerSet Role) :
    choiceFold a xs base = xs.foldl (WinnerSet.choice a) base := by
  let _ : Std.Commutative (WinnerSet.choice a) :=
    ⟨fun X Y => WinnerSet.choice_comm X Y a⟩
  let _ : Std.Associative (WinnerSet.choice a) :=
    ⟨fun X Y Z => WinnerSet.choice_assoc (A := X) (B := Y) (r := a) Z⟩
  exact List.foldl_eq_foldr.symm

end KFOL.Reductions.RawPair

namespace KFOL.Reductions.RawPair

universe u

variable {Role : Type u}

theorem choiceFold_subset (a : Role) (xs : List (WinnerSet Role)) (base W : WinnerSet Role)
    (hbase : base.val ⊆ W.val) (hxs : ∀ X ∈ xs, X.val ⊆ W.val) :
    (choiceFold a xs base).val ⊆ W.val := by
  induction xs with
  | nil => exact hbase
  | cons X xs ih =>
    change (WinnerSet.choice a X (choiceFold a xs base)).val ⊆ W.val
    exact (WinnerSet.choice_subset_union a X _).trans
      (Set.union_subset (hxs X (List.mem_cons_self ..)) (ih (fun Y hy => hxs Y (List.mem_cons_of_mem _ hy))))

end KFOL.Reductions.RawPair
