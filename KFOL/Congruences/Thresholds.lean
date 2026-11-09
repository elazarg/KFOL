module

public import KFOL.Congruences.Symmetry

/-! # Classification of invariant closures by ambiguity thresholds -/

@[expose] public section

namespace KFOL.WinnerSet

universe u

variable {Role : Type u} [Finite Role] [Nonempty Role]

omit [Finite Role] in
@[simp] theorem threshold_full (m : ℕ) : threshold (Role := Role) m full = full := by
  classical
  unfold threshold
  split <;> rfl

/-- Every ambiguity threshold is a genuine closure operator in subset order. -/
noncomputable def thresholdClosure (m : ℕ) : ClosureOperator (WinnerSet Role) where
  toFun := threshold m
  monotone' := by
    intro A B hAB
    classical
    have hc : A.val.ncard ≤ B.val.ncard := Set.ncard_le_ncard hAB
    unfold threshold
    split_ifs with ha hb hb
    · exact hAB
    · exact le_full A
    · exact False.elim (ha (hc.trans hb))
    · exact le_rfl
  le_closure' A := by
    classical
    unfold threshold
    split
    · exact le_rfl
    · exact le_full A
  idempotent' A := by
    classical
    by_cases ha : A.val.ncard ≤ m
    · simp only [threshold,ite_eq_left ha]
    · have he : threshold m A = full := by rw [threshold,ite_eq_right ha]
      change threshold m (threshold m A) = threshold m A
      rw [he,threshold_full]

@[simp] theorem thresholdClosure_apply (m : ℕ) (A : WinnerSet Role) : thresholdClosure m A = threshold m A := rfl

theorem thresholdClosure_atom (m : ℕ) : AtomClosure (thresholdClosure (Role := Role) m) := by
  intro owner
  classical
  by_cases hm : 1 ≤ m
  · apply Or.inl
    simp [thresholdClosure_apply,threshold,singleton,hm]
  · apply Or.inr
    simp [thresholdClosure_apply,threshold,singleton,hm]

omit [Finite Role] in
@[simp] theorem rename_full (p : Equiv.Perm Role) : rename p full = full := by
  apply Subtype.ext
  change p '' Set.univ = Set.univ
  rw [Set.image_univ]
  exact p.surjective.range_eq

theorem thresholdClosure_invariant (m : ℕ) : PermutationInvariant (thresholdClosure (Role := Role) m) := by
  intro p A
  classical
  have hc : (rename p A).val.ncard = A.val.ncard := Set.ncard_image_of_injective _ p.injective
  simp only [thresholdClosure_apply,threshold,hc]
  split <;> simp only [rename_full]

/-- The complete invariant-closure classification, with an actual threshold
index strictly below the number of roles. -/
theorem invariant_eq_threshold (c : ClosureOperator (WinnerSet Role)) (hp : PermutationInvariant c) :
    ∃ m : Fin (Nat.card Role), ∀ A : WinnerSet Role, c A = threshold m.val A := by
  classical
  by_cases hex : ∃ A : WinnerSet Role, c A = A ∧ A ≠ full
  · let F : Set (WinnerSet Role) := {A | c A = A ∧ A ≠ full}
    obtain ⟨A,hA,hmax⟩ := (Set.toFinite F).exists_maximalFor (fun A : WinnerSet Role => A.val.ncard) F hex
    have hproper : A.val ≠ Set.univ := fun he => hA.2 (Subtype.ext he)
    have hcard : A.val.ncard < Nat.card Role := by
      simpa only [Set.ncard_univ] using Set.ncard_lt_ncard (Set.ssubset_univ_iff.mpr hproper)
    refine ⟨⟨A.val.ncard,hcard⟩,?_⟩
    intro B
    by_cases hB : B.val.ncard ≤ A.val.ncard
    · rw [threshold,ite_eq_left hB]
      exact invariant_closed_of_ncard_le c hp B A hA.1 hA.2 hB
    · rw [threshold,ite_eq_right hB]
      rcases invariant_closure_eq_or_full c hp B with he | he
      · by_cases hfull : B = full
        · exact he.trans hfull
        · have hmaxB : B.val.ncard ≤ A.val.ncard :=
            hmax ⟨he,hfull⟩ (le_of_lt (Nat.lt_of_not_ge hB))
          exact False.elim (hB hmaxB)
      · exact he
  · have hroles : 0 < Nat.card Role := Nat.card_pos
    refine ⟨⟨0,hroles⟩,?_⟩
    intro A
    have hAcard : 0 < A.val.ncard := (Set.ncard_pos (Set.toFinite A.val)).mpr A.property
    have hfull : c A = full := by
      rcases invariant_closure_eq_or_full c hp A with he | he
      · by_cases ha : A = full
        · exact he.trans ha
        · exact False.elim (hex ⟨A,he,ha⟩)
      · exact he
    rw [hfull,threshold,ite_eq_right (Nat.not_le_of_gt hAcard)]

end KFOL.WinnerSet
