module

public import KFOL.Congruences.Thresholds

/-! # Exactly K symmetric congruences, ordered by ambiguity threshold -/

@[expose] public section

namespace KFOL.WinnerSet

universe u

variable {Role : Type u} [Finite Role] [Nonempty Role]

/-- Consecutive threshold ranks are distinguished by a genuinely existing
nonempty set of the required size, compared with the full winner value. -/
theorem threshold_separating_set (m n : Fin (Nat.card Role)) (hmn : m.val < n.val) :
    ∃ A : WinnerSet Role,
      threshold m.val A = threshold m.val full ∧ threshold n.val A ≠ threshold n.val full := by
  classical
  have hsize : m.val + 1 ≤ (Set.univ : Set Role).ncard := by
    rw [Set.ncard_univ]
    omega
  obtain ⟨S,_,hS⟩ := Set.exists_subset_card_eq hsize
  have hsne : S.Nonempty := (Set.ncard_pos (Set.toFinite S)).mp (by omega)
  let A : WinnerSet Role := ⟨S,hsne⟩
  have ha : A.val.ncard = m.val + 1 := hS
  have hn : A.val.ncard ≤ n.val := by omega
  have hm : ¬ A.val.ncard ≤ m.val := by omega
  have hproper : A ≠ full := by
    intro he
    have hc := congrArg (fun B : WinnerSet Role => B.val.ncard) he
    simp only [full_val,Set.ncard_univ,ha] at hc
    omega
  refine ⟨A,?_,?_⟩
  · rw [threshold,ite_eq_right hm,threshold_full]
  · rw [threshold,ite_eq_left hn,threshold_full]
    exact hproper

theorem threshold_index_eq_of_kernels_eq (m n : Fin (Nat.card Role))
    (h : ∀ A B : WinnerSet Role,
      (threshold m.val A = threshold m.val B) ↔ (threshold n.val A = threshold n.val B)) : m = n := by
  by_contra hne
  have hv : m.val ≠ n.val := fun he => hne (Fin.ext he)
  rcases lt_or_gt_of_ne hv with hlt | hlt
  · obtain ⟨A,hm,hn⟩ := threshold_separating_set m n hlt
    exact hn ((h A full).mp hm)
  · obtain ⟨A,hn,hm⟩ := threshold_separating_set n m hlt
    exact hm ((h A full).mpr hn)

namespace SymmetricCongruence

omit [Finite Role] [Nonempty Role] in
@[ext] theorem ext {θ η : SymmetricCongruence Role} (h : ∀ A B, θ.r A B ↔ η.r A B) : θ = η := by
  have hc : θ.toCongruence = η.toCongruence := Congruence.ext h
  cases θ
  cases η
  cases hc
  rfl

/-- The complete symmetric classification, including uniqueness of the
threshold among the K ranks 0 through K-1. -/
theorem exists_unique_threshold (three : Fin 3 ↪ Role) (θ : SymmetricCongruence Role) :
    ∃! m : Fin (Nat.card Role), ∀ A B : WinnerSet Role,
      θ.r A B ↔ threshold m.val A = threshold m.val B := by
  obtain ⟨m,hm⟩ := invariant_eq_threshold (θ.toCongruence.closureOperator three)
    (θ.closureOperator_invariant three)
  have hrel (A B : WinnerSet Role) : θ.r A B ↔ threshold m.val A = threshold m.val B := by
    rw [← θ.toCongruence.closureOperator_rel_iff three,hm A,hm B]
  refine ⟨m,hrel,?_⟩
  intro n hn
  apply threshold_index_eq_of_kernels_eq
  intro A B
  exact (hn A B).symm.trans (hrel A B)

/-- The actual bijection witnesses the exact congruence count; none of the
K ranks is merely an unconnected finite certificate. -/
noncomputable def equivThresholds (three : Fin 3 ↪ Role) : SymmetricCongruence Role ≃ Fin (Nat.card Role) where
  toFun θ := (exists_unique_threshold three θ).choose
  invFun m := ClosureOperator.symmetricKernel (thresholdClosure m.val)
    (thresholdClosure_atom m.val) (thresholdClosure_invariant m.val)
  left_inv θ := by
    apply SymmetricCongruence.ext
    intro A B
    exact ((exists_unique_threshold three θ).choose_spec.1 A B).symm
  right_inv m := by
    exact ((exists_unique_threshold three (ClosureOperator.symmetricKernel (thresholdClosure m.val)
      (thresholdClosure_atom m.val) (thresholdClosure_invariant m.val))).choose_spec.2 m
      (fun _ _ => Iff.rfl)).symm

theorem card (three : Fin 3 ↪ Role) : Nat.card (SymmetricCongruence Role) = Nat.card Role := by
  rw [Nat.card_congr (equivThresholds three),Nat.card_fin]

end SymmetricCongruence

omit [Finite Role] in
/-- Increasing the threshold refines its kernel, giving the asserted chain. -/
theorem threshold_comp {m n : ℕ} (hmn : m ≤ n) (A : WinnerSet Role) :
    threshold m (threshold n A) = threshold m A := by
  classical
  by_cases hn : A.val.ncard ≤ n
  · have he : threshold n A = A := by rw [threshold,ite_eq_left hn]
    rw [he]
  · have hm : ¬ A.val.ncard ≤ m := fun h => hn (h.trans hmn)
    have he : threshold n A = full := by rw [threshold,ite_eq_right hn]
    rw [he,threshold_full,threshold,ite_eq_right hm]

omit [Finite Role] in
theorem threshold_kernel_antitone {m n : ℕ} (hmn : m ≤ n) (A B : WinnerSet Role)
    (h : threshold n A = threshold n B) : threshold m A = threshold m B := by
  have he := congrArg (threshold m) h
  simpa only [threshold_comp hmn] using he

@[simp] theorem threshold_zero (A : WinnerSet Role) : threshold 0 A = full := by
  classical
  have hp := (Set.ncard_pos (Set.toFinite A.val)).mpr A.property
  simp only [threshold,ite_eq_right (Nat.not_le_of_gt hp)]

@[simp] theorem threshold_last (A : WinnerSet Role) : threshold (Nat.card Role - 1) A = A := by
  classical
  by_cases h : A.val.ncard ≤ Nat.card Role - 1
  · simp only [threshold,ite_eq_left h]
  · have he : A = full := by
      by_contra hne
      have hv : A.val ≠ Set.univ := fun he => hne (Subtype.ext he)
      have hc : A.val.ncard < Nat.card Role := by
        simpa only [Set.ncard_univ] using Set.ncard_lt_ncard (Set.ssubset_univ_iff.mpr hv)
      omega
    rw [he,threshold_full]

end KFOL.WinnerSet
