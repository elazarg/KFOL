module

public import KFOL.Congruences.Thresholds
public import Mathlib.Combinatorics.Matroid.IndepAxioms
public import Mathlib.Combinatorics.Matroid.Rank.ENat

/-! # The actual finite uniform matroid underlying ambiguity thresholds -/

@[expose] public section

namespace KFOL

universe u

variable {Role : Type u} [Finite Role]

/-- The finite uniform matroid of the specified rank bound. Its independent
sets satisfy the literal cardinality bound, and finite augmentation is proved
from the existence of a new point and the successor-cardinality formula. -/
noncomputable def uniformMatroid (rank : ℕ) : Matroid Role :=
  (IndepMatroid.ofFinite (Set.toFinite (Set.univ : Set Role))
    (fun I => I.ncard ≤ rank)
    (by simp)
    (by intro I J hJ hIJ; exact (Set.ncard_le_ncard hIJ).trans hJ)
    (by
      intro I J _ hJ hIJ
      obtain ⟨e,heJ,heI⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hIJ
      refine ⟨e,heJ,heI,?_⟩
      rw [Set.ncard_insert_of_notMem heI]
      omega)
    (by intro I _; exact Set.subset_univ I)).matroid

@[simp] theorem uniformMatroid_ground (rank : ℕ) : (uniformMatroid (Role := Role) rank).E = Set.univ := rfl

@[simp] theorem uniformMatroid_indep (rank : ℕ) (I : Set Role) :
    (uniformMatroid rank).Indep I ↔ I.ncard ≤ rank := Iff.rfl

/-- Below full rank, matroid closure fixes a set; at the exact cardinal
boundary, every outside point becomes dependent and closure is full. -/
theorem uniformMatroid_closure (m : ℕ) (S : Set Role) :
    (uniformMatroid (m+1)).closure S = if S.ncard ≤ m then S else Set.univ := by
  classical
  let M := uniformMatroid (Role := Role) (m+1)
  by_cases hs : S.ncard ≤ m
  · rw [ite_eq_left hs]
    have hI : M.Indep S := (uniformMatroid_indep (m+1) S).mpr (by omega)
    apply Set.Subset.antisymm
    · intro x hx
      have hmem := (hI.mem_closure_iff').mp hx
      apply hmem.2
      rw [uniformMatroid_indep]
      exact (Set.ncard_insert_le x S).trans (by omega)
    · exact M.subset_closure S (by simp [M])
  · rw [ite_eq_right hs]
    obtain ⟨I,hIS,hIcard⟩ := Set.exists_subset_card_eq (show m+1 ≤ S.ncard by omega)
    have hI : M.Indep I := (uniformMatroid_indep (m+1) I).mpr hIcard.le
    have hfull : M.closure I = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      apply (hI.mem_closure_iff').mpr
      refine ⟨by simp [M],?_⟩
      intro hinsert
      by_contra hx
      have hc := (uniformMatroid_indep (m+1) (insert x I)).mp hinsert
      rw [Set.ncard_insert_of_notMem hx,hIcard] at hc
      omega
    apply Set.Subset.antisymm (Set.subset_univ _)
    rw [← hfull]
    exact M.closure_mono hIS

/-- The bases have the prescribed size whenever the rank bound does not
exceed the number of roles. -/
theorem uniformMatroid_isBase_iff {rank : ℕ} (hrank : rank ≤ Nat.card Role) (B : Set Role) :
    (uniformMatroid rank).IsBase B ↔ B.ncard = rank := by
  classical
  let M := uniformMatroid (Role := Role) rank
  constructor
  · intro hB
    have hle := (uniformMatroid_indep rank B).mp hB.indep
    apply Nat.le_antisymm hle
    by_contra hn
    have hlt : B.ncard < Nat.card Role := by omega
    obtain ⟨e,heU,heB⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
      (show B.ncard < (Set.univ : Set Role).ncard by simpa only [Set.ncard_univ] using hlt)
    have hinsert : M.Indep (insert e B) := by
      rw [uniformMatroid_indep,Set.ncard_insert_of_notMem heB]
      omega
    have heq := hB.eq_of_subset_indep hinsert (Set.subset_insert e B)
    exact heB (heq.symm ▸ Set.mem_insert e B)
  · intro hcard
    have hB : M.Indep B := (uniformMatroid_indep rank B).mpr hcard.le
    apply hB.isBase_of_maximal
    intro J hJ hBJ
    apply Set.eq_of_subset_of_ncard_le hBJ
    rw [hcard]
    exact (uniformMatroid_indep rank J).mp hJ

theorem uniformMatroid_eRank {rank : ℕ} (hrank : rank ≤ Nat.card Role) :
    (uniformMatroid (Role := Role) rank).eRank = rank := by
  obtain ⟨B,_,hBcard⟩ := Set.exists_subset_card_eq
    (show rank ≤ (Set.univ : Set Role).ncard by simpa only [Set.ncard_univ] using hrank)
  have hbase := (uniformMatroid_isBase_iff hrank B).mpr hBcard
  rw [← hbase.encard_eq_eRank,← (Set.toFinite B).cast_ncard_eq,hBcard]

namespace WinnerSet

/-- The independently defined winner threshold is literally the restriction
of the actual uniform-matroid closure to nonempty winner sets. -/
theorem threshold_eq_uniformMatroid_closure [Nonempty Role] (m : ℕ) (A : WinnerSet Role) :
    (threshold m A).val = (uniformMatroid (m+1)).closure A.val := by
  classical
  rw [uniformMatroid_closure]
  unfold threshold
  split <;> rfl

/-- Complete paper-facing uniform-matroid identification, including actual
independence and rank rather than a renamed threshold function. -/
theorem uniform_matroid_identification [Nonempty Role] (m : ℕ) (hm : m < Nat.card Role) :
    ∃ M : Matroid Role,
      M.E = Set.univ ∧
      (∀ I : Set Role, M.Indep I ↔ I.ncard ≤ m+1) ∧
      M.eRank = (m+1 : ℕ) ∧
      ∀ A : WinnerSet Role, (threshold m A).val = M.closure A.val := by
  exact ⟨uniformMatroid (m+1),uniformMatroid_ground (m+1),uniformMatroid_indep (m+1),
    uniformMatroid_eRank (by omega),threshold_eq_uniformMatroid_closure m⟩

end WinnerSet

end KFOL
