module

public import KFOL.Algebra.IdempotencyTests
public import KFOL.Algebra.ReductTestCard

/-! # Optimal diagonal test domains, with attaining ambiguous domains -/

@[expose] public section

namespace KFOL

universe u

variable {Role : Type u} [Fintype Role]

/-- Complements of singletons always give a certifying ambiguous domain of size K. -/
theorem exists_idempotency_domain_card (three : Fin 3 ↪ Role) :
    ∃ D : Finset (WinnerSet Role), (∀ A ∈ D, WinnerSet.Ambiguous A) ∧
      CertifiesIdempotency (D : Set (WinnerSet Role)) ∧ D.card = Fintype.card Role := by
  classical
  let missing := fun k : Role => PlayerView.representative three k .impossible
  let D := Finset.univ.image missing
  have hm : ∀ k, missing k ∈ D := fun k => Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  have hamb : ∀ A ∈ D, WinnerSet.Ambiguous A := by
    intro A hA
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hA
    exact ((WinnerSet.view_eq_impossible_iff k _).mp (PlayerView.view_representative three k _)).2
  have hi : Function.Injective missing := by
    intro a b he
    by_contra hab
    have hb : a ∈ (missing b).val := hab
    rw [← he] at hb
    exact hb rfl
  refine ⟨D, hamb, (certifiesIdempotency_iff three _ hamb).mpr ⟨?_, ?_⟩, ?_⟩
  · intro k
    exact ⟨missing k, hm k, fun h => h rfl⟩
  · intro a b h
    by_contra hab
    exact ((h (missing a) (hm a)).mpr (Ne.symm hab)) rfl
  · exact (Finset.card_image_of_injective _ hi).trans (Finset.card_univ)

/-- At least three tests are needed whenever three roles are available,
even when singleton tests are allowed. -/
theorem three_le_card_idempotency_domain (three : Fin 3 ↪ Role)
    (D : Finset (WinnerSet Role))
    (hD : CertifiesIdempotency (D : Set (WinnerSet Role))) : 3 ≤ D.card := by
  classical
  by_contra hn
  have hsmall : D.card ≤ 2 := by omega
  obtain ⟨homit, hsep⟩ := certifiesIdempotency_necessary three _ hD
  have hatoms : ∀ A ∈ D, ∃ r, A = WinnerSet.singleton r := by
    intro A hAD
    by_contra hA
    have hamb : A.Ambiguous := fun r he => hA ⟨r, he⟩
    obtain ⟨a, ha⟩ := A.property
    obtain ⟨B, hBD, hBa⟩ := homit a
    have hne : A ≠ B := fun he => hBa (he ▸ ha)
    have hsub : ({A, B} : Finset (WinnerSet Role)) ⊆ D :=
      Finset.insert_subset hAD (Finset.singleton_subset_iff.mpr hBD)
    have hEq : ({A, B} : Finset (WinnerSet Role)) = D :=
      Finset.eq_of_subset_of_card_le hsub (by simpa [hne] using hsmall)
    have hd : Disjoint A.val B.val := by
      apply Set.disjoint_left.mpr
      intro r hrA hrB
      obtain ⟨F, hFD, hFr⟩ := homit r
      have hF : F = A ∨ F = B := by simpa [← hEq] using hFD
      exact hF.elim (fun he => hFr (he ▸ hrA)) (fun he => hFr (he ▸ hrB))
    have hnot : ¬∃ b ∈ A.val, b ≠ a := by
      rintro ⟨b, hb, hba⟩
      have heq : a = b := hsep a b (by
        intro F hF
        have hcases : F = A ∨ F = B := by simpa [← hEq] using hF
        rcases hcases with rfl | rfl
        · exact iff_of_true ha hb
        · exact iff_of_false (fun h => Set.disjoint_left.mp hd ha h)
            (fun h => Set.disjoint_left.mp hd hb h))
      exact hba heq.symm
    apply hamb a
    apply WinnerSet.eq_singleton_of_subset
    intro b hb
    by_contra hba
    exact hnot ⟨b, hb, hba⟩
  obtain ⟨t, _, ht, ha⟩ := Term.exists_public_ambiguity_adder three (three 2)
  have he : ∀ A : WinnerSet Role, t.eval (fun _ => A) = A := by
    apply hD 1 t
    intro A hA
    obtain ⟨r, rfl⟩ := hatoms A hA
    exact ht r
  let P := WinnerSet.union (WinnerSet.singleton (three 0)) (WinnerSet.singleton (three 1))
  have hP : P.Ambiguous := WinnerSet.ambiguous_of_two_mem P (three 0) (three 1)
    (three.injective.ne (by decide)) (Or.inl rfl) (Or.inr rfl)
  have hm : three 2 ∈ (t.eval (fun _ => P)).val := by rw [ha P hP]; exact Or.inr rfl
  rw [he P] at hm
  rcases hm with hm | hm
  · exact three.injective.ne (by decide : (2 : Fin 3) ≠ 0) hm
  · exact three.injective.ne (by decide : (2 : Fin 3) ≠ 1) hm

/-- Choose K distinct proper binary supports, reserving all co-singletons.
Each coordinate then contains at least two selected roles. -/
theorem exists_binary_idempotency_domain (three : Fin 3 ↪ Role)
    (m : ℕ) (hm : 3 ≤ m) (hmK : m ≤ Fintype.card Role)
    (hKm : Fintype.card Role ≤ 2 ^ m - 1) :
    ∃ D : Finset (WinnerSet Role), (∀ A ∈ D, WinnerSet.Ambiguous A) ∧
      CertifiesIdempotency (D : Set (WinnerSet Role)) ∧ D.card ≤ m := by
  classical
  let comp : Fin m → Finset (Fin m) := fun i => Finset.univ.erase i
  let reserved := Finset.univ.image comp
  let labels : Finset (Finset (Fin m)) := Finset.univ.erase Finset.univ
  have hcomp : ∀ i, comp i ∈ labels := by
    intro i
    simp only [labels, Finset.mem_erase, Finset.mem_univ, and_true]
    intro he
    have hh : i ∈ comp i := by rw [he]; exact Finset.mem_univ i
    simp [comp] at hh
  have hci : Function.Injective comp := by
    intro a b he
    by_contra hab
    have hb : a ∈ comp b := by simp [comp, hab]
    rw [← he] at hb
    simp [comp] at hb
  have hres : reserved ⊆ labels := by
    intro A hA
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hA
    exact hcomp i
  have hrc : reserved.card = m := by
    rw [Finset.card_image_of_injective _ hci, Finset.card_univ, Fintype.card_fin]
  have hlc : labels.card = 2 ^ m - 1 := by simp [labels]
  obtain ⟨B, hresB, hBl, hBc⟩ := Finset.exists_subsuperset_card_eq hres
    (by simpa [hrc] using hmK) (by simpa [hlc] using hKm)
  let e : Role ≃ B := Fintype.equivOfCardEq (by rw [Fintype.card_coe, hBc])
  have hbi : ∀ i, comp i ∈ B := fun i => hresB (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  let role : Fin m → Role := fun i => e.symm ⟨comp i, hbi i⟩
  have hri : Function.Injective role := by
    intro a b he
    apply hci
    exact congrArg Subtype.val (e.symm.injective he)
  have herole : ∀ i, (e (role i)).val = comp i := fun i => congrArg Subtype.val (e.apply_symm_apply _)
  have hrole : ∀ i j, j ∈ (e (role i)).val ↔ j ≠ i := by
    intro i j
    rw [herole]
    simp [comp]
  have hrow : ∀ j : Fin m, ∃ a b : Role, a ≠ b ∧
      j ∈ (e a).val ∧ j ∈ (e b).val := by
    intro j
    let emb : Fin 3 ↪ Fin m := Fin.castLEEmb hm
    obtain ⟨a, haj, _⟩ := exists_role_outside_pair emb j j
    obtain ⟨b, hba, hbj⟩ := exists_role_outside_pair emb a j
    exact ⟨role a, role b, hri.ne hba.symm,
      (hrole a j).mpr haj.symm, (hrole b j).mpr hbj.symm⟩
  let row : Fin m → WinnerSet Role := fun j =>
    ⟨{r | j ∈ (e r).val}, by obtain ⟨a, _, _, ha, _⟩ := hrow j; exact ⟨a, ha⟩⟩
  let D := Finset.univ.image row
  have hrowD : ∀ j, row j ∈ D := fun j => Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hamb : ∀ A ∈ D, A.Ambiguous := by
    intro A hA
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨a, b, hab, ha, hb⟩ := hrow j
    exact WinnerSet.ambiguous_of_two_mem (row j) a b hab ha hb
  refine ⟨D, hamb, (certifiesIdempotency_iff three _ hamb).mpr ⟨?_, ?_⟩, ?_⟩
  · intro r
    have hproper : (e r).val ≠ Finset.univ := (Finset.mem_erase.mp (hBl (e r).property)).1
    have hout : ∃ j : Fin m, j ∉ (e r).val := by
      by_contra hn
      apply hproper
      apply Finset.eq_univ_of_forall
      intro j
      by_contra hj
      exact hn ⟨j, hj⟩
    obtain ⟨j, hj⟩ := hout
    exact ⟨row j, hrowD j, hj⟩
  · intro a b hab
    apply e.injective
    apply Subtype.ext
    apply Finset.ext
    intro j
    exact hab (row j) (hrowD j)
  · simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_image_le (s := Finset.univ) (f := row))

/-- An ambiguous certifying domain attains the claimed optimum. -/
theorem exists_optimal_idempotency_domain (three : Fin 3 ↪ Role) :
    ∃ D : Finset (WinnerSet Role), (∀ A ∈ D, WinnerSet.Ambiguous A) ∧
      CertifiesIdempotency (D : Set (WinnerSet Role)) ∧
      D.card = if Fintype.card Role = 3 then 3 else Nat.clog 2 (Fintype.card Role + 1) := by
  classical
  by_cases hc : Fintype.card Role = 3
  · obtain ⟨D, hamb, hD, hcard⟩ := exists_idempotency_domain_card three
    exact ⟨D, hamb, hD, by simp [hc, hcard]⟩
  · have h3 : 3 ≤ Fintype.card Role := by simpa using Fintype.card_le_of_embedding three
    have h4 : 4 ≤ Fintype.card Role := by omega
    let m := Nat.clog 2 (Fintype.card Role + 1)
    have hm : 3 ≤ m := by
      have ht : 2 < m := (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr (by change 4 < _; omega)
      omega
    have hmK : m ≤ Fintype.card Role := Nat.clog_le_of_le_pow
      (Nat.succ_le_of_lt (Nat.lt_pow_self (by decide : 1 < 2)))
    have hpow : Fintype.card Role + 1 ≤ 2 ^ m := Nat.le_pow_clog (by decide) _
    have hKm : Fintype.card Role ≤ 2 ^ m - 1 := by omega
    obtain ⟨D, hamb, hD, hcard⟩ := exists_binary_idempotency_domain three m hm hmK hKm
    refine ⟨D, hamb, hD, ?_⟩
    have hl := card_idempotency_domain_lower three D hD
    simp only [ite_eq_right hc]
    exact Nat.le_antisymm hcard hl

/-- The sharp lower bound for all domains, including those containing atoms. -/
theorem card_optimal_idempotency_domain_lower (three : Fin 3 ↪ Role)
    (D : Finset (WinnerSet Role)) (hD : CertifiesIdempotency (D : Set (WinnerSet Role))) :
    (if Fintype.card Role = 3 then 3 else Nat.clog 2 (Fintype.card Role + 1)) ≤ D.card := by
  split_ifs
  · exact three_le_card_idempotency_domain three D hD
  · exact card_idempotency_domain_lower three D hD

end KFOL
