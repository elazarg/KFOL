module

public import KFOL.Algebra

/-! Boundary cases for the two testing notions. Incidence conditions alone
need not certify a mixed domain, and a certifying ambiguous domain need not
contain every role anywhere. -/

@[expose] public section

namespace KFOLTest.TestDomains

open KFOL

private noncomputable def twoAtoms : Finset (WinnerSet (Fin 3)) := by
  classical
  exact {WinnerSet.singleton 0, WinnerSet.singleton 1}

-- The incidence words 10, 01 and 00 are distinct and avoid 11, but the
-- ambiguous-only criterion must not be applied to these singleton tests.
example :
    (∀ k : Fin 3, ∃ A ∈ twoAtoms, k ∉ A.val) ∧
    (∀ a b : Fin 3, (∀ A ∈ twoAtoms, a ∈ A.val ↔ b ∈ A.val) → a = b) ∧
    ¬CertifiesIdempotency (twoAtoms : Set (WinnerSet (Fin 3))) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro k
    by_cases hk : k = 0
    · exact ⟨WinnerSet.singleton 1, by simp [twoAtoms], by simp [hk]⟩
    · exact ⟨WinnerSet.singleton 0, by simp [twoAtoms], hk⟩
  · intro a b h
    have h0 := h (WinnerSet.singleton 0) (by simp [twoAtoms])
    have h1 := h (WinnerSet.singleton 1) (by simp [twoAtoms])
    simp only [WinnerSet.val_singleton, Set.mem_singleton_iff] at h0 h1
    apply Fin.ext
    omega
  · intro hc
    have h := three_le_card_idempotency_domain (Function.Embedding.refl _) twoAtoms hc
    simp [twoAtoms] at h

private def pair (a b : Fin 4) : WinnerSet (Fin 4) :=
  WinnerSet.union (WinnerSet.singleton a) (WinnerSet.singleton b)

private noncomputable def missingZero : Finset (WinnerSet (Fin 4)) := by
  classical
  exact {pair 1 2, pair 1 3, pair 2 3}

-- Role 0 is absent from every test. This is allowed: the condition requires
-- empty intersection and distinct incidences, not that the union cover all roles.
private theorem missingZero_spec : CertifiesIdempotency (missingZero : Set (WinnerSet (Fin 4))) ∧
    (∀ A ∈ missingZero, (0 : Fin 4) ∉ A.val) ∧ missingZero.card = 3 := by
  classical
  have hamb : ∀ A ∈ missingZero, A.Ambiguous := by
    intro A hA
    simp only [missingZero, Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with rfl | rfl | rfl
    · exact WinnerSet.ambiguous_of_two_mem _ 1 2 (by decide) (Or.inl rfl) (Or.inr rfl)
    · exact WinnerSet.ambiguous_of_two_mem _ 1 3 (by decide) (Or.inl rfl) (Or.inr rfl)
    · exact WinnerSet.ambiguous_of_two_mem _ 2 3 (by decide) (Or.inl rfl) (Or.inr rfl)
  refine ⟨(certifiesIdempotency_iff (Fin.castLEEmb (by decide : 3 ≤ 4)) _ hamb).mpr ⟨?_, ?_⟩,
    ?_, ?_⟩
  · intro k
    by_cases h1 : k = 1
    · exact ⟨pair 2 3, by simp [missingZero], by simp [pair, h1]⟩
    by_cases h2 : k = 2
    · exact ⟨pair 1 3, by simp [missingZero], by simp [pair, h2]⟩
    · exact ⟨pair 1 2, by simp [missingZero], by simp [pair, h1, h2]⟩
  · intro a b h
    have h12 := h (pair 1 2) (by simp [missingZero])
    have h13 := h (pair 1 3) (by simp [missingZero])
    have h23 := h (pair 2 3) (by simp [missingZero])
    simp only [pair, WinnerSet.val_union, WinnerSet.val_singleton, Set.mem_union,
      Set.mem_singleton_iff] at h12 h13 h23
    apply Fin.ext
    omega
  · intro A hA
    simp only [missingZero, Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with rfl | rfl | rfl <;> simp [pair]
  · have h12 : pair 1 2 ≠ pair 1 3 := by
      intro h
      have hm : (2 : Fin 4) ∈ (pair 1 3).val := h ▸ Or.inr rfl
      simp [pair] at hm
    have h13 : pair 1 2 ≠ pair 2 3 := by
      intro h
      have hm : (1 : Fin 4) ∈ (pair 2 3).val := h ▸ Or.inl rfl
      simp [pair] at hm
    have h23 : pair 1 3 ≠ pair 2 3 := by
      intro h
      have hm : (1 : Fin 4) ∈ (pair 2 3).val := h ▸ Or.inl rfl
      simp [pair] at hm
    simp [missingZero, h12, h13, h23]

-- Certifying all diagonals does not require testing every equation on all
-- tuples: this certifying domain omits the necessary singleton test {0}.
example : ¬CompletePublicTestDomain (missingZero : Set (WinnerSet (Fin 4))) := by
  intro hc
  have h0 := ((completePublicTestDomain_iff
    (Fin.castLEEmb (by decide : 3 ≤ 4)) _).mp hc).1 0
  exact missingZero_spec.2.1 (WinnerSet.singleton 0) h0 rfl

end KFOLTest.TestDomains
