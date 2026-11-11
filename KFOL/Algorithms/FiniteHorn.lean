module

public import KFOL.Definitions.FiniteHorn

/-! # Exact finite-round saturation of positive Horn rules -/

@[expose] public section

namespace KFOL.FiniteHorn

universe u
variable {Fact : Type u} [Fintype Fact] (S : System Fact)

@[simp] theorem mem_step (D : Finset Fact) (c : Fact) :
    c ∈ step S D ↔ c ∈ D ∨ S.seed c ∨ ∃ a ∈ D, ∃ b ∈ D, S.rule a b c := by
  classical
  simp [step]

theorem subset_step (D : Finset Fact) : D ⊆ step S D :=
  fun _ h => (mem_step S D _).mpr (Or.inl h)

theorem step_mono {D E : Finset Fact} (h : D ⊆ E) : step S D ⊆ step S E := by
  intro c hc
  rcases (mem_step S D c).mp hc with hc | hc | ⟨a, ha, b, hb, hr⟩
  · exact (mem_step S E c).mpr (Or.inl (h hc))
  · exact (mem_step S E c).mpr (Or.inr (Or.inl hc))
  · exact (mem_step S E c).mpr (Or.inr (Or.inr ⟨a, h ha, b, h hb, hr⟩))

theorem stage_le_succ (n : ℕ) : stage S n ⊆ stage S (n + 1) := subset_step S _

private theorem stage_plateau {k : ℕ} (h : stage S k = stage S (k + 1)) :
    ∀ n, k ≤ n → stage S n = stage S k := by
  intro n hn
  induction hn with
  | refl => rfl
  | @step n hn ih =>
    change step S (stage S n) = stage S k
    rw [ih]
    exact h.symm

theorem saturate_fixed : step S (saturate S) = saturate S := by
  classical
  unfold saturate
  let N := Fintype.card Fact
  have plateau : ∃ k ≤ N, stage S k = stage S (k + 1) := by
    by_contra h
    have strict (k : ℕ) (hk : k ≤ N) : (stage S k).card < (stage S (k + 1)).card := by
      apply Finset.card_lt_card
      exact (Finset.ssubset_iff_subset_ne).mpr
        ⟨stage_le_succ S k, fun he => h ⟨k, hk, he⟩⟩
    have lower (k : ℕ) : k ≤ N + 1 → k ≤ (stage S k).card := by
      induction k with
      | zero => exact fun _ => Nat.zero_le _
      | succ k ih =>
        intro hk
        have hprev := ih (by omega)
        have hnext := strict k (by omega)
        omega
    have lo := lower (N + 1) (by omega)
    have hi := Finset.card_le_univ (s := stage S (N + 1))
    omega
  obtain ⟨k, hk, he⟩ := plateau
  have hN := stage_plateau S he N hk
  have hNext := stage_plateau S he (N + 1) (by omega)
  exact hNext.trans hN.symm

theorem derives_of_mem_stage (n : ℕ) {c : Fact} (hc : c ∈ stage S n) : Derives S c := by
  induction n generalizing c with
  | zero => simp [stage] at hc
  | succ n ih =>
    rcases (mem_step S _ _).mp hc with h | h | ⟨a, ha, b, hb, hr⟩
    · exact ih h
    · exact .seed h
    · exact .step hr (ih ha) (ih hb)

/-- The bounded saturation is exactly ordinary finite derivability. -/
theorem mem_saturate_iff (c : Fact) : c ∈ saturate S ↔ Derives S c := by
  constructor
  · intro hc
    exact derives_of_mem_stage S _ (by simpa only [saturate] using hc)
  · intro hc
    induction hc with
    | seed hs =>
      rw [← saturate_fixed S]
      exact (mem_step S _ _).mpr (Or.inr (Or.inl hs))
    | step hr _ _ ha hb =>
      rw [← saturate_fixed S]
      exact (mem_step S _ _).mpr (Or.inr (Or.inr ⟨_, ha, _, hb, hr⟩))

end KFOL.FiniteHorn
