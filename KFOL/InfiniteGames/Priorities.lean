module

public import KFOL.InfiniteGames.Profiles
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Basic

/-! # A finite-priority play has exactly one winner -/

@[expose] public section

namespace KFOL.InfiniteGames

universe u v

theorem exists_dominant_priority {n : ℕ} (priority : ℕ → Fin n) :
    ∃ p, (∀ N, ∃ k, N ≤ k ∧ priority k = p) ∧
      ∃ N, ∀ k, N ≤ k → priority k ≤ p := by
  classical
  let recurrent : Finset (Fin n) :=
    Finset.univ.filter fun p => ∀ N, ∃ k, N ≤ k ∧ priority k = p
  have recurrent_nonempty : recurrent.Nonempty := by
    by_contra empty
    have bound (p : Fin n) : ∃ N, ∀ k, N ≤ k → priority k ≠ p := by
      have hp : ¬ ∀ N, ∃ k, N ≤ k ∧ priority k = p := by
        intro hp
        exact empty ⟨p, by simp only [recurrent, Finset.mem_filter,
          Finset.mem_univ, true_and]; exact hp⟩
      simpa only [not_forall, not_exists, not_and] using hp
    choose cutoff cutoff_spec using bound
    let N := Finset.univ.sup cutoff
    exact cutoff_spec (priority N) N (Finset.le_sup (Finset.mem_univ _)) rfl
  let p := recurrent.max' recurrent_nonempty
  have p_recurrent : ∀ N, ∃ k, N ≤ k ∧ priority k = p :=
    (Finset.mem_filter.mp (Finset.max'_mem recurrent recurrent_nonempty)).2
  have bound (q : Fin n) : ∃ N, ∀ k, N ≤ k → priority k = q → q ≤ p := by
    by_cases hqp : q ≤ p
    · exact ⟨0, fun _ _ _ => hqp⟩
    · have hq : ¬ ∀ N, ∃ k, N ≤ k ∧ priority k = q := by
        intro hq
        exact hqp (Finset.le_max' recurrent q (by
          simp only [recurrent, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hq))
      obtain ⟨N, hN⟩ : ∃ N, ∀ k, N ≤ k → priority k ≠ q := by
        simpa only [not_forall, not_exists, not_and] using hq
      exact ⟨N, fun k hk h => (hN k hk h).elim⟩
  choose cutoff cutoff_spec using bound
  exact ⟨p, p_recurrent, Finset.univ.sup cutoff, fun k hk =>
    cutoff_spec (priority k) k ((Finset.le_sup (Finset.mem_univ _)).trans hk) rfl⟩

namespace PriorityGame

variable {Role : Type u} {Move : Type v} {n : ℕ}
variable (G : PriorityGame Role Move n)

theorem dominantPriority_exists (π : ℕ → List Move) :
    ∃ p, G.DominantPriority π p := exists_dominant_priority (G.priority ∘ π)

theorem dominantPriority_unique {π : ℕ → List Move} {p q : Fin n}
    (hp : G.DominantPriority π p) (hq : G.DominantPriority π q) : p = q := by
  apply le_antisymm
  · obtain ⟨N, hN⟩ := hq.2
    obtain ⟨k, hk, hkp⟩ := hp.1 N
    simpa only [hkp] using hN k hk
  · obtain ⟨N, hN⟩ := hp.2
    obtain ⟨k, hk, hkq⟩ := hq.1 N
    simpa only [hkq] using hN k hk

theorem wins_exists_unique (π : ℕ → List Move) : ∃! i, G.Wins i π := by
  obtain ⟨p, hp⟩ := G.dominantPriority_exists π
  refine ⟨G.priorityWinner p, ⟨p, rfl, hp⟩, ?_⟩
  rintro i ⟨q, hq, hqp⟩
  exact hq.symm.trans (congrArg G.priorityWinner (G.dominantPriority_unique hqp hp))

end PriorityGame

end KFOL.InfiniteGames
