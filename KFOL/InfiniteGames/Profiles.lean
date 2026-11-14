module

public import KFOL.Definitions.InfiniteGames

/-! # Full deviations and paths through an infinite history tree -/

@[expose] public section

namespace KFOL.InfiniteGames

universe u v

variable {Move : Type v}

@[simp] theorem run_zero (σ : Profile Move) (h : List Move) : run σ h 0 = h := rfl

@[simp] theorem run_succ (σ : Profile Move) (h : List Move) (k : ℕ) :
    run σ h (k + 1) = run σ h k ++ [σ (run σ h k)] := rfl

theorem run_length (σ : Profile Move) (h : List Move) (k : ℕ) :
    (run σ h k).length = h.length + k := by
  induction k with
  | zero => simp
  | succ k ih => simp [ih, Nat.add_assoc]

theorem path_length {π : ℕ → List Move}
    (step : ∀ k, legal (π k) (π (k + 1))) (k : ℕ) :
    (π k).length = (π 0).length + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨a, ha⟩ := step k
    simp [ha, ih, Nat.add_assoc]

theorem path_injective {π : ℕ → List Move}
    (step : ∀ k, legal (π k) (π (k + 1))) : Function.Injective π := by
  intro a b hab
  have hlen := congrArg List.length hab
  exact Nat.add_left_cancel ((path_length step a).symm.trans (hlen.trans (path_length step b)))

theorem run_profilePath (σ : Profile Move) (h : List Move) :
    ∀ k, profileRel σ (run σ h k) (run σ h (k + 1)) := fun _ => rfl

theorem eq_run_of_profilePath {σ : Profile Move} {h : List Move}
    {π : ℕ → List Move} (initial : π 0 = h)
    (step : ∀ k, profileRel σ (π k) (π (k + 1))) : π = run σ h := by
  funext k
  induction k with
  | zero => exact initial
  | succ k ih =>
    have hs : π (k + 1) = π k ++ [σ (π k)] := step k
    simpa only [run_succ, ih] using hs

namespace PriorityGame

variable {Role : Type u} {n : ℕ} (G : PriorityGame Role Move n)

theorem deviation_run_path {i : Role} {σ τ : Profile Move}
    (deviation : G.Deviation i σ τ) (h : List Move) :
    ∀ k, G.deviationRel σ i (run τ h k) (run τ h (k + 1)) := by
  intro k
  exact ⟨τ (run τ h k), rfl, deviation (run τ h k)⟩

/-- Any path that changes only one player's moves extends to a complete
replacement profile. Distinct path positions have distinct history lengths,
so the prescribed replacements are consistent even off the original path. -/
theorem exists_deviation_of_path {i : Role} {σ : Profile Move} {h : List Move}
    {π : ℕ → List Move} (initial : π 0 = h)
    (step : ∀ k, G.deviationRel σ i (π k) (π (k + 1))) :
    ∃ τ, G.Deviation i σ τ ∧ run τ h = π := by
  classical
  have legalStep : ∀ k, legal (π k) (π (k + 1)) :=
    fun k => ⟨(step k).choose, (step k).choose_spec.1⟩
  have injective := path_injective legalStep
  let action : ℕ → Move := fun k => (step k).choose
  have actionStep (k : ℕ) : π (k + 1) = π k ++ [action k] :=
    (step k).choose_spec.1
  have actionOther (k : ℕ) : G.owner (π k) ≠ i → action k = σ (π k) :=
    (step k).choose_spec.2
  let τ : Profile Move := fun k =>
    if occurs : ∃ j, π j = k then action occurs.choose else σ k
  have τ_path (k : ℕ) : τ (π k) = action k := by
    dsimp [τ]
    rw [dite_eq_left ⟨k, rfl⟩]
    congr 1
    exact injective (Exists.choose_spec (show ∃ j, π j = π k from ⟨k, rfl⟩))
  refine ⟨τ, ?_, ?_⟩
  · intro k hk
    dsimp [τ]
    split_ifs with occurs
    · have heq := occurs.choose_spec
      simpa only [heq] using actionOther occurs.choose (by simpa only [heq] using hk)
    · rfl
  · symm
    apply eq_run_of_profilePath initial
    intro k
    change π (k + 1) = π k ++ [τ (π k)]
    rw [τ_path k]
    exact actionStep k

theorem deviation_path_iff {i : Role} {σ : Profile Move} {h : List Move}
    {π : ℕ → List Move} :
    (∃ τ, G.Deviation i σ τ ∧ run τ h = π) ↔
      π 0 = h ∧ ∀ k, G.deviationRel σ i (π k) (π (k + 1)) := by
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨rfl, G.deviation_run_path hτ h⟩
  · rintro ⟨initial, step⟩
    exact G.exists_deviation_of_path initial step

end PriorityGame

end KFOL.InfiniteGames
