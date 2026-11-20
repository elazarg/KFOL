module

/-! # Restarting finite proofs in an alternating reachability game

A state wins if a finite tree of allowed successors ends in accepting states.
An entry can restart the game, and an execution applies the original rule.
-/

@[expose] public section
namespace KFOL.Core.AlternatingReachability

universe u
variable {State : Type u}

/-- An accepting or rejecting end, or a choice of one or both successors. -/
inductive Rule (State : Type u) where
  | accept
  | reject
  | either (left right : State)
  | both (left right : State)

/-- The least winning set, presented by finite accepting trees. -/
inductive Wins (rule : State → Rule State) : State → Prop where
  | accept {s} : rule s = .accept → Wins rule s
  | left {s x y} : rule s = .either x y → Wins rule x → Wins rule s
  | right {s x y} : rule s = .either x y → Wins rule y → Wins rule s
  | both {s x y} : rule s = .both x y → Wins rule x → Wins rule y → Wins rule s

/-- Entry states can run their original rule or restart. An original
rejection can only restart. -/
def withRestart (rule : State → Rule State) (initial : State) : State ⊕ State → Rule (State ⊕ State)
  | .inl s => .either (.inr s) (.inl initial)
  | .inr s =>
    match rule s with
    | .accept => .accept
    | .reject => .either (.inl initial) (.inl initial)
    | .either x y => .either (.inl x) (.inl y)
    | .both x y => .both (.inl x) (.inl y)

variable {rule : State → Rule State} {initial : State}

private theorem entry_win {s : State} (h : Wins rule s) :
    Wins (withRestart rule initial) (.inl s) := by
  induction h <;> refine Wins.left (rule := withRestart rule initial) (y := .inl initial) rfl ?_
  case accept step => exact Wins.accept (by simp [withRestart, step])
  case left s x y step _ ih => exact Wins.left (y := .inl y) (by simp [withRestart, step]) ih
  case right s x y step _ ih => exact Wins.right (x := .inl x) (by simp [withRestart, step]) ih
  case both step _ _ ihx ihy => exact Wins.both (by simp [withRestart, step]) ihx ihy

private theorem original_of_win_if_no_restart (no : ¬ Wins rule initial)
    {s : State ⊕ State} (h : Wins (withRestart rule initial) s) :
    Wins rule (s.elim id id) := by
  induction h with
  | @accept s step =>
    cases s with
    | inl s => simp [withRestart] at step
    | inr s =>
      cases old : rule s <;> simp [withRestart, old] at step
      exact Wins.accept old
  | @left s x y step _ ih =>
    cases s with
    | inl s =>
      simp [withRestart] at step
      obtain ⟨rfl, rfl⟩ := step
      exact ih
    | inr s =>
      cases old : rule s <;> simp [withRestart, old] at step
      · obtain ⟨rfl, rfl⟩ := step
        exact (no ih).elim
      · obtain ⟨rfl, rfl⟩ := step
        exact Wins.left old ih
  | @right s x y step _ ih =>
    cases s with
    | inl s =>
      simp [withRestart] at step
      obtain ⟨rfl, rfl⟩ := step
      exact (no ih).elim
    | inr s =>
      cases old : rule s <;> simp [withRestart, old] at step
      · obtain ⟨rfl, rfl⟩ := step
        exact (no ih).elim
      · obtain ⟨rfl, rfl⟩ := step
        exact Wins.right old ih
  | @both s x y step _ _ ihx ihy =>
    cases s with
    | inl s => simp [withRestart] at step
    | inr s =>
      cases old : rule s <;> simp [withRestart, old] at step
      obtain ⟨rfl, rfl⟩ := step
      exact Wins.both old ihx ihy

/-- Restarts preserve whether the initial state wins. -/
theorem initial_win_iff : Wins (withRestart rule initial) (.inl initial) ↔ Wins rule initial := by
  exact ⟨fun h => Classical.byContradiction (fun no => no (original_of_win_if_no_restart no h)), entry_win⟩

/-- A winning start gives a finite winning tree at every entry and
execution state of the extended game. -/
theorem all_win_iff : (∀ s, Wins (withRestart rule initial) s) ↔ Wins rule initial := by
  refine ⟨fun h => initial_win_iff.mp (h (.inl initial)), fun h s => ?_⟩
  have entry (x : State) : Wins (withRestart rule initial) (.inl x) :=
    Wins.right rfl (entry_win h)
  cases s with
  | inl s => exact entry s
  | inr s =>
    cases step : rule s with
    | accept => exact Wins.accept (by simp [withRestart, step])
    | reject => exact Wins.left (y := .inl initial) (by simp [withRestart, step]) (entry initial)
    | either x y => exact Wins.left (y := .inl y) (by simp [withRestart, step]) (entry x)
    | both x y => exact Wins.both (by simp [withRestart, step]) (entry x) (entry y)

end KFOL.Core.AlternatingReachability
