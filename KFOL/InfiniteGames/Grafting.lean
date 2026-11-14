module

public import KFOL.Definitions.InfiniteGrafting

/-! # Strict-zero owned choice for arbitrary public continuations -/

@[expose] public section

namespace KFOL.InfiniteGames.PublicGrafting

universe u v w

variable {Role : Type u} {G : Continuation.{u, v} Role} {H : Continuation.{u, w} Role}

namespace GraftPlan

theorem isNash_of_root_optimal {owner : Role} {p : GraftPlan G H}
    (left : G.perfect p.left) (right : H.perfect p.right)
    (optimal : G.winner p.left = owner ∨ H.winner p.right = owner → p.winner = owner) :
    p.IsNash owner := by
  intro i q deviation wins
  by_cases hi : i = owner
  · have alt : G.winner p.left = owner ∨ H.winner p.right = owner := by
      cases hq : q.action with
      | false =>
        exact Or.inl ((G.perfect_nash p.left left i q.left deviation.2.1
          (by simpa only [winner, hq, Bool.false_eq_true, ↓reduceIte] using wins)).trans hi)
      | true =>
        exact Or.inr ((H.perfect_nash p.right right i q.right deviation.2.2
          (by simpa only [winner, hq, ↓reduceIte] using wins)).trans hi)
    exact (optimal alt).trans hi.symm
  · have same : p.action = q.action := deviation.1 (Ne.symm hi)
    cases hp : p.action with
    | false =>
      have hq : q.action = false := same.symm.trans hp
      simpa only [winner, hp, Bool.false_eq_true, ↓reduceIte] using
        G.perfect_nash p.left left i q.left deviation.2.1
          (by simpa only [winner, hq, Bool.false_eq_true, ↓reduceIte] using wins)
    | true =>
      have hq : q.action = true := same.symm.trans hp
      simpa only [winner, hp, ↓reduceIte] using
        H.perfect_nash p.right right i q.right deviation.2.2
          (by simpa only [winner, hq, ↓reduceIte] using wins)

theorem root_optimal_of_isNash {owner : Role} {p : GraftPlan G H}
    (nash : p.IsNash owner) :
    G.winner p.left = owner ∨ H.winner p.right = owner → p.winner = owner := by
  rintro (left | right)
  · apply nash owner ⟨false, p.left, p.right⟩
    · exact ⟨fun h => (h rfl).elim, G.deviation_refl owner p.left,
        H.deviation_refl owner p.right⟩
    · exact left
  · apply nash owner ⟨true, p.left, p.right⟩
    · exact ⟨fun h => (h rfl).elim, G.deviation_refl owner p.left,
        H.deviation_refl owner p.right⟩
    · exact right

end GraftPlan

private theorem value_nonempty_iff (G : Continuation.{u, v} Role) :
    G.possibleWinners.Nonempty ↔ ∃ p, G.perfect p := by
  constructor
  · rintro ⟨i, p, hp, _⟩
    exact ⟨p, hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨G.winner p, p, hp, rfl⟩

private theorem exists_losing {owner : Role} (nonempty : G.possibleWinners.Nonempty)
    (not_singleton : G.possibleWinners ≠ {owner}) :
    ∃ p, G.perfect p ∧ G.winner p ≠ owner := by
  classical
  by_contra h
  have all : ∀ p, G.perfect p → G.winner p = owner := by
    simpa only [not_exists, not_and, not_not] using h
  apply not_singleton
  apply Set.eq_singleton_iff_unique_mem.mpr
  obtain ⟨p, hp⟩ := (value_nonempty_iff G).mp nonempty
  refine ⟨⟨p, hp, all p hp⟩, ?_⟩
  rintro i ⟨q, hq, rfl⟩
  exact all q hq

private theorem possibleWinners_subset_union (owner : Role) :
    possibleWinners owner G H ⊆ G.possibleWinners ∪ H.possibleWinners := by
  rintro i ⟨p, hp, rfl⟩
  cases ha : p.action with
  | false => exact Or.inl ⟨p.left, hp.2.1, by simp only [GraftPlan.winner, ha, Bool.false_eq_true, ↓reduceIte]⟩
  | true => exact Or.inr ⟨p.right, hp.2.2, by simp only [GraftPlan.winner, ha, ↓reduceIte]⟩

private theorem union_subset_possibleWinners {owner : Role}
    (left_nonempty : G.possibleWinners.Nonempty)
    (right_nonempty : H.possibleWinners.Nonempty)
    (left_not_singleton : G.possibleWinners ≠ {owner})
    (right_not_singleton : H.possibleWinners ≠ {owner}) :
    G.possibleWinners ∪ H.possibleWinners ⊆ possibleWinners owner G H := by
  rintro i (left | right)
  · obtain ⟨p, hp, hpi⟩ := left
    obtain ⟨q, hq, hqlose⟩ := exists_losing right_nonempty right_not_singleton
    let plan : GraftPlan G H := ⟨false, p, q⟩
    refine ⟨plan, ⟨?_, hp, hq⟩, hpi⟩
    apply GraftPlan.isNash_of_root_optimal hp hq
    rintro (h | h)
    · exact h
    · exact (hqlose h).elim
  · obtain ⟨q, hq, hqi⟩ := right
    obtain ⟨p, hp, hplose⟩ := exists_losing left_nonempty left_not_singleton
    let plan : GraftPlan G H := ⟨true, p, q⟩
    refine ⟨plan, ⟨?_, hp, hq⟩, hqi⟩
    apply GraftPlan.isNash_of_root_optimal hp hq
    rintro (h | h)
    · exact (hplose h).elim
    · exact h

private theorem possibleWinners_eq_singleton {owner : Role}
    (left_nonempty : G.possibleWinners.Nonempty)
    (right_nonempty : H.possibleWinners.Nonempty)
    (forced : G.possibleWinners = {owner} ∨ H.possibleWinners = {owner}) :
    possibleWinners owner G H = {owner} := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  obtain ⟨p, hp⟩ := (value_nonempty_iff G).mp left_nonempty
  obtain ⟨q, hq⟩ := (value_nonempty_iff H).mp right_nonempty
  have forced_win : G.winner p = owner ∨ H.winner q = owner := by
    rcases forced with h | h
    · exact Or.inl (by simpa only [h, Set.mem_singleton_iff] using
        (show G.winner p ∈ G.possibleWinners from ⟨p, hp, rfl⟩))
    · exact Or.inr (by simpa only [h, Set.mem_singleton_iff] using
        (show H.winner q ∈ H.possibleWinners from ⟨q, hq, rfl⟩))
  constructor
  · rcases forced_win with h | h
    · let plan : GraftPlan G H := ⟨false, p, q⟩
      exact ⟨plan, ⟨GraftPlan.isNash_of_root_optimal hp hq (fun _ => h), hp, hq⟩, h⟩
    · let plan : GraftPlan G H := ⟨true, p, q⟩
      exact ⟨plan, ⟨GraftPlan.isNash_of_root_optimal hp hq (fun _ => h), hp, hq⟩, h⟩
  · rintro i ⟨plan, hplan, rfl⟩
    apply GraftPlan.root_optimal_of_isNash hplan.1
    rcases forced with h | h
    · exact Or.inl (by simpa only [h, Set.mem_singleton_iff] using
        (show G.winner plan.left ∈ G.possibleWinners from ⟨plan.left, hplan.2.1, rfl⟩))
    · exact Or.inr (by simpa only [h, Set.mem_singleton_iff] using
        (show H.winner plan.right ∈ H.possibleWinners from ⟨plan.right, hplan.2.2, rfl⟩))

/-- Public owned choice remains compositional for arbitrary continuations.
There is no SPE-existence premise: an empty child value makes the result empty. -/
theorem possibleWinners_eq_strictChoice (owner : Role) :
    possibleWinners owner G H = strictChoice owner G.possibleWinners H.possibleWinners := by
  classical
  by_cases empty : G.possibleWinners = ∅ ∨ H.possibleWinners = ∅
  · rw [strictChoice, ite_eq_left empty]
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro i ⟨p, hp, _⟩
    rcases empty with h | h
    · have hi : G.winner p.left ∈ G.possibleWinners := ⟨p.left, hp.2.1, rfl⟩
      simp only [h, Set.mem_empty_iff_false] at hi
    · have hi : H.winner p.right ∈ H.possibleWinners := ⟨p.right, hp.2.2, rfl⟩
      simp only [h, Set.mem_empty_iff_false] at hi
  · have left_nonempty : G.possibleWinners.Nonempty :=
      Set.nonempty_iff_ne_empty.mpr fun h => empty (Or.inl h)
    have right_nonempty : H.possibleWinners.Nonempty :=
      Set.nonempty_iff_ne_empty.mpr fun h => empty (Or.inr h)
    rw [strictChoice, ite_eq_right empty]
    split_ifs with forced
    · exact possibleWinners_eq_singleton left_nonempty right_nonempty forced
    · exact Set.Subset.antisymm (possibleWinners_subset_union owner)
        (union_subset_possibleWinners left_nonempty right_nonempty
          (fun h => forced (Or.inl h)) (fun h => forced (Or.inr h)))

/-- The empty-set extension agrees exactly with the existing winner algebra
whenever both continuation values are nonempty. -/
theorem strictChoice_winnerSet (owner : Role) (S T : WinnerSet Role) :
    strictChoice owner S.val T.val = (WinnerSet.choice owner S T).val := by
  classical
  have left_nonempty : S.val ≠ ∅ := S.property.ne_empty
  have right_nonempty : T.val ≠ ∅ := T.property.ne_empty
  have singleton_iff (A : WinnerSet Role) :
      A = WinnerSet.singleton owner ↔ A.val = {owner} := by
    constructor
    · rintro rfl
      rfl
    · intro h
      exact Subtype.ext h
  have forced_iff : (S = WinnerSet.singleton owner ∨ T = WinnerSet.singleton owner) ↔
      (S.val = {owner} ∨ T.val = {owner}) := or_congr (singleton_iff S) (singleton_iff T)
  by_cases forced : S = WinnerSet.singleton owner ∨ T = WinnerSet.singleton owner
  · rw [WinnerSet.choice, ite_eq_left forced]
    simp only [strictChoice, left_nonempty, right_nonempty, false_or,
      ↓reduceIte, forced_iff.mp forced, WinnerSet.singleton]
  · have not_forced : ¬ (S.val = {owner} ∨ T.val = {owner}) :=
      fun h => forced (forced_iff.mpr h)
    rw [WinnerSet.choice, ite_eq_right forced]
    simp only [strictChoice, left_nonempty, right_nonempty, false_or,
      ↓reduceIte, not_forced, WinnerSet.union]

end KFOL.InfiniteGames.PublicGrafting
