import KFOL.Core.GhostElimination

open KFOL

namespace CoreGhostEliminationTests

private def three : Fin 3 ↪ Fin 3 := Function.Embedding.refl _

-- With no ordinary inputs, the alternative must select zero: a nonempty
-- residual would require a constant-free term on the empty variable type.
example (t : Term (Fin 3) (Option Empty)) (ht : t.IsCore) :
    ∀ (v : Empty → WinnerSet (Fin 3)) (k : Fin 3),
      k ∉ (t.eval (fun j =>
        j.elim (PlayerView.representative three k .impossible) v)).val := by
  rcases Core.core_residual_alternative three t ht with hz | ⟨g, hg, _⟩
  · exact hz
  · obtain ⟨j, _⟩ := hg.vars_nonempty
    exact nomatch j

private def repeatedSource : Term (Fin 3) (Option Unit) :=
  .choice 0 (.var none) (.var none)

-- An available but unused ordinary input does not create a residual. This
-- also checks that the zero case cannot be mistaken for a core constant.
example :
    (∀ (v : Unit → WinnerSet (Fin 3)) (k : Fin 3),
      k ∉ (repeatedSource.eval (fun j =>
        j.elim (PlayerView.representative three k .impossible) v)).val) ∧
    ¬∃ g : Term (Fin 3) Unit, ∀ (v : Unit → WinnerSet (Fin 3)) (k : Fin 3),
      k ∈ (g.eval v).val ↔ k ∈ (repeatedSource.eval (fun j =>
        j.elim (PlayerView.representative three k .impossible) v)).val := by
  have hz : ∀ (v : Unit → WinnerSet (Fin 3)) (k : Fin 3),
      k ∉ (repeatedSource.eval (fun j =>
        j.elim (PlayerView.representative three k .impossible) v)).val := by
    intro v k
    simp [repeatedSource, Term.eval, WinnerSet.choice_self, PlayerView.representative]
  refine ⟨hz, ?_⟩
  rintro ⟨g, hg⟩
  let v : Unit → WinnerSet (Fin 3) := fun _ => WinnerSet.singleton 0
  obtain ⟨k, hk⟩ := (g.eval v).property
  exact hz v k ((hg v k).mp hk)

private def base : Term (Fin 3) (Fin 2) := .choice 0 (.var 0) (.var 1)

-- A genuine binary residual lifts into the fiber. Classifying that lift
-- excludes the projection branch, and every classified residual must equal
-- the original operation, rather than merely sharing its singleton profiles.
example : ∃ t : Term (Fin 3) (Option (Fin 2)), t.IsCore ∧
    (∀ (v : Fin 2 → WinnerSet (Fin 3)) (A : WinnerSet (Fin 3)) (r : Fin 3),
      t.eval (fun j => j.elim A v) = WinnerSet.singleton r ↔ A = WinnerSet.singleton r) ∧
    ∃ h : Term (Fin 3) (Fin 2), h.IsCore ∧
      (∀ (v : Fin 2 → WinnerSet (Fin 3)) (A : WinnerSet (Fin 3)),
        t.eval (fun j => j.elim A v) = (h.eval v).reset A) ∧
      (fun v => h.eval v) = (fun v => base.eval v) := by
  obtain ⟨t, ht, he⟩ := Core.exists_core_reset_lift three base (by trivial)
  have hp : ∀ (v : Fin 2 → WinnerSet (Fin 3)) (A : WinnerSet (Fin 3)) (r : Fin 3),
      t.eval (fun j => j.elim A v) = WinnerSet.singleton r ↔ A = WinnerSet.singleton r := by
    intro v A r
    rw [he, WinnerSet.reset_eq_singleton]
  refine ⟨t, ht, hp, ?_⟩
  rcases (Core.projection_fiber_iff three t ht).mp hp with hz | ⟨h, hh, hres⟩
  · exact (Core.reset_lift_ne_projection three (fun v => base.eval v)
      (fun v A => (he v A).symm.trans (hz v A))).elim
  · refine ⟨h, hh, hres, ?_⟩
    apply Core.reset_lift_injective three
    intro v A
    exact (hres v A).symm.trans (he v A)

-- Even over the empty ordinary variable type, the separation statement has
-- an actual valuation and cannot become vacuously true or false.
example (g : (Empty → WinnerSet (Fin 3)) → WinnerSet (Fin 3)) :
    ¬∀ (v : Empty → WinnerSet (Fin 3)) (A : WinnerSet (Fin 3)), (g v).reset A = A :=
  Core.reset_lift_ne_projection three g

private def erasureTrap : Term (Fin 3) (Option (Fin 2)) :=
  .choice 1 (.choice 0 (.var none) (.var (some 0))) (.var (some 1))

-- Simply erasing the zero-residual X child is insufficient at the next gate:
-- the ghost stops the resulting {1} from absorbing the other input {2}.
example :
    2 ∈ (erasureTrap.eval (fun j => j.elim
      (PlayerView.representative three 2 .impossible)
      (fun i : Fin 2 => WinnerSet.singleton (if i = 0 then 1 else 2)))).val ∧
    2 ∉ (WinnerSet.choice (1 : Fin 3) (WinnerSet.singleton 1)
      (WinnerSet.singleton 2)).val := by
  let A := PlayerView.representative three (2 : Fin 3) .impossible
  have hinner : WinnerSet.choice 0 A (WinnerSet.singleton 1) = A := by
    rw [WinnerSet.choice_comm]
    exact WinnerSet.choice_singleton_of_mem A 0 1 (by decide) (by change (1 : Fin 3) ≠ 2; decide)
  have ha : A ≠ WinnerSet.singleton 1 := by
    intro he
    have hm : (0 : Fin 3) ∈ A.val := by change (0 : Fin 3) ≠ 2; decide
    rw [he] at hm
    exact (by decide : (0 : Fin 3) ≠ 1) hm
  have houter : WinnerSet.choice 1 A (WinnerSet.singleton 2) =
      A.union (WinnerSet.singleton 2) := by
    apply ite_eq_right
    simp [ha]
  constructor
  · change 2 ∈ (WinnerSet.choice 1
      (WinnerSet.choice 0 A (WinnerSet.singleton 1)) (WinnerSet.singleton 2)).val
    rw [hinner, houter]
    exact Or.inr rfl
  · simp [WinnerSet.choice]

end CoreGhostEliminationTests
