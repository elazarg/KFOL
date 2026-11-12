module

public import KFOL.Core.IntervalCrownCompletion
public import KFOL.Core.PatchInterpolation

/-! # Local interpolation from the deletion patches of a Boolean crown

A valuation can distinguish the full operation from at most one deletion
patch. The number of patches is independent of the number of input variables. -/

@[expose] public section
namespace KFOL.Core.IntervalCrown.Frame
universe u v
variable {Var : Type u} [Fintype Var] [DecidableEq Var] [Nonempty Var]
    {m : ℕ}

/-- The common collapsed cover adds one more patch: the complete crown passes
interpolation on as many valuations as there are matching edges. -/
theorem operation_locallyInterpolable_sharp {Role : Type v} [Fintype Role]
    (three : Fin 3 ↪ Role) (G : Frame Var m) :
    LocallyInterpolable m (Intervals.operation (three 1) (three 2) (G.edges Set.univ)) := by
  classical
  have hp : Intervals.Proper (G.edges Set.univ) := by
    rintro L U ⟨i, _, h⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨G.lower_nonempty i, (G.cover i).lt, G.upper_ne_univ i⟩
  obtain ⟨cover, hcover, hcoverValue⟩ := Intervals.exists_collapsed_cover three (G.edges Set.univ) hp
  choose deleted hdeleted heval using fun i => G.exists_delete_completion three i
  let terms : Option (Fin m) → Term Role Var := fun o => o.elim cover deleted
  have hterms (o : Option (Fin m)) : (terms o).IsCore := by
    cases o with
    | none => exact hcover
    | some i => exact hdeleted i
  apply locallyInterpolable_of_finite_patches m (by simp) terms hterms
  intro values
  let p := (Intervals.lowerInputs (three 2) values, Intervals.upperInputs (three 1) values)
  by_cases hm : p ∈ G.edges Set.univ
  · obtain ⟨i, _, hpi⟩ := hm
    have hf : p ∈ G.edges Set.univ := ⟨i, Set.mem_univ _, hpi⟩
    refine ⟨some i, fun o ho => ?_⟩
    cases o with
    | none =>
      change cover.eval values = _
      rw [hcoverValue values hf]
      dsimp only [p] at hf
      simp only [Intervals.operation, ite_eq_left hf]
    | some j =>
      change (deleted j).eval values = _
      rw [heval j]
      have hji : j ≠ i := fun he => ho (congrArg some he)
      have hd : p ∈ G.deleteEdges j := ⟨i, Ne.symm hji, hpi⟩
      dsimp only [p] at hd hf
      simp only [Intervals.operation, ite_eq_left hd, ite_eq_left hf]
  · refine ⟨none, fun o ho => ?_⟩
    cases o with
    | none => exact False.elim (ho rfl)
    | some j =>
      change (deleted j).eval values = _
      rw [heval j]
      have hd : p ∉ G.deleteEdges j := by
        rintro ⟨i, _, hpi⟩
        exact hm ⟨i, Set.mem_univ _, hpi⟩
      dsimp only [p] at hd hm
      simp only [Intervals.operation, ite_eq_right hd, ite_eq_right hm]

/-- Every smaller interpolation test follows from the sharp bound. -/
theorem operation_locallyInterpolable {Role : Type v} [Fintype Role]
    (three : Fin 3 ↪ Role) (G : Frame Var m) (n : ℕ) (hn : n < m) :
    LocallyInterpolable n (Intervals.operation (three 1) (three 2) (G.edges Set.univ)) :=
  (G.operation_locallyInterpolable_sharp three).of_le (Nat.le_of_lt hn)

end KFOL.Core.IntervalCrown.Frame
