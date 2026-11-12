module

public import KFOL.Core.CrownFrame
public import KFOL.Core.IntervalCompletion

/-! # Actual core realizations of cut crown frames

The explicit principal cuts provide the hypotheses of the full-winner
interval completion theorem. No atomic-only realization is substituted for
the winner-valued deletion patch. -/

@[expose] public section
namespace KFOL.Core.IntervalCrown.Frame
universe u v
variable {Var : Type u} [Fintype Var] [DecidableEq Var] {m : ℕ}

/-- The retained matching intervals avoid the two endpoints of the Boolean lattice. -/
theorem cutEdges_proper (G : Frame Var m) : Intervals.Proper G.cutEdges := by
  rintro L U ⟨i, _hi, h⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  exact ⟨G.lower_nonempty i, (G.cover i).lt, G.upper_ne_univ i⟩

/-- Every nonempty principal cut is a normalized allowed Boolean profile. -/
theorem cut_good (G : Frame Var m) (A : Finset Var) (hA : A.Nonempty) :
    Intervals.Good G.cutEdges (G.cut A) := by
  refine ⟨G.cut_mono A, G.cut_bot A hA, G.cut_top A, ?_⟩
  rintro L U ⟨i, hi, h⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  exact G.cut_edge A i hi

/-- There is a normalized separator for every unselected strict interval. -/
theorem cutEdges_separates (G : Frame Var m) (A B : Finset Var) (hAB : A ⊂ B)
    (hnot : (A, B) ∉ G.cutEdges) : Intervals.Separates G.cutEdges A B := by
  have hB : B.Nonempty := by
    by_contra hh
    have he : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hh
    subst B
    simp at hAB
  obtain ⟨hA, hB'⟩ := G.cut_separates A B hAB hnot
  exact ⟨G.cut B, G.cut_good B hB, hA, hB'⟩

/-- Deleting the wrapping interval of any crown frame yields a genuine core operation. -/
theorem exists_cut_completion {Role : Type v} [Fintype Role] [Nonempty Var]
    (three : Fin 3 ↪ Role) (G : Frame Var m) :
    ∃ t : Term Role Var, t.IsCore ∧ ∀ values,
      t.eval values = Intervals.operation (three 1) (three 2) G.cutEdges values :=
  Intervals.exists_completion three G.cutEdges G.cutEdges_proper G.cutEdges_separates

/-- Every one-edge deletion of a crown frame is a core operation on all winner inputs. -/
theorem exists_delete_completion {Role : Type v} [Fintype Role] [Nonempty Var]
    (three : Fin 3 ↪ Role) (G : Frame Var m) (h : Fin m) :
    ∃ t : Term Role Var, t.IsCore ∧ ∀ values,
      t.eval values = Intervals.operation (three 1) (three 2) (G.deleteEdges h) values := by
  classical
  cases m with
  | zero => exact Fin.elim0 h
  | succ n =>
    let e : Equiv.Perm (Fin (n+1)) := finCycle (h - Fin.last n)
    have he (i : Fin (n+1)) :
        e (finRotate (n+1) i) = finRotate (n+1) (e i) := by
      simp only [e, finCycle_apply, finRotate_apply]
      simp only [add_assoc, add_left_comm, add_comm]
    have hlast : e (Fin.last n) = h := by
      simp only [e, finCycle_apply]
      exact add_sub_cancel _ _
    have hn (i : Fin (n+1)) : i.val + 1 < n+1 ↔ i ≠ Fin.last n := by
      constructor
      · intro hi hh
        have hv := congrArg Fin.val hh
        simp only [Fin.val_last] at hv
        omega
      · intro hi
        have hv : i.val ≠ n := fun hv => hi (Fin.ext hv)
        omega
    let G' := G.reindex e he
    obtain ⟨t, ht, hvalue⟩ := G'.exists_cut_completion three
    have hEdges : G'.cutEdges = G.deleteEdges h := by
      ext p
      constructor
      · rintro ⟨i, hi, hp⟩
        refine ⟨e i, ?_, hp⟩
        change e i ≠ h
        rw [← hlast]
        exact e.injective.ne ((hn i).mp hi)
      · rintro ⟨i, hi, hp⟩
        refine ⟨e.symm i, (hn _).mpr ?_, ?_⟩
        · intro hh
          apply hi
          rw [← e.apply_symm_apply i, hh, hlast]
        · simpa only [G', reindex, e.apply_symm_apply] using hp
    exact ⟨t, ht, fun values => by rw [hvalue, hEdges]⟩

end KFOL.Core.IntervalCrown.Frame
