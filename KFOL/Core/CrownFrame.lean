module

public import KFOL.Definitions.CrownFrame
public import Mathlib.Logic.Equiv.Fin.Rotate

/-! # Separating all intervals of a cut crown

Explicit principal upsets are constant on the retained matching edges and
separate every other strict interval. The formula uses only set incidence
and the linear order obtained by deleting the wrapping edge. -/

@[expose] public section
namespace KFOL.Core.IntervalCrown.Frame
universe u
variable {Var : Type u} [Fintype Var] [DecidableEq Var] {m : ℕ}

@[simp] theorem cut_eq_true (G : Frame Var m) (A S : Finset Var) :
    G.cut A S = true ↔ A ⊆ S ∨ ∃ i : Fin m, i.val + 1 < m ∧ A ⊆ G.upper i ∧
      ∃ j : Fin m, j.val ≤ i.val ∧ G.lower j ⊆ S := by
  simp [cut]

theorem cut_mono (G : Frame Var m) (A : Finset Var) : Monotone (G.cut A) := by
  intro S T hST
  apply Bool.le_iff_imp.mpr
  intro h
  rcases (cut_eq_true G A S).mp h with h | ⟨i, hi, hAi, j, hji, hjS⟩
  · exact (cut_eq_true G A T).mpr (Or.inl (h.trans hST))
  · exact (cut_eq_true G A T).mpr (Or.inr ⟨i, hi, hAi, j, hji, hjS.trans hST⟩)

theorem cut_bot (G : Frame Var m) (A : Finset Var) (hA : A.Nonempty) :
    G.cut A ∅ = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  rcases (cut_eq_true G A ∅).mp h with h | ⟨i, hi, hAi, j, hji, hj⟩
  · obtain ⟨x, hx⟩ := hA
    simpa using h hx
  · obtain ⟨x, hx⟩ := G.lower_nonempty j
    simpa using hj hx

@[simp] theorem cut_top (G : Frame Var m) (A : Finset Var) :
    G.cut A Finset.univ = true :=
  (cut_eq_true G A Finset.univ).mpr (Or.inl (Finset.subset_univ _))

@[simp] theorem cut_self (G : Frame Var m) (A : Finset Var) : G.cut A A = true :=
  (cut_eq_true G A A).mpr (Or.inl Finset.Subset.rfl)

/-- Every retained cover has equal endpoint values under every principal cut. -/
theorem cut_edge (G : Frame Var m) (A : Finset Var) (i : Fin m)
    (hi : i.val + 1 < m) : G.cut A (G.lower i) = G.cut A (G.upper i) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact (Bool.le_iff_imp.mp (G.cut_mono A (G.cover i).le))
  · intro h
    apply (cut_eq_true G A (G.lower i)).mpr
    right
    rcases (cut_eq_true G A (G.upper i)).mp h with hAi | ⟨a, ha, hAa, j, hja, hji⟩
    · exact ⟨i, hi, hAi, i, le_rfl, Finset.Subset.rfl⟩
    · refine ⟨a, ha, hAa, i, ?_, Finset.Subset.rfl⟩
      rcases (G.incidence i j).mp hji with rfl | hj
      · exact hja
      · have hv : j.val = i.val + 1 := by
          have : NeZero m := i.neZero
          simp only [hj, finRotate_apply, Fin.val_add, Fin.val_one']
          rw [Nat.mod_eq_of_lt (by omega : 1 < m), Nat.mod_eq_of_lt hi]
        omega

/-- A strict interval outside the retained matching is separated by its upper cut. -/
theorem cut_separates (G : Frame Var m) (A B : Finset Var) (hAB : A ⊂ B)
    (hnot : (A, B) ∉ G.cutEdges) : G.cut B A = false ∧ G.cut B B = true := by
  refine ⟨?_, G.cut_self B⟩
  apply Bool.eq_false_iff.mpr
  intro h
  rcases (cut_eq_true G B A).mp h with hBA | ⟨i, hi, hBi, j, hji, hjA⟩
  · exact hAB.not_ge hBA
  · have hlowup : G.lower j ⊆ G.upper i := hjA.trans (hAB.le.trans hBi)
    rcases (G.incidence i j).mp hlowup with hj | hj
    · subst j
      have hAi : A = G.lower i := by
        rcases (G.cover i).eq_or_eq hjA (hAB.le.trans hBi) with hAi | hAu
        · exact hAi
        · exact False.elim (hAB.not_ge (hBi.trans hAu.ge))
      have hBi' : B = G.upper i := by
        rcases (G.cover i).eq_or_eq (hjA.trans hAB.le) hBi with hBl | hBu
        · exact False.elim (hAB.not_ge (hBl.le.trans hjA))
        · exact hBu
      exact hnot ⟨i, hi, by simp [hAi, hBi']⟩
    · have hv : j.val = i.val + 1 := by
        have : NeZero m := i.neZero
        simp only [hj, finRotate_apply, Fin.val_add, Fin.val_one']
        rw [Nat.mod_eq_of_lt (by omega : 1 < m), Nat.mod_eq_of_lt hi]
      omega

end KFOL.Core.IntervalCrown.Frame
