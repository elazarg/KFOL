module

public import KFOL.Algebra

/-! Boundary cases: switches need not preserve one player's view, two roles
need not realize the impossible state, and the representation is subdirect
rather than the whole Cartesian product. -/

@[expose] public section

namespace KFOLTest.Views

open KFOL

private def A : WinnerSet (Fin 3) := WinnerSet.singleton 0
private def B : WinnerSet (Fin 3) := WinnerSet.union (WinnerSet.singleton 0) (WinnerSet.singleton 1)

example : WinnerSet.view 0 A = WinnerSet.view 0 B := by
  have hA : WinnerSet.view 0 A = .possible := (WinnerSet.view_eq_possible_iff _ _).mpr rfl
  have hB : WinnerSet.view 0 B = .possible :=
    (WinnerSet.view_eq_possible_iff _ _).mpr (Or.inl rfl)
  exact hA.trans hB.symm

example : WinnerSet.view 0 (WinnerSet.rename (Equiv.swap 0 2) A) ≠
    WinnerSet.view 0 (WinnerSet.rename (Equiv.swap 0 2) B) := by
  intro h
  have hs := ((WinnerSet.view_eq_view_iff _ _ _).mp h).2 2 (by decide)
  have hA : WinnerSet.rename (Equiv.swap 0 2) A = WinnerSet.singleton 2 := by
    simp [A]
  have hB := hs.mp hA
  have hm : (1 : Fin 3) ∈ (WinnerSet.rename (Equiv.swap 0 2) B).val :=
    ⟨1, Or.inr rfl, by decide⟩
  simp [hB] at hm

example (S : WinnerSet (Fin 2)) : WinnerSet.view 0 S ≠ .impossible := by
  intro h
  obtain ⟨hk, ha⟩ := (WinnerSet.view_eq_impossible_iff _ _).mp h
  apply ha 1
  apply WinnerSet.eq_singleton_of_subset
  intro x hx
  have hcases : x = 0 ∨ x = 1 := by omega
  exact hcases.elim (fun he => False.elim (hk (he ▸ hx))) id

example : ¬∃ S : WinnerSet (Fin 3), WinnerSet.view 0 S = .possible ∧
    WinnerSet.view 1 S = .other ⟨2, by decide⟩ := by
  rintro ⟨S, h0, h1⟩
  have hm := (WinnerSet.view_eq_possible_iff _ _).mp h0
  have he := (WinnerSet.view_eq_other_iff _ _ _).mp h1
  simp [he] at hm

end KFOLTest.Views
