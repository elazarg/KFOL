module

public import KFOL.Algebra.Semilattice
public import KFOL.Algebra.SemilatticeTrace

/-! Three clones preserve the operation membership problem and exclude every
one-owner fold from the pointwise lower bounds. -/

@[expose] public section
namespace KFOL.Core.ThreePortPadding

open WinnerSet

variable {Role X : Type*}

noncomputable def port (r s : Role) (v : X × Fin 3 → WinnerSet Role) (x : X) :
    WinnerSet Role :=
  choice s (choice r (v (x, 0)) (v (x, 1))) (v (x, 2))

private def portTerm (r s : Role) (x : X) : Term Role (X × Fin 3) :=
  .choice s (.choice r (.var (x, 0)) (.var (x, 1))) (.var (x, 2))

/-- A table is a term operation if and only if its three-port expansion is. -/
theorem realization_iff (r s : Role) (f : (X → WinnerSet Role) → WinnerSet Role) :
    (∃ t : Term Role X, t.IsCore ∧ ∀ v, t.eval v = f v) ↔
      (∃ t : Term Role (X × Fin 3), t.IsCore ∧ ∀ v, t.eval v = f (port r s v)) := by
  classical
  constructor
  · rintro ⟨t, core, eq⟩
    refine ⟨t.subst (portTerm r s), core.subst _ (fun _ _ => ⟨⟨trivial, trivial⟩, trivial⟩), ?_⟩
    intro v
    rw [Term.eval_subst]
    exact eq _
  · rintro ⟨t, core, eq⟩
    refine ⟨t.subst (fun j => .var j.1), core.subst _ (fun _ _ => trivial), ?_⟩
    intro v
    rw [Term.eval_subst]
    have diagonal : port r s (fun j => v j.1) = v := by
      funext x
      simp [port]
    simpa only [Term.eval, diagonal] using eq (fun j => v j.1)

/-- Even testing on assignments constant across ports of the same index
excludes every nonempty one-owner fold. -/
theorem no_fold_below (r s z : Role) (distinct : r ≠ s)
    (f : (X → WinnerSet Role) → WinnerSet Role)
    (unanimous : ∀ a, f (fun _ => singleton a) = singleton a)
    (H : Finset (X × Fin 3)) (nonempty : H.Nonempty) :
    ¬∀ v, (choiceFold z H nonempty v).val ⊆ (f (port r s v)).val := by
  classical
  intro bounded
  have contradictionAt (v : X × Fin 3 → WinnerSet Role) (a b : Role)
      (ne : a ≠ b) (fold : choiceFold z H nonempty v = singleton a)
      (image : ∀ x, port r s v x = singleton b) : False := by
    have hp := bounded v
    rw [fold, show port r s v = fun _ => singleton b from funext image, unanimous] at hp
    exact ne (hp (show a ∈ (singleton a).val from rfl))
  by_cases use : ∃ j ∈ H, j.2 ≠ 2
  · obtain ⟨j, hj, notLast⟩ := use
    let other : Role := if z = r then s else r
    let v : X × Fin 3 → WinnerSet Role := fun i =>
      if i.2 = j.2 then singleton z else singleton other
    have hne : z ≠ other := by
      by_cases hr : z = r
      · simpa [other, hr] using distinct
      · simp [other, hr]
    apply contradictionAt v z other hne
    · exact (choiceFold_eq_owner_iff z H nonempty v).mpr ⟨j, hj, by simp [v]⟩
    · intro x
      have last : v (x, 2) = singleton other := ite_eq_right (Ne.symm notLast)
      unfold port
      rw [last]
      by_cases hr : z = r
      · rw [show other = s from ite_eq_left hr]
        exact (choice_eq_owner_iff _ _ _).mpr (Or.inr rfl)
      · have hor : other = r := ite_eq_right hr
        rw [hor]
        have absorbed : choice r (v (x, 0)) (v (x, 1)) = singleton r := by
          apply (choice_eq_owner_iff _ _ _).mpr
          by_cases h0 : (0 : Fin 3) = j.2
          · right
            have h1 : (1 : Fin 3) ≠ j.2 := by rw [← h0]; decide
            simp [v, h1, hor]
          · left
            simp [v, h0, hor]
        rw [absorbed, choice_self]
  · let v : X × Fin 3 → WinnerSet Role := fun i =>
      if i.2 = 2 then singleton r else singleton s
    have all : ∀ j ∈ H, v j = singleton r := by
      intro j hj
      exact ite_eq_left (by_contra fun h => use ⟨j, hj, h⟩)
    apply contradictionAt v r s distinct
    · by_cases hz : z = r
      · subst z
        obtain ⟨j, hj⟩ := nonempty
        exact (choiceFold_eq_owner_iff r _ _ _).mpr ⟨j, hj, all j hj⟩
      · exact (choiceFold_eq_other_iff z r hz _ _ _).mpr all
    · intro x
      have first : v (x, 0) = WinnerSet.singleton s := ite_eq_right (show (0 : Fin 3) ≠ 2 by decide)
      have second : v (x, 1) = WinnerSet.singleton s := ite_eq_right (show (1 : Fin 3) ≠ 2 by decide)
      rw [port, first, second, choice_self]
      exact (choice_eq_owner_iff _ _ _).mpr (Or.inl rfl)

end KFOL.Core.ThreePortPadding
