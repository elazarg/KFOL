module

public import KFOL.Congruences.Basic

/-! # Class-maximum closures and exact owner-atom constraints -/

@[expose] public section

namespace KFOL.WinnerSet

universe u

variable {Role : Type u}

namespace Congruence

/-- The greatest element of the actual finite congruence class. -/
noncomputable def classMaximum [Finite Role] (θ : Congruence Role) (three : Fin 3 ↪ Role)
    (A : WinnerSet Role) : WinnerSet Role := (θ.exists_classMaximum three A).choose

theorem related_classMaximum [Finite Role] (θ : Congruence Role) (three : Fin 3 ↪ Role)
    (A : WinnerSet Role) : θ.r A (θ.classMaximum three A) := (θ.exists_classMaximum three A).choose_spec.1

theorem le_classMaximum [Finite Role] (θ : Congruence Role) (three : Fin 3 ↪ Role)
    {A B : WinnerSet Role} (h : θ.r A B) : B ≤ θ.classMaximum three A :=
  (θ.exists_classMaximum three A).choose_spec.2 B h

theorem classMaximum_eq_of_related [Finite Role] (θ : Congruence Role) (three : Fin 3 ↪ Role)
    {A B : WinnerSet Role} (h : θ.r A B) : θ.classMaximum three A = θ.classMaximum three B := by
  apply le_antisymm
  · exact θ.le_classMaximum three (θ.trans (θ.symm h) (θ.related_classMaximum three A))
  · exact θ.le_classMaximum three (θ.trans h (θ.related_classMaximum three B))

/-- The class-maximum map is a mathlib closure operator in the ordinary
subset order on the nonempty winner carrier. -/
noncomputable def closureOperator [Finite Role] (θ : Congruence Role) (three : Fin 3 ↪ Role) :
    ClosureOperator (WinnerSet Role) where
  toFun := θ.classMaximum three
  monotone' := by
    intro A B hAB
    have hh := θ.union three (θ.related_classMaximum three A) (θ.refl B)
    have hu : A.union B = B := Subtype.ext (Set.union_eq_right.mpr hAB)
    rw [hu] at hh
    exact Set.Subset.trans Set.subset_union_left (θ.le_classMaximum three hh)
  le_closure' A := θ.le_classMaximum three (θ.refl A)
  idempotent' A := (θ.classMaximum_eq_of_related three (θ.related_classMaximum three A)).symm

theorem closureOperator_rel_iff [Finite Role] (θ : Congruence Role) (three : Fin 3 ↪ Role)
    (A B : WinnerSet Role) : θ.closureOperator three A = θ.closureOperator three B ↔ θ.r A B := by
  constructor
  · intro h
    have ha := θ.related_classMaximum three A
    have hb := θ.related_classMaximum three B
    change θ.classMaximum three A = θ.classMaximum three B at h
    rw [h] at ha
    exact θ.trans ha (θ.symm hb)
  · exact θ.classMaximum_eq_of_related three

theorem closureOperator_atom [Finite Role] [Nonempty Role] (θ : Congruence Role) (three : Fin 3 ↪ Role) :
    AtomClosure (θ.closureOperator three) := by
  intro owner
  by_cases h : θ.closureOperator three (singleton owner) = singleton owner
  · exact Or.inl h
  · apply Or.inr
    have hr := θ.atom_collapse_to_full three owner (θ.closureOperator three (singleton owner)) h
      (θ.related_classMaximum three (singleton owner))
    apply le_antisymm (le_full _)
    exact θ.le_classMaximum three hr

end Congruence

namespace ClosureOperator

/-- Equality with a singleton closure forces a nonempty input to be that
same singleton, by extensivity. -/
theorem input_eq_singleton_of_closure (c : ClosureOperator (WinnerSet Role))
    (A : WinnerSet Role) (owner : Role) (h : c A = singleton owner) : A = singleton owner := by
  have ha : A.val ⊆ {owner} := by
    have hle := c.le_closure A
    rw [h] at hle
    exact hle
  have hm : owner ∈ A.val := by
    obtain ⟨x,hx⟩ := A.property
    have hx' : x = owner := ha hx
    exact hx' ▸ hx
  apply Subtype.ext
  exact Set.Subset.antisymm ha (Set.singleton_subset_iff.mpr hm)

@[simp] theorem full [Nonempty Role] (c : ClosureOperator (WinnerSet Role)) : c WinnerSet.full = WinnerSet.full :=
  le_antisymm (le_full _) (c.le_closure _)

/-- Every closure has the familiar union normalization, even though its
nonempty-set domain does not have an empty-set bottom element. -/
theorem union_eq (c : ClosureOperator (WinnerSet Role)) (A B : WinnerSet Role) :
    c (A.union B) = c ((c A).union (c B)) := by
  apply le_antisymm
  · apply c.monotone
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl (c.le_closure A hx)
    · exact Or.inr (c.le_closure B hx)
  · have hu : (c A).union (c B) ≤ c (A.union B) := by
      intro x hx
      rcases hx with hx | hx
      · exact c.monotone Set.subset_union_left hx
      · exact c.monotone Set.subset_union_right hx
    exact (c.monotone hu).trans_eq (c.idempotent _)

/-- A singleton closing to full forces every union containing an equivalent
operand to close to full as well. -/
theorem union_full_of_atom_equiv [Nonempty Role] (c : ClosureOperator (WinnerSet Role))
    (hc : AtomClosure c) (owner : Role) (A B : WinnerSet Role)
    (hA : c A = c (singleton owner)) (hnot : A ≠ singleton owner) : c (A.union B) = WinnerSet.full := by
  have hnotclosed : c (singleton owner) ≠ singleton owner := by
    intro he
    exact hnot (input_eq_singleton_of_closure c A owner (hA.trans he))
  have hatop := (hc owner).resolve_left hnotclosed
  apply le_antisymm (le_full _)
  rw [← hatop,← hA]
  exact c.monotone Set.subset_union_left

/-- Owner-compatible closures induce a congruence of all owned choices,
without presupposing that their kernels are operation-compatible. -/
def kernel [Nonempty Role] (c : ClosureOperator (WinnerSet Role)) (hc : AtomClosure c) : Congruence Role where
  toSetoid := Setoid.ker c
  choice owner := by
    intro A B C D hAC hBD
    change c A = c C at hAC
    change c B = c D at hBD
    change c (choice owner A B) = c (choice owner C D)
    classical
    by_cases hleft : A = singleton owner ∨ B = singleton owner
    · by_cases hright : C = singleton owner ∨ D = singleton owner
      · simp only [choice,ite_eq_left hleft,ite_eq_left hright]
      · have hC : C ≠ singleton owner := fun h => hright (Or.inl h)
        have hD : D ≠ singleton owner := fun h => hright (Or.inr h)
        rw [choice,ite_eq_left hleft,choice,ite_eq_right hright]
        rcases hleft with rfl | rfl
        · have he : c (C.union D) = WinnerSet.full :=
            union_full_of_atom_equiv c hc owner C D hAC.symm hC
          rw [he]
          exact (hc owner).resolve_left (fun hh => hC
            (input_eq_singleton_of_closure c C owner (hAC.symm.trans hh)))
        · have he : c (D.union C) = WinnerSet.full :=
            union_full_of_atom_equiv c hc owner D C hBD.symm hD
          rw [union_comm] at he
          rw [he]
          exact (hc owner).resolve_left (fun hh => hD
            (input_eq_singleton_of_closure c D owner (hBD.symm.trans hh)))
    · by_cases hright : C = singleton owner ∨ D = singleton owner
      · have hA : A ≠ singleton owner := fun h => hleft (Or.inl h)
        have hB : B ≠ singleton owner := fun h => hleft (Or.inr h)
        rw [choice,ite_eq_right hleft,choice,ite_eq_left hright]
        rcases hright with rfl | rfl
        · exact union_full_of_atom_equiv c hc owner A B hAC hA |>.trans
            ((hc owner).resolve_left (fun hh => hA
              (input_eq_singleton_of_closure c A owner (hAC.trans hh)))).symm
        · have he := union_full_of_atom_equiv c hc owner B A hBD hB
          rw [union_comm] at he
          exact he.trans ((hc owner).resolve_left (fun hh => hB
            (input_eq_singleton_of_closure c B owner (hBD.trans hh)))).symm
      · simp only [choice,ite_eq_right hleft,ite_eq_right hright]
        rw [union_eq c A B, union_eq c C D,hAC,hBD]

end ClosureOperator

end KFOL.WinnerSet
