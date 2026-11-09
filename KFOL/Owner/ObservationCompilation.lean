module

public import KFOL.Owner.GuardEncoding
public import KFOL.Owner.Completeness

/-! # Linear compilation of an observer's own H into two resets -/
@[expose] public section
namespace KFOL.Owner.Term
universe u v
variable {Role : Type u} {Var : Type v} [DecidableEq Role]

@[simp] theorem compileObservation_step (observer : Role) (s t : Term Role Var) :
    (s.step t).compileObservation observer =
      (s.compileObservation observer).step (t.compileObservation observer) := rfl

@[simp] theorem compileObservation_guarded (observer r : Role) (x y z : Term Role Var) :
    (guarded r x y z).compileObservation observer =
      if r = observer then (z.compileObservation observer).step
        ((y.compileObservation observer).step (x.compileObservation observer))
      else guarded () (x.compileObservation observer) (y.compileObservation observer)
        (z.compileObservation observer) := rfl

@[simp] theorem root_compileObservation (observer : Role) (term : Term Role Var) :
    (term.compileObservation observer).root = term.root := by
  induction term using induction_owner with
  | var => rfl
  | step s t _ ht => exact ht
  | guarded r x y z hx _ _ =>
    rw [compileObservation_guarded]
    split <;> exact hx

/-- The original raw guard list is preserved exactly, even before the
semantic restriction to at most one other owner is imposed. -/
theorem guards_compileObservation (observer : Role) (term : Term Role Var) :
    ((term.compileObservation observer).withOwner false).guards true = term.guards observer := by
  induction term using induction_owner with
  | var => rfl
  | step s t hs ht =>
    simp only [compileObservation_step,withOwner_step,guards_step,root_withOwner,
      root_compileObservation,hs,ht]
  | guarded r x y z hx hy hz =>
    by_cases he : r = observer
    · simp only [compileObservation_guarded,he,ite_true,withOwner_step,guards_step,
        root_withOwner,root_compileObservation,root_step,hx,hy,hz,guards_guarded,List.map_append,List.append_assoc]
    · simp only [compileObservation_guarded,he,ite_false,withOwner_guarded,guards_guarded,
        Bool.false_eq_true,root_withOwner,root_compileObservation,hx,hy,hz]

/-- Universal implication reduces to the fixed one-owner raw guard checker
whenever the source uses at most the observer and one other actual owner. -/
theorem compileObservation_implication_iff [DecidableEq Var]
    (observer other background : Role) (hko : observer ≠ other)
    (hkb : observer ≠ background) (hob : other ≠ background)
    (left right : Term Role Var)
    (hl : left.OwnersIn (fun r => r = observer ∨ r = other))
    (hr : right.OwnersIn (fun r => r = observer ∨ r = other)) :
    coversB (((left.compileObservation observer).withOwner false).guards true)
      (((right.compileObservation observer).withOwner false).guards true) = true ↔
      ∀ valuation : Var → WinnerSet Role,
        observer ∈ (left.eval valuation).val → observer ∈ (right.eval valuation).val := by
  rw [guards_compileObservation,guards_compileObservation,coversB_correct]
  exact left.observation_implication_iff right observer other background hko hkb hob hl hr

omit [DecidableEq Role] in
theorem OwnersIn.mono {P Q : Role → Prop} {term : Term Role Var}
    (h : term.OwnersIn P) (implication : ∀ r, P r → Q r) : term.OwnersIn Q := by
  induction term using induction_owner with
  | var => trivial
  | step s t hs ht => exact ⟨hs h.1,ht h.2⟩
  | guarded r x y z hx hy hz =>
    exact ⟨implication r h.1,hx h.2.1,hy h.2.2.1,hz h.2.2.2⟩

end KFOL.Owner.Term

namespace KFOL.Owner
variable {Role : Type*} [DecidableEq Role]

/-- A finite family with at most one owner outside the observer fits the
independently defined two-owner observation theorem. -/
theorem exists_observation_owner (three : Fin 3 ↪ Role) (owners : Finset Role)
    (observer : Role) (small : (owners.erase observer).card ≤ 1) :
    ∃ other : Role, observer ≠ other ∧ ∀ r ∈ owners, r = observer ∨ r = other := by
  by_cases empty : owners.erase observer = ∅
  · obtain ⟨other,hne⟩ : ∃ other : Role, observer ≠ other := by
      by_cases he : observer = three 0
      · exact ⟨three 1,by simpa only [he] using three.injective.ne (show (0 : Fin 3) ≠ 1 by decide)⟩
      · exact ⟨three 0,he⟩
    refine ⟨other,hne,?_⟩
    intro r hr
    by_cases he : r = observer
    · exact Or.inl he
    · have hm : r ∈ owners.erase observer := Finset.mem_erase.mpr ⟨he,hr⟩
      rw [empty] at hm
      exact False.elim (Finset.notMem_empty r hm)
  · obtain ⟨other,hm⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    refine ⟨other,(Finset.mem_erase.mp hm).1.symm,?_⟩
    intro r hr
    by_cases he : r = observer
    · exact Or.inl he
    · exact Or.inr ((Finset.card_le_one.mp small) r (Finset.mem_erase.mpr ⟨he,hr⟩) other hm)

end KFOL.Owner
