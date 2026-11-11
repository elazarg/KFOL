module

public import KFOL.Algebra.Basic
public import KFOL.Definitions.Counting
public import Lean.Elab.Tactic.Omega

/-! # Exact winner accounting and occurrence budgets -/

@[expose] public section

namespace KFOL

universe u v
variable {Role : Type u} {Var : Type v} [Finite Role]

namespace WinnerSet

omit [Finite Role] in
@[simp] theorem ncard_rename (p : Equiv.Perm Role) (A : WinnerSet Role) :
    (rename p A).val.ncard = A.val.ncard :=
  Set.ncard_image_of_injective A.val p.injective

theorem choice_ncard_le (r : Role) (A B : WinnerSet Role) :
    (choice r A B).val.ncard ≤ A.val.ncard + B.val.ncard := by
  classical
  have ha := A.property.ncard_pos
  have hb := B.property.ncard_pos
  unfold choice
  split_ifs
  · simp only [val_singleton, Set.ncard_singleton]
    omega
  · exact Set.ncard_union_le A.val B.val

theorem choice_ncard_accounting (r : Role) (A B : WinnerSet Role) :
    (choice r A B).val.ncard + (A.val ∩ B.val).ncard +
      (if A = singleton r ∨ B = singleton r
       then (A.val ∪ B.val).ncard - 1 else 0) = A.val.ncard + B.val.ncard := by
  classical
  have hu := (union A B).property.ncard_pos
  have hi := Set.ncard_union_add_ncard_inter A.val B.val
  unfold choice
  split_ifs <;> simp only [val_singleton, Set.ncard_singleton, val_union] at * <;> omega

theorem choice_ncard_eq_add_iff (r : Role) (A B : WinnerSet Role) :
    (choice r A B).val.ncard = A.val.ncard + B.val.ncard ↔
      ¬(A = singleton r ∨ B = singleton r) ∧ Disjoint A.val B.val := by
  classical
  by_cases h : A = singleton r ∨ B = singleton r
  · have ha := A.property.ncard_pos
    have hb := B.property.ncard_pos
    simp only [choice, h, ↓reduceIte, val_singleton, Set.ncard_singleton, not_true_eq_false,
      false_and, iff_false]
    omega
  · simp only [choice, h, ↓reduceIte, val_union, not_false_eq_true, true_and]
    exact Set.ncard_union_eq_iff

end WinnerSet

namespace Term

theorem winner_accounting (t : Term Role Var) (ν : Var → WinnerSet Role) :
    (t.eval ν).val.ncard + t.overlapLoss ν + t.absorptionLoss ν = t.leafMass ν := by
  induction t with
  | winner r => simp [eval, overlapLoss, absorptionLoss, leafMass]
  | var x => simp [eval, overlapLoss, absorptionLoss, leafMass]
  | choice r s t ihs iht =>
    have h := WinnerSet.choice_ncard_accounting r (s.eval ν) (t.eval ν)
    simp only [eval, overlapLoss, absorptionLoss, leafMass]
    omega
  | rename p t ih => simpa [eval, overlapLoss, absorptionLoss, leafMass] using ih

theorem winner_budget (t : Term Role Var) (ν : Var → WinnerSet Role) :
    (t.eval ν).val.ncard ≤ min (Nat.card Role) (t.leafMass ν) := by
  have h := winner_accounting t ν
  exact le_min (Set.ncard_le_card _) (by omega)

theorem leafMass_eq (t : Term Role Var) (ν : Var → WinnerSet Role) :
    t.leafMass ν = t.choiceCount + 1 + t.inputExcess ν := by
  induction t with
  | winner r => simp [leafMass, choiceCount, inputExcess]
  | var x =>
    have h := (ν x).property.ncard_pos
    simp only [leafMass, choiceCount, inputExcess]
    omega
  | choice r s t ihs iht =>
    simp only [leafMass, choiceCount, inputExcess]
    omega
  | rename p t ih => exact ih

theorem winner_budget_eq_iff (t : Term Role Var) (ν : Var → WinnerSet Role) :
    (t.eval ν).val.ncard = t.leafMass ν ↔ t.DisjointChoices ν := by
  induction t with
  | winner r => simp [eval, leafMass, DisjointChoices]
  | var x => simp [eval, leafMass, DisjointChoices]
  | choice r s t ihs iht =>
    have hs := winner_budget s ν
    have ht := winner_budget t ν
    have hc := WinnerSet.choice_ncard_le r (s.eval ν) (t.eval ν)
    simp only [le_min_iff] at hs ht
    simp only [eval, leafMass, DisjointChoices]
    constructor
    · intro h
      have heq : (WinnerSet.choice r (s.eval ν) (t.eval ν)).val.ncard =
          (s.eval ν).val.ncard + (t.eval ν).val.ncard := by omega
      have hlocal := (WinnerSet.choice_ncard_eq_add_iff r (s.eval ν) (t.eval ν)).mp heq
      exact ⟨ihs.mp (by omega), iht.mp (by omega), hlocal⟩
    · rintro ⟨hs', ht', hlocal⟩
      rw [(WinnerSet.choice_ncard_eq_add_iff r (s.eval ν) (t.eval ν)).mpr hlocal,
        ihs.mpr hs', iht.mpr ht']
  | rename p t ih => simpa [eval, leafMass, DisjointChoices] using ih

theorem winner_budget_absorbing (t : Term Role Var) (ν : Var → WinnerSet Role) :
    (t.eval ν).val.ncard + t.absorbingCount ν ≤ t.leafMass ν := by
  classical
  induction t with
  | winner r => simp [eval, absorbingCount, leafMass]
  | var x => simp [eval, absorbingCount, leafMass]
  | choice r s t ihs iht =>
    have hc := WinnerSet.choice_ncard_le r (s.eval ν) (t.eval ν)
    have hs := (s.eval ν).property.ncard_pos
    have ht := (t.eval ν).property.ncard_pos
    simp only [eval, absorbingCount, leafMass]
    split_ifs with h
    · have hv : WinnerSet.choice r (s.eval ν) (t.eval ν) = WinnerSet.singleton r := by
        simp [WinnerSet.choice, h]
      rw [hv]
      simp only [WinnerSet.val_singleton, Set.ncard_singleton]
      omega
    · omega
  | rename p t ih => simpa [eval, absorbingCount, leafMass] using ih

theorem atomic_winner_budget (t : Term Role Var) (ν : Var → WinnerSet Role)
    (atomic : ∀ x, (ν x).val.ncard = 1) :
    (t.eval ν).val.ncard ≤ min (Nat.card Role) (t.choiceCount + 1) := by
  have hz : t.inputExcess ν = 0 := by
    induction t with
    | winner r => rfl
    | var x => simp only [inputExcess, atomic, Nat.sub_self]
    | choice r s t ihs iht => simp only [inputExcess, ihs, iht, Nat.add_zero]
    | rename p t ih => exact ih
  simpa [leafMass_eq, hz] using winner_budget t ν

end Term
end KFOL
