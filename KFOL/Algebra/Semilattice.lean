module

public import KFOL.Algebra.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Data.Finset.Lattice.Fold

/-! # Owned-choice semilattices and finite nonempty folds -/

@[expose] public section

namespace KFOL

universe u v w

namespace WinnerSet

variable {Role : Type u}

/-- Each owned choice is a genuine mathlib semilattice join. -/
@[instance_reducible] noncomputable def choiceSemilattice (r : Role) : SemilatticeSup (WinnerSet Role) :=
  letI : Max (WinnerSet Role) := ⟨choice r⟩
  SemilatticeSup.mk' (fun A B => choice_comm A B r)
    (fun A B C => choice_assoc A B r C) (choice_idempotent r)

/-- The owner's singleton is raised to top; otherwise this is ordinary set
inclusion, excluding that singleton as a lower value. -/
theorem choice_le_iff (r : Role) (A B : WinnerSet Role) :
    @LE.le (WinnerSet Role) (choiceSemilattice r).toLE A B ↔ B = singleton r ∨ (A ≠ singleton r ∧ A.val ⊆ B.val) := by
  classical
  change choice r A B = B ↔ _
  by_cases hb : B = singleton r
  · simp [choice,hb]
  by_cases ha : A = singleton r
  · simp [choice,ha,hb,Ne.symm hb]
  simp only [choice,ha,hb,or_self,ite_false,false_or]
  constructor
  · intro he
    refine ⟨ha,fun x hx => ?_⟩
    have hm : x ∈ (A.union B).val := Or.inl hx
    exact he ▸ hm
  · rintro ⟨_,hsub⟩
    apply Subtype.ext
    exact Set.union_eq_right.mpr hsub

/-- A finite nonempty owned-choice fold uses mathlib's semilattice fold. -/
noncomputable def choiceFold {Index : Type v} (r : Role) (S : Finset Index)
    (hS : S.Nonempty) (v : Index → WinnerSet Role) : WinnerSet Role :=
  letI := choiceSemilattice r
  S.sup' hS v

/-- The fold reaches the owner atom exactly when some operand is that atom. -/
theorem choiceFold_eq_owner_iff {Index : Type v} (r : Role) (S : Finset Index)
    (hS : S.Nonempty) (v : Index → WinnerSet Role) :
    choiceFold r S hS v = singleton r ↔ ∃ i ∈ S, v i = singleton r := by
  classical
  let := choiceSemilattice r
  constructor
  · intro he
    by_contra hno
    have hleaf : ∀ i ∈ S, v i ≠ singleton r := by
      intro i hi hv
      exact hno ⟨i,hi,hv⟩
    have hfold : choiceFold r S hS v ≠ singleton r :=
      Finset.sup'_induction hS v (p := fun A : WinnerSet Role => A ≠ singleton r)
        (fun A ha B hb => by
          change choice r A B ≠ singleton r
          rw [ne_eq,choice_eq_owner_iff]
          exact fun h => h.elim ha hb) hleaf
    exact hfold he
  · rintro ⟨i,hi,he⟩
    have hle : @LE.le (WinnerSet Role) (choiceSemilattice r).toLE (v i) (choiceFold r S hS v) := Finset.le_sup' v hi
    rw [he] at hle
    rcases (choice_le_iff r _ _).mp hle with h | ⟨h,_⟩
    · exact h
    · exact False.elim (h rfl)

/-- In the absence of an absorbing operand, the finite fold is exactly union. -/
theorem mem_choiceFold_of_no_owner {Index : Type v} (r : Role) (S : Finset Index)
    (hS : S.Nonempty) (v : Index → WinnerSet Role)
    (hn : ∀ i ∈ S, v i ≠ singleton r) (a : Role) :
    a ∈ (choiceFold r S hS v).val ↔ ∃ i ∈ S, a ∈ (v i).val := by
  classical
  let := choiceSemilattice r
  have hfold : choiceFold r S hS v ≠ singleton r := by
    rw [ne_eq,choiceFold_eq_owner_iff]
    rintro ⟨i,hi,he⟩
    exact hn i hi he
  have hsub : (choiceFold r S hS v).val ⊆ {a | ∃ i ∈ S, a ∈ (v i).val} :=
    Finset.sup'_induction hS v (p := fun A : WinnerSet Role => A.val ⊆ {a | ∃ i ∈ S, a ∈ (v i).val})
      (fun A hA B hB => (choice_subset_union r A B).trans (Set.union_subset hA hB))
      (fun i hi a ha => ⟨i,hi,ha⟩)
  constructor
  · exact fun h => hsub h
  · rintro ⟨i,hi,ha⟩
    have hle : @LE.le (WinnerSet Role) (choiceSemilattice r).toLE (v i) (choiceFold r S hS v) := Finset.le_sup' v hi
    exact ((choice_le_iff r _ _).mp hle).resolve_left hfold |>.2 ha

end WinnerSet

namespace Term

variable {Role : Type u} {Var : Type v}

/-- Every finite nonempty fold has an actual binary owned-choice term,
allowing arbitrary existing terms as its action continuations. -/
theorem exists_choice_fold {Index : Type w} (r : Role) (S : Finset Index)
    (hS : S.Nonempty) (terms : Index → Term Role Var) :
    ∃ t : Term Role Var, ∀ v : Var → WinnerSet Role,
      t.eval v = WinnerSet.choiceFold r S hS (fun i => (terms i).eval v) := by
  let := WinnerSet.choiceSemilattice r
  have hp : ∃ t : Term Role Var, ∀ v : Var → WinnerSet Role,
      t.eval v = (S.sup' hS (fun i v => (terms i).eval v)) v :=
    Finset.sup'_induction hS (fun i v => (terms i).eval v)
      (p := fun f : (Var → WinnerSet Role) → WinnerSet Role =>
        ∃ t : Term Role Var, ∀ v, t.eval v = f v)
      (fun f ⟨s,hs⟩ g ⟨t,ht⟩ => ⟨.choice r s t,fun v => by
        change WinnerSet.choice r (s.eval v) (t.eval v) = WinnerSet.choice r (f v) (g v)
        rw [hs,ht]⟩)
      (fun i _ => ⟨terms i,fun _ => rfl⟩)
  obtain ⟨t,ht⟩ := hp
  refine ⟨t,fun v => ?_⟩
  exact (ht v).trans (Finset.sup'_apply hS _ v)

end Term

end KFOL
