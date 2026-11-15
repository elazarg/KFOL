module

public import KFOL.Core.ProfileBudgets.Pruning
public import KFOL.Core.ProfileBudgets.Closure
public import KFOL.Core.Folds

/-! # Nonempty one-owner folds and their simultaneous safe supports -/

@[expose] public section
namespace KFOL.Core.ProfileBudgets
universe u v w
variable {Role : Type u} [DecidableEq Role] {Var : Type v} {Row : Type w}
attribute [local instance] Equational.coreStructure

inductive OwnedFold (r : Role) : CoreTerm Role Var → Prop
  | var (j : Var) : OwnedFold r (.var j)
  | choice {x y} : OwnedFold r x → OwnedFold r y → OwnedFold r (choiceTerm r x y)

omit [DecidableEq Role] in
theorem Prunes.ownedFold {r : Role} {t s : CoreTerm Role Var} (h : Prunes r t s) :
    OwnedFold r s := by
  induction h with
  | var j => exact .var j
  | owned _ _ ihx ihy => exact .choice ihx ihy
  | left _ _ ih => exact ih
  | right _ _ ih => exact ih

omit [DecidableEq Role] in
private theorem choice_bound_iff (r : Role) (x y : WinnerSet Role) (U : Set Role) :
    (WinnerSet.choice r x y).val ⊆ U ↔
      ((x.val ⊆ U ∧ y.val ⊆ U) ∨
        (r ∈ U ∧ (x = WinnerSet.singleton r ∨ y = WinnerSet.singleton r))) := by
  classical
  by_cases ha : x = WinnerSet.singleton r ∨ y = WinnerSet.singleton r
  · rw [WinnerSet.choice,ite_eq_left ha]
    change ({r} : Set Role) ⊆ U ↔ _
    rw [Set.singleton_subset_iff]
    constructor
    · exact fun h => Or.inr ⟨h,ha⟩
    · rintro (⟨hx,hy⟩ | ⟨hr,_⟩)
      · exact ha.elim (fun he => hx (by rw [he]; rfl)) (fun he => hy (by rw [he]; rfl))
      · exact hr
  · simp only [WinnerSet.choice,ite_eq_right ha,WinnerSet.union,Set.union_subset_iff]
    exact ⟨Or.inl,fun h => h.elim id (fun hh => (ha hh.2).elim)⟩

/-- Every one-owner word is a fold on a finite nonempty support, with exact
profile and upper-bound semantics. -/
theorem OwnedFold.support {r : Role} {t : CoreTerm Role Var} (h : OwnedFold r t) :
    ∃ S : Finset Var, S.Nonempty ∧
      (∀ q A, profile q A t = true ↔
        if q = r then ∃ j ∈ S, A j = true else ∀ j ∈ S, A j = true) ∧
      (∀ values : Var → WinnerSet Role, ∀ U : Set Role,
        (t.realize values).val ⊆ U ↔
          (∀ j ∈ S, (values j).val ⊆ U) ∨
            (r ∈ U ∧ ∃ j ∈ S, values j = WinnerSet.singleton r)) := by
  classical
  induction h with
  | var j =>
    refine ⟨{j},by simp,?_,?_⟩
    · intro q A
      by_cases hqr : q = r <;> simp [hqr]
    · intro values U
      simp only [FirstOrder.Language.Term.realize_var,Finset.mem_singleton,forall_eq,
        exists_eq_left]
      constructor
      · exact Or.inl
      · rintro (hh | ⟨hr,he⟩)
        · exact hh
        · rw [he]
          exact Set.singleton_subset_iff.mpr hr
  | @choice x y hx hy ihx ihy =>
    obtain ⟨S,hS,hSp,hSb⟩ := ihx
    obtain ⟨T,hT,hTp,hTb⟩ := ihy
    refine ⟨S ∪ T,hS.mono Finset.subset_union_left,?_,?_⟩
    · intro q A
      by_cases hqr : q = r
      · subst q
        simp only [profile_choice,ite_true,Bool.or_eq_true,hSp,hTp,
          Finset.mem_union,or_and_right,exists_or]
      · simp only [profile_choice,ite_eq_right (Ne.symm hqr),Bool.and_eq_true,hSp,hTp,
          ite_eq_right hqr,Finset.mem_union,or_imp,forall_and]
    · intro values U
      have atom (s : CoreTerm Role Var) (F : Finset Var)
          (hp : ∀ q A, profile q A s = true ↔
            if q = r then ∃ j ∈ F, A j = true else ∀ j ∈ F, A j = true) :
          s.realize values = WinnerSet.singleton r ↔
            ∃ j ∈ F, values j = WinnerSet.singleton r := by
        rw [winnerSet_eq_singleton_iff_profile,hp]
        simp only [ite_true,decide_eq_true_eq]
      change (WinnerSet.choice r (x.realize values) (y.realize values)).val ⊆ U ↔ _
      rw [choice_bound_iff,hSb,hTb,atom x S hSp,atom y T hTp]
      simp only [Finset.mem_union,or_imp,forall_and,or_and_right,exists_or]
      aesop

/-- Every finite nonempty safe support is realized by a one-owner fold. -/
theorem exists_fold_support (r : Role) (S : Finset Var) (hS : S.Nonempty) :
    ∃ t : CoreTerm Role Var,
      (∀ q A, profile q A t = true ↔
        if q = r then ∃ j ∈ S, A j = true else ∀ j ∈ S, A j = true) ∧
      ∀ b : Row → Budget Role Var, SafeSupport b r (S : Set Var) → Satisfies b t := by
  classical
  obtain ⟨j,hj⟩ := hS
  let t : CoreTerm Role Var := foldTerm r (S.toList.map fun j => .var j) (.var j)
  have hprof : ∀ q A, profile q A t = true ↔
      if q = r then ∃ k ∈ S, A k = true else ∀ k ∈ S, A k = true := by
    intro q A
    by_cases hqr : q = r
    · subst q
      simp only [t,profile_fold_owner,profile_var,ite_true]
      constructor
      · rintro (hh | ⟨s,hs,hsa⟩)
        · exact ⟨j,hj,hh⟩
        · obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hs
          exact ⟨k,Finset.mem_toList.mp hk,hsa⟩
      · rintro ⟨k,hk,hka⟩
        exact Or.inr ⟨.var k,List.mem_map.mpr ⟨k,Finset.mem_toList.mpr hk,rfl⟩,hka⟩
    · simp only [t,profile_fold_other r q (Ne.symm hqr),profile_var,
        List.forall_mem_map,Finset.mem_toList,ite_eq_right hqr]
      exact ⟨fun hh => hh.2,fun hh => ⟨hh j hj,hh⟩⟩
  refine ⟨t,hprof,?_⟩
  intro b hb
  have hf : OwnedFold r t := by
      have aux (xs : List Var) :
          OwnedFold r (foldTerm r (xs.map fun k => .var k) (.var j)) := by
        induction xs with
        | nil => exact .var j
        | cons k xs ih => exact .choice (.var k) ih
      exact aux _
  obtain ⟨T,_,hTp,hTb⟩ := hf.support
  have hT : T = S := by
    apply Finset.ext
    intro k
    have hh := (hTp r (fun l => decide (l = k))).symm.trans
      (hprof r (fun l => decide (l = k)))
    simpa only [ite_true,decide_eq_true_eq,exists_eq_right] using hh
  subst T
  intro i
  exact (hTb (b i).values (b i).allowed).mpr (hb i)

end KFOL.Core.ProfileBudgets
