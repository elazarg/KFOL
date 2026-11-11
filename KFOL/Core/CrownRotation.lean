module

public import KFOL.Core.CrownRegions
public import KFOL.Algebra.SemilatticeTrace

/-! # Relabelling cyclic exceptional regions -/

@[expose] public section
namespace KFOL.Core.Crown
open WinnerSet
universe u v
variable {Role : Type u} {Var : Type v}

theorem cylinder_relabel (b c : Role) (next e : Equiv.Perm Var)
    (he : ∀ i, e (next i) = next (e i)) (i : Var) (v : Var → WinnerSet Role) :
    Cylinder b c next i (fun j => v (e j)) ↔ Cylinder b c next (e i) v := by
  constructor
  · rintro ⟨hc, hb, hnc, hrest⟩
    refine ⟨hc, ?_, ?_, ?_⟩
    · simpa only [he] using hb
    · simpa only [he] using hnc
    · intro j hji hjn
      obtain ⟨k, rfl⟩ := e.surjective j
      exact hrest k (fun hk => hji (congrArg e hk))
        (fun hk => hjn ((congrArg e hk).trans (he i)))
  · rintro ⟨hc, hb, hnc, hrest⟩
    refine ⟨hc, ?_, ?_, ?_⟩
    · simpa only [he] using hb
    · simpa only [he] using hnc
    · intro j hji hjn
      exact hrest (e j) (e.injective.ne hji)
        (fun h => hjn (e.injective (h.trans (he i).symm)))

theorem inputUnion_relabel [Nonempty Var] (e : Equiv.Perm Var)
    (v : Var → WinnerSet Role) :
    inputUnion (fun j => v (e j)) = inputUnion v := by
  apply Subtype.ext
  ext r
  simp only [inputUnion, Set.mem_iUnion]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨e j, hj⟩
  · rintro ⟨j, hj⟩
    obtain ⟨k, rfl⟩ := e.surjective j
    exact ⟨k, hj⟩

theorem operation_relabel [Nonempty Var] (b c : Role) (next e : Equiv.Perm Var)
    (he : ∀ i, e (next i) = next (e i)) (S : Set Var) (v : Var → WinnerSet Role) :
    operation b c next S (fun j => v (e j)) = operation b c next (e '' S) v := by
  classical
  have hcond : (∃ i ∈ S, Cylinder b c next i (fun j => v (e j))) ↔
      ∃ i ∈ e '' S, Cylinder b c next i v := by
    constructor
    · rintro ⟨i, hi, hc⟩
      exact ⟨e i, Set.mem_image_of_mem e hi, (cylinder_relabel b c next e he i v).mp hc⟩
    · rintro ⟨j, ⟨i, hi, rfl⟩, hc⟩
      exact ⟨i, hi, (cylinder_relabel b c next e he i v).mpr hc⟩
  unfold operation
  rw [hcond, inputUnion_relabel]

/-- A core base patch transports along every symmetry of the successor. -/
theorem core_patch_relabel [Nonempty Var] [DecidableEq Var]
    (b c : Role) (next e : Equiv.Perm Var) (he : ∀ i, e (next i) = next (e i))
    (h : Var) (base : Term Role Var) (hbase : base.IsCore)
    (hvalue : ∀ v, base.eval v = operation b c next {i | i ≠ h} v) :
    ∃ t : Term Role Var, t.IsCore ∧
      ∀ v, t.eval v = operation b c next {i | i ≠ e h} v := by
  let t := base.subst (fun i => Term.var (e i))
  have hcore : t.IsCore := hbase.subst (fun i => Term.var (e i)) (fun _ _ => trivial)
  have hS : e '' {i | i ≠ h} = {i | i ≠ e h} := by
    ext j
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact e.injective.ne hi
    · intro hj
      refine ⟨e.symm j, ?_, e.apply_symm_apply j⟩
      intro hi
      exact hj ((e.apply_symm_apply j).symm.trans (congrArg e hi))
  refine ⟨t, hcore, fun v => ?_⟩
  rw [Term.eval_subst]
  change base.eval (fun j => v (e j)) = _
  rw [hvalue, operation_relabel b c next e he, hS]

end KFOL.Core.Crown
