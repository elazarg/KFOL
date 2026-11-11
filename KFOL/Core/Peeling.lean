module

public import KFOL.Core.AtomicInterpolation
public import KFOL.Core.BoundedGeneration
public import KFOL.Core.FiniteInterpolation

/-! # A direct row-deletion characterization of core interpolation

Boundary generators reduce the number of constrained rows. Minimal singleton
profiles then replace generation by rainbow intersections and one-positive
column tests. The resulting criterion has no auxiliary clause or fixed point.
-/

@[expose] public section
namespace KFOL.Core.Interpolation
open WinnerSet
universe u v w
variable {Role : Type u} {Row : Type v} {Var : Type w}
variable [DecidableEq Role] [DecidableEq Row]

omit [DecidableEq Role] [DecidableEq Row] in
private theorem boundary_fits_iff (values : Row → Var → WinnerSet Role)
    (N : Finset Row) (U : Row → Set Role) (D : Finset (Row × Role))
    (p : Option (Row × Role)) :
    (∃ t : Term Role Var, t.IsCore ∧ Fits N U D p (fun i => t.eval (values i))) ↔
      ∃ s : Term Role (BoundaryGenerator values N U), s.IsCore ∧
        Atomic D (fun i => s.eval (fun g => g.val i)) ∧
        Positive p (fun i => s.eval (fun g => g.val i)) := by
  constructor
  · rintro ⟨t, ht, hb, ha, hp⟩
    obtain ⟨s, hs, he⟩ := bounded_generated_by_boundary values N U t ht hb
    have heq := funext he
    exact ⟨s, hs, heq.symm ▸ ha, heq.symm ▸ hp⟩
  · rintro ⟨s, hs, ha, hp⟩
    obtain ⟨t, ht, hb, he⟩ := (boundary_generated_iff values N U
      (fun i => s.eval (fun g => g.val i))).mpr ⟨s, hs, fun _ => rfl⟩
    have heq := funext he
    exact ⟨t, ht, hb, heq.symm ▸ ha, heq.symm ▸ hp⟩

private theorem boundary_query_iff (values : Row → Var → WinnerSet Role)
    (N : Finset Row) (U : Row → Set Role) (D : Finset (Row × Role))
    (p : Option (Row × Role)) :
    (∃ g : BoundaryGenerator values N U, Atomic D g.val ∧ Positive p g.val) ↔
      (∃ j, Fits N U D p (fun i => values i j)) ∨
      ∃ i, ∃ _hi : i ∈ N, ∃ r ∈ U i, ∃ t : Term Role Var, t.IsCore ∧
        Fits (N.erase i) U (insert (i,r) D) p (fun q => t.eval (values q)) := by
  constructor
  · rintro ⟨g, ha, hp⟩
    rcases boundary_projection_or_atomic g with ⟨j, hj⟩ | ⟨i, hi, r, hr⟩
    · left
      have he := funext hj
      exact ⟨j, he ▸ boundary_bounded g, he ▸ ha, he ▸ hp⟩
    · right
      have hrU : r ∈ U i := by
        apply boundary_bounded g i hi
        rw [hr]
        exact Set.mem_singleton r
      obtain ⟨t, ht, he⟩ := boundary_realizer g
      have heq := funext he
      refine ⟨i, hi, r, hrU, t, ht, ?_, ?_, heq.symm ▸ hp⟩
      · intro q hq
        change (t.eval (values q)).val ⊆ U q
        rw [he q]
        exact boundary_bounded g q (Finset.mem_of_mem_erase hq)
      · intro d hd
        change t.eval (values d.1) = WinnerSet.singleton d.2
        rw [he d.1]
        rcases Finset.mem_insert.mp hd with rfl | hd
        · exact hr
        · exact ha d hd
  · rintro (⟨j, hb, ha, hp⟩ | ⟨i, hi, r, hrU, t, ht, hb, ha, hp⟩)
    · exact ⟨⟨fun i => values i j, hb, Or.inl ⟨j, fun _ => rfl⟩⟩, ha, hp⟩
    · have hatom : t.eval (values i) = WinnerSet.singleton r := ha (i,r) (Finset.mem_insert_self _ _)
      have hbound : Bounded N U (fun q => t.eval (values q)) := by
        intro q hq
        change (t.eval (values q)).val ⊆ U q
        by_cases hqi : q = i
        · subst q
          rw [hatom]
          exact Set.singleton_subset_iff.mpr hrU
        · exact hb q (Finset.mem_erase.mpr ⟨hqi, hq⟩)
      let g : BoundaryGenerator values N U :=
        ⟨fun q => t.eval (values q), hbound,
          Or.inr ⟨⟨t, ht, fun _ => rfl⟩, i, hi, r, hatom⟩⟩
      exact ⟨g, fun d hd => ha d (Finset.mem_insert_of_mem hd), hp⟩

/-- The hereditary test is exact. Its only recursive calls delete a constrained
row; there are no auxiliary invariant clauses or generated relations. -/
theorem peels_iff [Fintype Role] [Fintype Row] (three : Fin 3 ↪ Role)
    (values : Row → Var → WinnerSet Role) (U : Row → Set Role)
    (N : Finset Row) (D : Finset (Row × Role)) (p : Option (Row × Role)) :
    Peels values U N D p ↔
      ∃ t : Term Role Var, t.IsCore ∧ Fits N U D p (fun i => t.eval (values i)) := by
  classical
  induction N using Finset.strongInductionOn generalizing D p with
  | _ N ih =>
    let B := BoundaryGenerator values N U
    let : Fintype B := Fintype.ofFinite B
    have hstep :
        (fun E o => (∃ j, Fits N U E o (fun i => values i j)) ∨
          ∃ i, ∃ _hi : i ∈ N, ∃ r ∈ U i,
            Peels values U (N.erase i) (insert (i,r) E) o) =
        (fun E o => ∃ g : B, Atomic E g.val ∧ Positive o g.val) := by
      funext E o
      apply propext
      rw [boundary_query_iff]
      refine or_congr Iff.rfl ?_
      constructor
      · rintro ⟨i, hi, r, hr, h⟩
        exact ⟨i, hi, r, hr, (ih (N.erase i) (Finset.erase_ssubset hi) _ _).mp h⟩
      · rintro ⟨i, hi, r, hr, h⟩
        exact ⟨i, hi, r, hr, (ih (N.erase i) (Finset.erase_ssubset hi) _ _).mpr h⟩
    rw [Peels.eq_1, hstep]
    exact ((boundary_fits_iff values N U D p).trans
      (atomic_positive_iff three (fun i (g : B) => g.val i) D p)).symm

/-- Full raw value tables have the same direct test, including nullary inputs,
empty row sets and empty requested values. -/
theorem recognizes_iff [Fintype Role] [Fintype Row] (three : Fin 3 ↪ Role)
    (values : Row → Var → WinnerSet Role) (U : Row → Set Role) :
    Recognizes values U ↔
      ∃ t : Term Role Var, t.IsCore ∧ ∀ i, (t.eval (values i)).val = U i := by
  classical
  rw [exact_iff_memberships three values U]
  simp only [Recognizes, peels_iff three, Fits, Atomic, Positive]
  simp

/-- At every finite arity, the hereditary condition characterizes the full
core operation directly from its value table. -/
theorem operation_iff [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (f : (Var → WinnerSet Role) → WinnerSet Role) :
    (∃ t : Term Role Var, t.IsCore ∧ ∀ v, t.eval v = f v) ↔ RecognizesOperation f := by
  classical
  let : Fintype (WinnerSet Role) := Fintype.ofFinite (WinnerSet Role)
  unfold RecognizesOperation
  rw [recognizes_iff three]
  constructor
  · rintro ⟨t, ht, he⟩
    exact ⟨t, ht, fun v => congrArg Subtype.val (he v)⟩
  · rintro ⟨t, ht, he⟩
    exact ⟨t, ht, fun v => Subtype.ext (he v)⟩

end KFOL.Core.Interpolation
