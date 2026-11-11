module

public import KFOL.Definitions.CoreInterpolation
public import KFOL.Algebra.TestDomains
public import Mathlib.Data.Fintype.Prod

/-! # Joining bounded interpolation witnesses

One bounded core witness per requested membership suffices to realize a finite
raw value table. An initial bounded witness also covers the empty row type.
-/

@[expose] public section
namespace KFOL.Core.Interpolation

universe u v w
variable {Role : Type u} {Row : Type v} {Var : Type w}

/-- Finitely many requested memberships can be joined without violating any
of the fixed upper bounds. -/
theorem join_memberships (three : Fin 3 ↪ Role) (values : Row → Var → WinnerSet Role)
    (N : Finset Row) (U : Row → Set Role) (S : Finset (Row × Role))
    (hbase : ∃ t : Term Role Var, t.IsCore ∧ Bounded N U (fun i => t.eval (values i)))
    (hw : ∀ p ∈ S, ∃ t : Term Role Var, t.IsCore ∧
      Bounded N U (fun i => t.eval (values i)) ∧ p.2 ∈ (t.eval (values p.1)).val) :
    ∃ t : Term Role Var, t.IsCore ∧ Bounded N U (fun i => t.eval (values i)) ∧
      ∀ p ∈ S, p.2 ∈ (t.eval (values p.1)).val := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    obtain ⟨t, ht, hb⟩ := hbase
    exact ⟨t, ht, hb, by simp⟩
  | @insert p S hp ih =>
    obtain ⟨s, hsc, hsb, hsm⟩ := ih (fun q hq => hw q (Finset.mem_insert_of_mem hq))
    obtain ⟨t, htc, htb, htm⟩ := hw p (Finset.mem_insert_self _ _)
    refine ⟨Term.unionTerm three s t, ⟨⟨hsc, htc⟩, ⟨hsc, htc⟩⟩, ?_, ?_⟩
    · intro i hi
      change ((Term.unionTerm three s t).eval (values i)).val ⊆ U i
      rw [Term.eval_unionTerm]
      exact Set.union_subset (hsb i hi) (htb i hi)
    · intro q hq
      rw [Term.eval_unionTerm]
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact Or.inr htm
      · exact Or.inl (hsm q hq)

/-- Exact finite interpolation reduces to bounded nonemptiness and separate
positive memberships, because finite union is a core operation. -/
theorem exact_iff_memberships [Fintype Role] [Fintype Row]
    (three : Fin 3 ↪ Role) (values : Row → Var → WinnerSet Role)
    (U : Row → Set Role) :
    (∃ t : Term Role Var, t.IsCore ∧ ∀ i, (t.eval (values i)).val = U i) ↔
      (∃ t : Term Role Var, t.IsCore ∧
        Bounded Finset.univ U (fun i => t.eval (values i))) ∧
      ∀ i k, k ∈ U i → ∃ t : Term Role Var, t.IsCore ∧
        Bounded Finset.univ U (fun i => t.eval (values i)) ∧ k ∈ (t.eval (values i)).val := by
  classical
  constructor
  · rintro ⟨t, ht, he⟩
    have hb : Bounded Finset.univ U (fun i => t.eval (values i)) :=
      fun i _ => (he i).subset
    exact ⟨⟨t, ht, hb⟩, fun i k hk => ⟨t, ht, hb, (he i).symm ▸ hk⟩⟩
  · rintro ⟨hbase, hw⟩
    let S : Finset (Row × Role) := Finset.univ.filter (fun p => p.2 ∈ U p.1)
    obtain ⟨t, ht, hb, hm⟩ := join_memberships three values Finset.univ U S hbase
      (fun p h => hw p.1 p.2 (Finset.mem_filter.mp h).2)
    refine ⟨t, ht, fun i => Set.Subset.antisymm (hb i (Finset.mem_univ _)) ?_⟩
    intro k hk
    exact hm (i,k) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)

end KFOL.Core.Interpolation
