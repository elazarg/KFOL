module

public import KFOL.Core.StatusModel
public import KFOL.Algebra.TestDomains
public import KFOL.Definitions.Core

/-! # Restricting core terms to a subset of roles

On valuations supported by an embedded role type, every outside owner's
choice is union. Three owners in the smaller type suffice to express that
union and simulate the original term without changing its variables.
-/

@[expose] public section

namespace KFOL.WinnerSet.StatusModel

universe u v
variable {Small : Type u} {Large : Type v}

@[simp] theorem mem_expand_embedding (e : Small ↪ Large) (A : WinnerSet Small)
    (r : Small) :
    e r ∈ (expand (fun x => singleton (e x)) A).val ↔ r ∈ A.val := by
  change (∃ x ∈ A.val, e r ∈ (singleton (e x)).val) ↔ r ∈ A.val
  simp only [val_singleton, Set.mem_singleton_iff, e.injective.eq_iff]
  constructor
  · rintro ⟨x, hx, he⟩
    simpa [he] using hx
  · intro hr
    exact ⟨r, hr, rfl⟩

private theorem expand_embedding_ne_singleton (e : Small ↪ Large)
    (A : WinnerSet Small) (r : Large) (hr : ¬∃ x, e x = r) :
    expand (fun x => singleton (e x)) A ≠ singleton r := by
  intro he
  obtain ⟨x, hx⟩ := A.property
  have hm : e x ∈ (expand (fun x => singleton (e x)) A).val :=
    (mem_expand_embedding e A x).mpr hx
  have hxr : e x = r := by simpa [he] using hm
  exact hr ⟨x, hxr⟩

private theorem expand_embedding_choice_outside (e : Small ↪ Large)
    (A B : WinnerSet Small) (r : Large) (hr : ¬∃ x, e x = r) :
    choice r (expand (fun x => singleton (e x)) A)
      (expand (fun x => singleton (e x)) B) =
      expand (fun x => singleton (e x)) (A.union B) := by
  rw [choice, ite_eq_right (not_or.mpr ⟨expand_embedding_ne_singleton e A r hr,
    expand_embedding_ne_singleton e B r hr⟩), expand_union]

end KFOL.WinnerSet.StatusModel

namespace KFOL.Core

universe u v w
variable {Small : Type u} {Large : Type v} {Var : Type w}

/-- Every core term restricts to a core term on any embedded role type with
three owners. Owners outside the image act as derived union. -/
theorem exists_role_restriction (e : Small ↪ Large) (three : Fin 3 ↪ Small)
    (t : Term Large Var) (ht : t.IsCore) :
    ∃ s : Term Small Var, s.IsCore ∧ ∀ v : Var → WinnerSet Small,
      t.eval (fun j => WinnerSet.StatusModel.expand
        (fun x => WinnerSet.singleton (e x)) (v j)) =
      WinnerSet.StatusModel.expand (fun x => WinnerSet.singleton (e x)) (s.eval v) := by
  classical
  induction t with
  | winner => exact ht.elim
  | rename => exact ht.elim
  | var x => exact ⟨.var x, trivial, fun _ => rfl⟩
  | choice r t u iht ihu =>
    obtain ⟨s, hs, hse⟩ := iht ht.1
    obtain ⟨z, hz, hze⟩ := ihu ht.2
    by_cases hr : ∃ x, e x = r
    · obtain ⟨x, rfl⟩ := hr
      refine ⟨.choice x s z, ⟨hs, hz⟩, ?_⟩
      intro v
      simp only [Term.eval, hse, hze]
      symm
      apply WinnerSet.StatusModel.expand_choice
      intro y
      simp only [WinnerSet.singleton_inj, e.injective.eq_iff]
    · refine ⟨Term.unionTerm three s z, ?_, ?_⟩
      · simp [Term.unionTerm, Term.IsCore, hs, hz]
      · intro v
        simp only [Term.eval, hse, hze, Term.eval_unionTerm]
        exact WinnerSet.StatusModel.expand_embedding_choice_outside e _ _ r hr

end KFOL.Core
