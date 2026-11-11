module

public import KFOL.Definitions.CoreFunctions
public import KFOL.Algebra.Basic
public import KFOL.Algebra.TestDomains
public import KFOL.Core.Interpolation
public import Mathlib.Tactic.Tauto

/-! # Pairwise interpolation and binary relational tests

Three short core operations have at most two distinct values at any valuation.
Their repeated-value patch has a common interpolant at every pair of points,
yet violates three-valuation persistence.
-/

@[expose] public section

namespace KFOL.Core

universe u v
variable {Role : Type u} {Var : Type v}

private theorem eval_mem_binary (t : Term Role Var) (ht : t.IsCore)
    (R : Set (WinnerSet Role × WinnerSet Role)) (hR : BinaryInvariant R)
    (v w : Var → WinnerSet Role) (h : ∀ i, (v i, w i) ∈ R) :
    (t.eval v, t.eval w) ∈ R := by
  induction t with
  | winner => exact ht.elim
  | rename => exact ht.elim
  | var i => exact h i
  | choice r s t ihs iht => exact hR r _ _ (ihs ht.1) (iht ht.2)

/-- Binary relational preservation is exactly simultaneous interpolation at two points. -/
theorem pairwiseInterpolable_iff_preservesBinary
    (f : (Var → WinnerSet Role) → WinnerSet Role) :
    PairwiseInterpolable f ↔ PreservesBinary f := by
  constructor
  · intro hf R hR v w h
    obtain ⟨t, ht, hv, hw⟩ := hf v w
    simpa only [hv, hw] using eval_mem_binary t ht R hR v w h
  · intro hf v w
    let R : Set (WinnerSet Role × WinnerSet Role) :=
      {p | ∃ t : Term Role Var, t.IsCore ∧ t.eval v = p.1 ∧ t.eval w = p.2}
    exact hf R (by
      rintro r x y ⟨s, hs, hsv, hsw⟩ ⟨t, ht, htv, htw⟩
      exact ⟨.choice r s t, ⟨hs, ht⟩, by simp [Term.eval, hsv, htv],
        by simp [Term.eval, hsw, htw]⟩) v w (fun i => ⟨.var i, trivial, rfl, rfl⟩)

/-- Two-point interpolation transfers ordinary inclusion monotonicity. -/
theorem PairwiseInterpolable.monotone {f : (Var → WinnerSet Role) → WinnerSet Role}
    (hf : PairwiseInterpolable f) (v w : Var → WinnerSet Role)
    (h : ∀ i, (v i).val ⊆ (w i).val) : (f v).val ⊆ (f w).val := by
  obtain ⟨t, _, hv, hw⟩ := hf v w
  rw [← hv, ← hw]
  exact t.eval_mono h

/-- Two-point interpolation transfers idempotence on all diagonal inputs. -/
theorem PairwiseInterpolable.diagonal {f : (Var → WinnerSet Role) → WinnerSet Role}
    (hf : PairwiseInterpolable f) (A : WinnerSet Role) : f (fun _ => A) = A := by
  obtain ⟨t, ht, hv, _⟩ := hf (fun _ => A) (fun _ => A)
  exact hv.symm.trans (ht.eval_diagonal A)

namespace Pairwise

open WinnerSet

private theorem union_assoc (A B C : WinnerSet Role) : (A.union B).union C = A.union (B.union C) :=
  Subtype.ext (Set.union_assoc _ _ _)

private theorem union_left_comm (A B C : WinnerSet Role) :
    A.union (B.union C) = B.union (A.union C) :=
  Subtype.ext (Set.union_left_comm _ _ _)

private theorem union_self (A : WinnerSet Role) : A.union A = A :=
  Subtype.ext (Set.union_self _)

private theorem union_left_idem (A B : WinnerSet Role) : A.union (A.union B) = A.union B :=
  by
  apply Subtype.ext
  change A.val ∪ (A.val ∪ B.val) = A.val ∪ B.val
  rw [← Set.union_assoc, Set.union_self]

private theorem choice_of_ne (r : Role) {A B : WinnerSet Role}
    (ha : A ≠ WinnerSet.singleton r) (hb : B ≠ WinnerSet.singleton r) : choice r A B = A.union B := by
  simp [choice, ha, hb]

set_option linter.unusedSimpArgs false in
/-- The three candidates have a repeated value, uniformly in the role type. -/
theorem candidates_coherent (three : Fin 3 ↪ Role) (v : Fin 3 → WinnerSet Role) :
    patchCandidates three v 0 = patchCandidates three v 1 ∨
    patchCandidates three v 0 = patchCandidates three v 2 ∨
    patchCandidates three v 1 = patchCandidates three v 2 := by
  classical
  let a := three 0
  let b := three 1
  let c := three 2
  have hab : a ≠ b := three.injective.ne (by decide)
  have hac : a ≠ c := three.injective.ne (by decide)
  have hbc : b ≠ c := three.injective.ne (by decide)
  have hba := hab.symm
  have hca := hac.symm
  have hcb := hbc.symm
  let X := v 0
  let Y := v 1
  let Z := v 2
  change Y.union (choice b X Z) = choice a (choice b X Z) (choice c Y Z) ∨
    Y.union (choice b X Z) = choice c (choice a X Y) (choice b X Z) ∨
    choice a (choice b X Z) (choice c Y Z) = choice c (choice a X Y) (choice b X Z)
  by_cases hx : X = WinnerSet.singleton b
  · right; left
    by_cases hy : Y = WinnerSet.singleton a <;>
      simp_all [choice, union_eq_singleton_iff, singleton_inj, union_comm,
        union_assoc, union_left_comm, union_self, union_left_idem]
  · by_cases hz : Z = WinnerSet.singleton b
    · left
      by_cases hy : Y = WinnerSet.singleton c <;>
        simp_all [choice, union_eq_singleton_iff, singleton_inj, union_comm,
          union_assoc, union_left_comm, union_self, union_left_idem]
    · rw [choice_of_ne b hx hz]
      by_cases hxa : X = WinnerSet.singleton a <;> by_cases hxc : X = WinnerSet.singleton c <;>
        by_cases hya : Y = WinnerSet.singleton a <;> by_cases hza : Z = WinnerSet.singleton a <;>
        by_cases hyc : Y = WinnerSet.singleton c <;> by_cases hzc : Z = WinnerSet.singleton c <;>
        simp_all [choice, union_eq_singleton_iff, singleton_inj, union_comm,
          union_assoc, union_left_comm, union_self, union_left_idem]

private theorem common_candidate {D A : Type*} [DecidableEq A] (f : D → Fin 3 → A)
    (coherent : ∀ x, f x 0 = f x 1 ∨ f x 0 = f x 2 ∨ f x 1 = f x 2)
    (x y : D) : ∃ i : Fin 3,
      f x i = (if f x 0 = f x 1 then f x 0 else f x 2) ∧
      f y i = (if f y 0 = f y 1 then f y 0 else f y 2) := by
  classical
  by_cases hx : f x 0 = f x 1 <;> by_cases hy : f y 0 = f y 1
  · exact ⟨0, by rw [ite_eq_left hx], by rw [ite_eq_left hy]⟩
  · rcases coherent y with h | h | h
    · exact (hy h).elim
    · exact ⟨0, by rw [ite_eq_left hx], by rw [ite_eq_right hy]; exact h⟩
    · exact ⟨1, by rw [ite_eq_left hx]; exact hx.symm,
        by rw [ite_eq_right hy]; exact h⟩
  · rcases coherent x with h | h | h
    · exact (hx h).elim
    · exact ⟨0, by rw [ite_eq_right hx]; exact h, by rw [ite_eq_left hy]⟩
    · exact ⟨1, by rw [ite_eq_right hx]; exact h,
        by rw [ite_eq_left hy]; exact hy.symm⟩
  · exact ⟨2, by rw [ite_eq_right hx], by rw [ite_eq_right hy]⟩

private def candidateTerm (three : Fin 3 ↪ Role) : Fin 3 → Term Role (Fin 3) :=
  let h := Term.choice (three 1) (.var 0) (.var 2)
  ![Term.unionTerm three (.var 1) h,
    .choice (three 0) h (.choice (three 2) (.var 1) (.var 2)),
    .choice (three 2) (.choice (three 0) (.var 0) (.var 1)) h]

private theorem candidate_core (three : Fin 3 ↪ Role) (i : Fin 3) :
    (candidateTerm three i).IsCore := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> trivial

private theorem candidate_eval (three : Fin 3 ↪ Role) (i : Fin 3)
    (v : Fin 3 → WinnerSet Role) :
    (candidateTerm three i).eval v = patchCandidates three v i := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;>
    simp [candidateTerm, patchCandidates, Term.eval]

/-- The repeated-value patch has a common term witness at every pair of points. -/
theorem counterexample_pairwise (three : Fin 3 ↪ Role) :
    PairwiseInterpolable (pairwiseCounterexample three) := by
  classical
  intro v w
  obtain ⟨i, hi, hj⟩ := common_candidate (patchCandidates three) (candidates_coherent three) v w
  exact ⟨candidateTerm three i, candidate_core three i,
    (candidate_eval three i v).trans hi, (candidate_eval three i w).trans hj⟩

private theorem first_value (three : Fin 3 ↪ Role) :
    pairwiseCounterexample three ![(WinnerSet.singleton (three 0)).union (WinnerSet.singleton (three 1)),
      WinnerSet.singleton (three 1), WinnerSet.singleton (three 1)] =
      WinnerSet.singleton (three 1) := by
  classical
  have hab := three.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hac := three.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hbc := three.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  simp [pairwiseCounterexample, patchCandidates, choice, singleton_inj,
    union_eq_singleton_iff, hab, hac, hbc, Ne.symm hab]

private theorem second_value (three : Fin 3 ↪ Role) :
    pairwiseCounterexample three ![WinnerSet.singleton (three 1),
      (WinnerSet.singleton (three 1)).union (WinnerSet.singleton (three 2)),
      (WinnerSet.singleton (three 0)).union (WinnerSet.singleton (three 1))] =
      (WinnerSet.singleton (three 1)).union (WinnerSet.singleton (three 2)) := by
  classical
  have hab := three.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hac := three.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hbc := three.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  simp [pairwiseCounterexample, patchCandidates, choice, singleton_inj,
    union_eq_singleton_iff, hab, hac, hbc, Ne.symm hab, Ne.symm hac,
    union_comm, union_left_comm, union_left_idem]

private theorem third_value (three : Fin 3 ↪ Role) :
    pairwiseCounterexample three ![WinnerSet.singleton (three 0),
      WinnerSet.singleton (three 1), WinnerSet.singleton (three 2)] =
      (WinnerSet.singleton (three 0)).union (WinnerSet.singleton (three 2)) := by
  classical
  have hab := three.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hac := three.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hbc := three.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  simp [pairwiseCounterexample, patchCandidates, choice, singleton_inj,
    union_eq_singleton_iff, hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc,
    union_comm, union_left_comm, union_left_idem]

private theorem repeated_predicate {A : Type*} [DecidableEq A]
    (S : A → Prop) (p q r : A) (h : p = q ∨ p = r ∨ q = r) :
    S (if p = q then p else r) ↔ (S p ∧ S q) ∨ (S p ∧ S r) ∨ (S q ∧ S r) := by
  by_cases hpq : p = q
  · rw [ite_eq_left hpq, hpq]
    tauto
  · rw [ite_eq_right hpq]
    rcases h with h | h | h
    · exact (hpq h).elim
    · rw [h]; tauto
    · rw [h]; tauto

private theorem choice_atom (owner r : Role) (A B : WinnerSet Role) :
    choice owner A B = WinnerSet.singleton r ↔
      (owner = r ∧ (A = WinnerSet.singleton r ∨ B = WinnerSet.singleton r)) ∨
      (owner ≠ r ∧ A = WinnerSet.singleton r ∧ B = WinnerSet.singleton r) := by
  by_cases h : owner = r
  · subst owner; simp [choice_eq_owner_iff]
  · simp [h, choice_eq_other_iff A B owner h]

/-- The patch has exactly the singleton profiles of a concrete core term. -/
theorem counterexample_profiles (three : Fin 3 ↪ Role) :
    ∃ s : Term Role (Fin 3), s.IsCore ∧ ∀ v r,
      (pairwiseCounterexample three v = WinnerSet.singleton r ↔ s.eval v = WinnerSet.singleton r) := by
  classical
  refine ⟨.choice (three 1) (candidateTerm three 1) (candidateTerm three 2),
    ⟨candidate_core three 1, candidate_core three 2⟩, ?_⟩
  intro v r
  simp only [Term.eval, candidate_eval]
  change (if patchCandidates three v 0 = patchCandidates three v 1 then
    patchCandidates three v 0 else patchCandidates three v 2) = WinnerSet.singleton r ↔ _
  rw [repeated_predicate (fun A => A = WinnerSet.singleton r) _ _ _ (candidates_coherent three v)]
  dsimp [patchCandidates]
  have hab := three.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hac := three.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hbc := three.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  by_cases ha : three 0 = r <;> by_cases hb : three 1 = r <;> by_cases hc : three 2 = r <;>
    simp_all [choice_atom, union_eq_singleton_iff] <;> tauto

/-- Three-valuation persistence excludes a single global realizing term. -/
theorem counterexample_not_term (three : Fin 3 ↪ Role) :
    ¬∃ t : Term Role (Fin 3), t.IsCore ∧ ∀ v, t.eval v = pairwiseCounterexample three v := by
  rintro ⟨t, ht, he⟩
  have hm := three_valuation_persistence (three 0) (three 1) (three 2)
    (three.injective.ne (by decide)) (three.injective.ne (by decide)) (three.injective.ne (by decide))
    id t ht (by simpa only [id_eq, he] using first_value three)
      (by simpa only [id_eq, he] using second_value three)
  change three 1 ∈ (t.eval ![WinnerSet.singleton (three 0),
    WinnerSet.singleton (three 1), WinnerSet.singleton (three 2)]).val at hm
  rw [he, third_value] at hm
  exact hm.elim (three.injective.ne (by decide)) (three.injective.ne (by decide))

end Pairwise
end KFOL.Core
