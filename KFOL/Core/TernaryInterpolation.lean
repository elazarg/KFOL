module

public import KFOL.Core.FourValuation
public import KFOL.Algebra.TestDomains
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Tauto

/-! # Three-point interpolation does not characterize core operations

Four short core terms agree three at a time at every valuation. Their common
value has all three-point interpolants but violates four-valuation persistence.
-/

@[expose] public section

namespace KFOL.Core.Threewise
open WinnerSet
variable {Role : Type*}
private theorem union_assoc (A B C : WinnerSet Role) : (A.union B).union C = A.union (B.union C) :=
  Subtype.ext (Set.union_assoc _ _ _)
private theorem union_left_comm (A B C : WinnerSet Role) :
    A.union (B.union C) = B.union (A.union C) :=
  Subtype.ext (Set.union_left_comm _ _ _)
private theorem union_self (A : WinnerSet Role) : A.union A = A :=
  Subtype.ext (Set.union_self _)
private theorem union_left_idem (A B : WinnerSet Role) : A.union (A.union B) = A.union B := by
  apply Subtype.ext
  change A.val ∪ (A.val ∪ B.val) = A.val ∪ B.val
  rw [← Set.union_assoc, Set.union_self]

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
theorem candidates_coherent {Role : Type*} (three : Fin 3 ↪ Role) (v : Fin 3 → WinnerSet Role) :
    (fourPatchCandidates three v 0 = fourPatchCandidates three v 1 ∧ fourPatchCandidates three v 0 = fourPatchCandidates three v 2) ∨
    (fourPatchCandidates three v 0 = fourPatchCandidates three v 1 ∧ fourPatchCandidates three v 0 = fourPatchCandidates three v 3) ∨
    (fourPatchCandidates three v 0 = fourPatchCandidates three v 2 ∧ fourPatchCandidates three v 0 = fourPatchCandidates three v 3) ∨
    (fourPatchCandidates three v 1 = fourPatchCandidates three v 2 ∧ fourPatchCandidates three v 1 = fourPatchCandidates three v 3) := by
  classical
  have hab := three.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hac := three.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hbc := three.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  have hba := hab.symm
  have hca := hac.symm
  have hcb := hbc.symm
  dsimp [fourPatchCandidates]
  by_cases hxa : v 0 = singleton (three 0) <;>
    by_cases hxb : v 0 = singleton (three 1) <;>
    by_cases hxc : v 0 = singleton (three 2) <;>
    by_cases hya : v 1 = singleton (three 0) <;>
    by_cases hyb : v 1 = singleton (three 1) <;>
    by_cases hyc : v 1 = singleton (three 2) <;>
    by_cases hza : v 2 = singleton (three 0) <;>
    by_cases hzb : v 2 = singleton (three 1) <;>
    by_cases hzc : v 2 = singleton (three 2) <;>
    simp_all [choice, union_eq_singleton_iff, singleton_inj, union_comm,
      union_assoc, union_left_comm, union_self, union_left_idem]

private def candidateTerm {Role : Type*} (three : Fin 3 ↪ Role) : Fin 4 → Term Role (Fin 3) :=
  let X := Term.var 0
  let Y := Term.var 1
  let Z := Term.var 2
  let H := Term.choice (three 1) X Y
  let T := Term.choice (three 0) Y Z
  ![.choice (three 2) H (.choice (three 0) H T),
    Term.unionTerm three Z (.choice (three 0) H (.choice (three 2) X Z)),
    Term.unionTerm three X (.choice (three 2) H T),
    .choice (three 2) H (.choice (three 0) Y (.choice (three 2) Z (.choice (three 0) X Y)))]

private theorem candidate_core {Role : Type*} (three : Fin 3 ↪ Role) (i : Fin 4) :
    (candidateTerm three i).IsCore := by
  fin_cases i <;> trivial

private theorem candidate_eval {Role : Type*} (three : Fin 3 ↪ Role) (i : Fin 4)
    (v : Fin 3 → WinnerSet Role) :
    (candidateTerm three i).eval v = fourPatchCandidates three v i := by
  fin_cases i <;> simp [candidateTerm, fourPatchCandidates, Term.eval]

private theorem common_value {A : Type*} [DecidableEq A] (p : Fin 4 → A)
    (h : (p 0 = p 1 ∧ p 0 = p 2) ∨ (p 0 = p 1 ∧ p 0 = p 3) ∨
      (p 0 = p 2 ∧ p 0 = p 3) ∨ (p 1 = p 2 ∧ p 1 = p 3)) :
    ∃ bad : Fin 4, ∀ i, i ≠ bad → p i = (if p 0 = p 1 then p 0 else p 2) := by
  rcases h with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩
  · refine ⟨3, ?_⟩
    intro i hi
    fin_cases i <;> simp_all
  · refine ⟨2, ?_⟩
    intro i hi
    fin_cases i <;> simp_all
  · refine ⟨1, ?_⟩
    intro i hi
    fin_cases i <;> split_ifs <;> simp_all
  · refine ⟨0, ?_⟩
    intro i hi
    fin_cases i <;> split_ifs <;> simp_all

/-- The common value has a core interpolant on every three evaluations. -/
theorem counterexample_interpolable {Role : Type*} (three : Fin 3 ↪ Role) :
    LocallyInterpolable 3 (threewiseCounterexample three) := by
  classical
  apply locallyInterpolable_of_patches 3 (candidateTerm three) (candidate_core three)
  intro v
  obtain ⟨bad, hb⟩ := common_value (fourPatchCandidates three v) (candidates_coherent three v)
  exact ⟨bad, fun i hi => (candidate_eval three i v).trans (hb i hi)⟩

/-- In particular, every ternary invariant relation is preserved. -/
theorem counterexample_preserves {Role : Type*} (three : Fin 3 ↪ Role) :
    PreservesInvariants 3 (threewiseCounterexample three) :=
  (locallyInterpolable_iff_preservesInvariants _ _).mp (counterexample_interpolable three)

private theorem values {Role : Type*} (three : Fin 3 ↪ Role) :
    threewiseCounterexample three
      ![(singleton (three 0)).union (singleton (three 2)), singleton (three 1), singleton (three 0)] =
      (singleton (three 0)).union ((singleton (three 1)).union (singleton (three 2))) ∧
    threewiseCounterexample three
      ![(singleton (three 0)).union (singleton (three 1)), singleton (three 0),
        (singleton (three 1)).union (singleton (three 2))] =
      (singleton (three 0)).union (singleton (three 1)) ∧
    threewiseCounterexample three ![singleton (three 0), singleton (three 1), singleton (three 2)] =
      (singleton (three 1)).union (singleton (three 2)) ∧
    threewiseCounterexample three ![singleton (three 1), singleton (three 2), singleton (three 0)] =
      (singleton (three 0)).union (singleton (three 1)) := by
  classical
  have hab := three.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hac := three.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hbc := three.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  simp [threewiseCounterexample, fourPatchCandidates, choice, singleton_inj,
    union_eq_singleton_iff, hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc,
    union_comm, union_left_comm, union_left_idem]

/-- Four-valuation persistence rules out a global realizing term. -/
theorem counterexample_not_term {Role : Type*} (three : Fin 3 ↪ Role) :
    ¬∃ t : Term Role (Fin 3), t.IsCore ∧ ∀ v, t.eval v = threewiseCounterexample three v := by
  classical
  rintro ⟨t, ht, he⟩
  have hab := three.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hac := three.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hbc := three.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  obtain ⟨hA, hB, hC, hD⟩ := values three
  have h := four_valuation_persistence three id t ht
    (by simpa only [id_eq, he, hB, val_union, val_singleton, Set.mem_union,
      Set.mem_singleton_iff, not_or] using And.intro hac.symm hbc.symm)
    (by simpa only [id_eq, he, hC, val_union, val_singleton, Set.mem_union,
      Set.mem_singleton_iff, not_or] using And.intro hab hac)
    (by simpa only [id_eq, he, hD, val_union, val_singleton, Set.mem_union,
      Set.mem_singleton_iff, not_or] using And.intro hac.symm hbc.symm)
  apply h
  simpa only [id_eq, he, hA, val_union, val_singleton, Set.mem_union,
    Set.mem_singleton_iff] using (Or.inr (Or.inr rfl) :
      three 2 = three 0 ∨ three 2 = three 1 ∨ three 2 = three 2)

private theorem choice_atom {Role : Type*} (owner r : Role) (A B : WinnerSet Role) :
    choice owner A B = singleton r ↔
      (owner = r ∧ (A = singleton r ∨ B = singleton r)) ∨
      (owner ≠ r ∧ A = singleton r ∧ B = singleton r) := by
  by_cases h : owner = r
  · subst owner; simp [choice_eq_owner_iff]
  · simp [h, choice_eq_other_iff A B owner h]

private theorem repeated_predicate {A : Type*} [DecidableEq A] (S : A → Prop)
    (p : Fin 4 → A) (h : (p 0 = p 1 ∧ p 0 = p 2) ∨ (p 0 = p 1 ∧ p 0 = p 3) ∨
      (p 0 = p 2 ∧ p 0 = p 3) ∨ (p 1 = p 2 ∧ p 1 = p 3)) :
    S (if p 0 = p 1 then p 0 else p 2) ↔
      (S (p 0) ∧ S (p 1)) ∨ (S (p 0) ∧ S (p 2)) ∨ (S (p 1) ∧ S (p 2)) := by
  by_cases h01 : p 0 = p 1
  · rw [ite_eq_left h01, h01]; tauto
  · rw [ite_eq_right h01]
    rcases h with h | h | h | h
    · exact (h01 h.1).elim
    · exact (h01 h.1).elim
    · rw [h.1]; tauto
    · rw [h.1]; tauto

/-- Its singleton profiles are those of a short, explicitly given core operation. -/
theorem counterexample_profiles {Role : Type*} (three : Fin 3 ↪ Role) :
    ∃ s : Term Role (Fin 3), s.IsCore ∧ ∀ v r,
      (threewiseCounterexample three v = singleton r ↔ s.eval v = singleton r) := by
  classical
  let U : Term Role (Fin 3) := Term.unionTerm three (.var 0) (.var 1)
  refine ⟨.choice (three 2) (.choice (three 0) U (.var 2)) U, by trivial, ?_⟩
  intro v r
  unfold threewiseCounterexample
  rw [repeated_predicate (fun A => A = singleton r) _ (candidates_coherent three v)]
  have hab := three.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hac := three.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hbc := three.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  dsimp [fourPatchCandidates]
  simp only [Term.eval, Term.eval_unionTerm, U]
  by_cases ha : three 0 = r <;> by_cases hb : three 1 = r <;> by_cases hc : three 2 = r <;>
    simp_all [choice_atom, union_eq_singleton_iff] <;> tauto

private def lowerTerm {Role : Type*} (three : Fin 3 ↪ Role) : Term Role (Fin 3) :=
  let X := Term.var 0
  let Y := Term.var 1
  let Z := Term.var 2
  let H := Term.choice (three 1) X Y
  let T := Term.choice (three 0) Y Z
  let J := Term.choice (three 2) X Z
  .choice (three 2) H (.choice (three 0) H (.choice (three 0) T J))

private theorem lower_profiles {Role : Type*} (three : Fin 3 ↪ Role)
    (v : Fin 3 → WinnerSet Role) (r : Role) :
    threewiseCounterexample three v = singleton r ↔ (lowerTerm three).eval v = singleton r := by
  classical
  unfold threewiseCounterexample
  rw [repeated_predicate (fun A => A = singleton r) _ (candidates_coherent three v)]
  have hab := three.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hac := three.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hbc := three.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  dsimp [fourPatchCandidates, lowerTerm]
  simp only [Term.eval]
  by_cases ha : three 0 = r <;> by_cases hb : three 1 = r <;> by_cases hc : three 2 = r <;>
    simp_all [choice_atom, union_eq_singleton_iff] <;> tauto

set_option maxHeartbeats 3000000 in
set_option linter.unusedSimpArgs false in
private theorem lower_subset {Role : Type*} (three : Fin 3 ↪ Role)
    (v : Fin 3 → WinnerSet Role) : (lowerTerm three).eval v ≤ threewiseCounterexample three v := by
  classical
  intro r hr
  change r ∈ (if fourPatchCandidates three v 0 = fourPatchCandidates three v 1 then
    fourPatchCandidates three v 0 else fourPatchCandidates three v 2).val
  rw [repeated_predicate (fun A => r ∈ A.val) _ (candidates_coherent three v)]
  have hab := three.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hac := three.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hbc := three.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  have hba := hab.symm
  have hca := hac.symm
  have hcb := hbc.symm
  dsimp [fourPatchCandidates]
  dsimp [lowerTerm] at hr
  simp only [Term.eval] at hr
  by_cases hxa : v 0 = singleton (three 0) <;>
    by_cases hxb : v 0 = singleton (three 1) <;>
    by_cases hxc : v 0 = singleton (three 2) <;>
    by_cases hya : v 1 = singleton (three 0) <;>
    by_cases hyb : v 1 = singleton (three 1) <;>
    by_cases hyc : v 1 = singleton (three 2) <;>
    by_cases hza : v 2 = singleton (three 0) <;>
    by_cases hzb : v 2 = singleton (three 1) <;>
    by_cases hzc : v 2 = singleton (three 2) <;>
    simp_all [choice, union_eq_singleton_iff, singleton_inj, union_comm,
      union_assoc, union_left_comm, union_self, union_left_idem] <;> tauto

/-- A core operation with the same profiles lies below the obstruction. -/
theorem counterexample_lower {Role : Type*} (three : Fin 3 ↪ Role) :
    ∃ s : Term Role (Fin 3), s.IsCore ∧
      (∀ v, s.eval v ≤ threewiseCounterexample three v) ∧
      ∀ v r, s.eval v = singleton r ↔ threewiseCounterexample three v = singleton r :=
  ⟨lowerTerm three, by trivial, lower_subset three,
    fun v r => (lower_profiles three v r).symm⟩

private def observerTerm {Role : Type*} (three : Fin 3 ↪ Role) : Fin 3 → Term Role (Fin 3) :=
  let X := Term.var 0
  let Y := Term.var 1
  let Z := Term.var 2
  let U := Term.unionTerm three X Y
  let H := Term.choice (three 1) X Y
  ![Term.unionTerm three (Term.unionTerm three Y H) (.choice (three 2) Z U),
    Term.unionTerm three X (.choice (three 0) Y (.choice (three 2) Z U)),
    Term.unionTerm three (Term.unionTerm three X H) (.choice (three 0) Y Z)]

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
private theorem observer_membership {Role : Type*} (three : Fin 3 ↪ Role)
    (i : Fin 3) (v : Fin 3 → WinnerSet Role) :
    three i ∈ (threewiseCounterexample three v).val ↔
      three i ∈ ((observerTerm three i).eval v).val := by
  classical
  unfold threewiseCounterexample
  rw [repeated_predicate (fun A => three i ∈ A.val) _ (candidates_coherent three v)]
  have hab := three.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hac := three.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hbc := three.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  have hba := hab.symm
  have hca := hac.symm
  have hcb := hbc.symm
  fin_cases i <;> dsimp [fourPatchCandidates, observerTerm] <;>
    simp only [Term.eval, Term.eval_unionTerm] <;>
    by_cases hxa : v 0 = singleton (three 0) <;>
    by_cases hxb : v 0 = singleton (three 1) <;>
    by_cases hxc : v 0 = singleton (three 2) <;>
    by_cases hya : v 1 = singleton (three 0) <;>
    by_cases hyb : v 1 = singleton (three 1) <;>
    by_cases hyc : v 1 = singleton (three 2) <;>
    by_cases hza : v 2 = singleton (three 0) <;>
    by_cases hzb : v 2 = singleton (three 1) <;>
    by_cases hzc : v 2 = singleton (three 2) <;>
    simp_all [choice, union_eq_singleton_iff, singleton_inj] <;> tauto

private theorem observer_other {Role : Type*} (three : Fin 3 ↪ Role)
    (i : Fin 3) (v : Fin 3 → WinnerSet Role) (r : Role) (hr : r ≠ three i) :
    threewiseCounterexample three v = singleton r ↔
      (observerTerm three i).eval v = singleton r := by
  classical
  unfold threewiseCounterexample
  rw [repeated_predicate (fun A => A = singleton r) _ (candidates_coherent three v)]
  have hab := three.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hac := three.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hbc := three.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  fin_cases i <;> dsimp [fourPatchCandidates, observerTerm] <;>
    simp only [Term.eval, Term.eval_unionTerm] <;>
    by_cases ha : three 0 = r <;> by_cases hb : three 1 = r <;>
    by_cases hc : three 2 = r <;>
    simp_all [choice_atom, union_eq_singleton_iff] <;> tauto

theorem counterexample_named_views {Role : Type*} (three : Fin 3 ↪ Role) (i : Fin 3) :
    ∃ t : Term Role (Fin 3), t.IsCore ∧ ∀ v,
      WinnerSet.view (three i) (threewiseCounterexample three v) =
        WinnerSet.view (three i) (t.eval v) := by
  refine ⟨observerTerm three i, ?_, ?_⟩
  · fin_cases i <;> trivial
  · intro v
    apply (WinnerSet.view_eq_view_iff _ _ _).mpr
    exact ⟨observer_membership three i v, fun r hr => observer_other three i v r hr⟩


/-- Three-point interpolation and separate player-view realizations do not
suffice for one common core realization. -/
theorem counterexample {Role : Type*} (three : Fin 3 ↪ Role) :
    LocallyInterpolable 3 (threewiseCounterexample three) ∧
    PreservesInvariants 3 (threewiseCounterexample three) ∧
    (∃ s : Term Role (Fin 3), s.IsCore ∧ ∀ v r,
      (threewiseCounterexample three v = singleton r ↔ s.eval v = singleton r)) ∧
    (∀ i : Fin 3, ∃ t : Term Role (Fin 3), t.IsCore ∧ ∀ v,
      WinnerSet.view (three i) (threewiseCounterexample three v) =
        WinnerSet.view (three i) (t.eval v)) ∧
    ¬∃ t : Term Role (Fin 3), t.IsCore ∧ ∀ v, t.eval v = threewiseCounterexample three v :=
  ⟨counterexample_interpolable three, counterexample_preserves three,
    counterexample_profiles three, counterexample_named_views three, counterexample_not_term three⟩

end KFOL.Core.Threewise
