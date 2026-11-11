module

public import KFOL.Core.MinorantObstruction
public import KFOL.Core.RelationalInterpolation
public import KFOL.Algebra.TestDomains
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Tauto

/-! # Three-point interpolation need not supply a core minorant

Four explicit core operations agree three at a time at every valuation. Their
common value excludes the four memberships retained by the uniform cover law,
so even a pointwise smaller core operation is impossible.
-/

@[expose] public section

namespace KFOL.Core.MinorantPatches

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

private noncomputable def candidateValue (three : Fin 3 ↪ Role)
    (v : Fin 4 → WinnerSet Role) : Fin 4 → WinnerSet Role :=
  let X := v 0
  let Y := v 1
  let Z := v 2
  let W := v 3
  let A := choice (three 0) X W
  let B := choice (three 2) Y Z
  let C := choice (three 1) X W
  let D := choice (three 2) X Y
  let E := choice (three 2) Y (X.union Z)
  let H := choice (three 0) Y (choice (three 0) Z W)
  let J := choice (three 0) W (choice (three 2) X Z)
  ![(choice (three 1) A B).union (choice (three 1) X H),
    (choice (three 0) W (choice (three 2) X (choice (three 0) Y Z))).union
      (choice (three 1) E (choice (three 0) Y C)),
    (choice (three 2) Z A).union
      (choice (three 1) Z (choice (three 0) D (Y.union W))),
    ((choice (three 0) Z W).union (choice (three 1) W (choice (three 0) X Y))).union
      (choice (three 1) E J)]

private def candidateTerm (three : Fin 3 ↪ Role) : Fin 4 → Term Role (Fin 4) :=
  let X := Term.var 0
  let Y := Term.var 1
  let Z := Term.var 2
  let W := Term.var 3
  let A := Term.choice (three 0) X W
  let B := Term.choice (three 2) Y Z
  let C := Term.choice (three 1) X W
  let D := Term.choice (three 2) X Y
  let E := Term.choice (three 2) Y (Term.unionTerm three X Z)
  let H := Term.choice (three 0) Y (Term.choice (three 0) Z W)
  let J := Term.choice (three 0) W (Term.choice (three 2) X Z)
  ![Term.unionTerm three (.choice (three 1) A B) (.choice (three 1) X H),
    Term.unionTerm three (.choice (three 0) W (.choice (three 2) X (.choice (three 0) Y Z)))
      (.choice (three 1) E (.choice (three 0) Y C)),
    Term.unionTerm three (.choice (three 2) Z A)
      (.choice (three 1) Z (.choice (three 0) D (Term.unionTerm three Y W))),
    Term.unionTerm three
      (Term.unionTerm three (.choice (three 0) Z W) (.choice (three 1) W (.choice (three 0) X Y)))
      (.choice (three 1) E J)]

private theorem candidate_core (three : Fin 3 ↪ Role) (i : Fin 4) :
    (candidateTerm three i).IsCore := by
  fin_cases i <;> trivial

private theorem candidate_eval (three : Fin 3 ↪ Role) (i : Fin 4)
    (v : Fin 4 → WinnerSet Role) :
    (candidateTerm three i).eval v = candidateValue three v i := by
  fin_cases i <;> simp [candidateTerm, candidateValue, Term.eval]

private def Coherent {A : Type*} (p : Fin 4 → A) : Prop :=
  (p 0 = p 1 ∧ p 0 = p 2) ∨ (p 0 = p 1 ∧ p 0 = p 3) ∨
    (p 0 = p 2 ∧ p 0 = p 3) ∨ (p 1 = p 2 ∧ p 1 = p 3)

set_option maxHeartbeats 12000000 in
set_option linter.unusedSimpArgs false in
private theorem candidates_coherent (three : Fin 3 ↪ Role) (v : Fin 4 → WinnerSet Role) :
    Coherent (candidateValue three v) := by
  classical
  have hab := three.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hac := three.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hbc := three.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  have hba := hab.symm
  have hca := hac.symm
  have hcb := hbc.symm
  have status (X : WinnerSet Role) :
      X = singleton (three 0) ∨ X = singleton (three 1) ∨ X = singleton (three 2) ∨
        (X ≠ singleton (three 0) ∧ X ≠ singleton (three 1) ∧ X ≠ singleton (three 2)) := by
    by_cases ha : X = singleton (three 0)
    · exact Or.inl ha
    by_cases hb : X = singleton (three 1)
    · exact Or.inr (Or.inl hb)
    by_cases hc : X = singleton (three 2)
    · exact Or.inr (Or.inr (Or.inl hc))
    exact Or.inr (Or.inr (Or.inr ⟨ha, hb, hc⟩))
  dsimp [candidateValue, Coherent]
  rcases status (v 0) with hxa | hxb | hxc | ⟨hxa, hxb, hxc⟩ <;>
    rcases status (v 1) with hya | hyb | hyc | ⟨hya, hyb, hyc⟩ <;>
    rcases status (v 2) with hza | hzb | hzc | ⟨hza, hzb, hzc⟩ <;>
    rcases status (v 3) with hwa | hwb | hwc | ⟨hwa, hwb, hwc⟩ <;>
    simp_all [choice, union_eq_singleton_iff, singleton_inj, union_comm,
      union_assoc, union_left_comm, union_self, union_left_idem]

private noncomputable def counterexample (three : Fin 3 ↪ Role)
    (v : Fin 4 → WinnerSet Role) : WinnerSet Role := by
  classical
  exact if candidateValue three v 0 = candidateValue three v 1 then
    candidateValue three v 0 else candidateValue three v 2

private theorem common_value {A : Type*} [DecidableEq A] (p : Fin 4 → A)
    (h : Coherent p) :
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

private theorem interpolable (three : Fin 3 ↪ Role) :
    LocallyInterpolable 3 (counterexample three) := by
  classical
  apply locallyInterpolable_of_patches 3 (candidateTerm three) (candidate_core three)
  intro v
  obtain ⟨bad, hb⟩ := common_value (candidateValue three v) (candidates_coherent three v)
  exact ⟨bad, fun i hi => (candidate_eval three i v).trans (hb i hi)⟩

private theorem values (three : Fin 3 ↪ Role) :
    counterexample three ![singleton (three 0), singleton (three 2),
      singleton (three 2), singleton (three 1)] =
        (singleton (three 1)).union (singleton (three 2)) ∧
    counterexample three ![singleton (three 1), singleton (three 2),
      singleton (three 1), singleton (three 1)] = singleton (three 1) ∧
    counterexample three ![(singleton (three 0)).union (singleton (three 2)),
      singleton (three 2), singleton (three 1), singleton (three 0)] =
        (singleton (three 0)).union (singleton (three 2)) ∧
    counterexample three ![singleton (three 0), singleton (three 0),
      (singleton (three 0)).union (singleton (three 2)), singleton (three 1)] =
        (singleton (three 0)).union (singleton (three 2)) := by
  classical
  have hab := three.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hac := three.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hbc := three.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  simp [counterexample, candidateValue, choice, singleton_inj,
    union_eq_singleton_iff, hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc,
    union_comm, union_left_comm, union_left_idem]

private theorem not_minorant (three : Fin 3 ↪ Role) :
    ¬∃ t : Term Role (Fin 4), t.IsCore ∧ ∀ v,
      (t.eval v).val ⊆ (counterexample three v).val := by
  classical
  rintro ⟨t, ht, hb⟩
  have hab := three.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hac := three.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hbc := three.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  obtain ⟨hA, hB, hC, hD⟩ := values three
  have h := four_valuation_minorant_cover three id t ht
  rcases h with h | h | h | h
  · have hh := hb _ h
    simp [id_eq, hA, val_union, val_singleton, hab, hac] at hh
  · have hh := hb _ h
    simp [id_eq, hB, val_singleton, Ne.symm hbc] at hh
  · have hh := hb _ h
    simp [id_eq, hC, val_union, val_singleton, Ne.symm hab, hbc] at hh
  · have hh := hb _ h
    simp [id_eq, hD, val_union, val_singleton, Ne.symm hab, hbc] at hh

end KFOL.Core.MinorantPatches

namespace KFOL.Core

/-- Three-point interpolation and preservation of every ternary invariant
relation need not admit even a pointwise smaller core operation. -/
theorem exists_three_local_without_core_minorant {Role : Type*} (three : Fin 3 ↪ Role) :
    ∃ f : (Fin 4 → WinnerSet Role) → WinnerSet Role,
      LocallyInterpolable 3 f ∧ PreservesInvariants 3 f ∧
        ¬∃ t : Term Role (Fin 4), t.IsCore ∧ ∀ v, (t.eval v).val ⊆ (f v).val := by
  refine ⟨MinorantPatches.counterexample three, MinorantPatches.interpolable three,
    (locallyInterpolable_iff_preservesInvariants _ _).mp (MinorantPatches.interpolable three),
    MinorantPatches.not_minorant three⟩

end KFOL.Core
