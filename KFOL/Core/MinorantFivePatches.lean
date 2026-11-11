module

public import KFOL.Core.MinorantFiveCertificate
public import KFOL.Core.MinorantFive
public import KFOL.Core.RelationalInterpolation
public import KFOL.Algebra.TestDomains
public import Mathlib.Tactic.FinCases

/-! # Four-point interpolation without a core minorant

The finite calculation checks five explicit core patches on all formal input
statuses. Set-valued substitution transfers the certificate to arbitrary role
sets; the five-row cover then excludes every core minorant.
-/

@[expose] public section

namespace KFOL.Core.FivePatch

open WinnerSet WinnerSet.StatusModel

private def candidateTerm {Role : Type*} (three : Fin 3 ↪ Role) : Fin 5 → Term Role (Fin 5) :=
  let X := Term.var 0
  let Y := Term.var 1
  let Z := Term.var 2
  let W := Term.var 3
  let V := Term.var 4
  ![(Term.unionTerm three (Term.unionTerm three (Term.unionTerm three (Term.choice (three 0) (Term.choice (three 2) X W) (Term.choice (three 2) Y (Term.unionTerm three Z V))) (Term.choice (three 1) X (Term.choice (three 0) V (Term.choice (three 1) Z (Term.unionTerm three Y W))))) (Term.unionTerm three (Term.choice (three 2) X Z) (Term.choice (three 1) X (Term.choice (three 1) W V)))) (Term.choice (three 0) Y (Term.choice (three 1) X (Term.choice (three 1) V (Term.choice (three 2) Z W))))),
    (Term.unionTerm three (Term.unionTerm three (Term.unionTerm three (Term.unionTerm three (Term.unionTerm three (Term.choice (three 2) Y (Term.unionTerm three V (Term.choice (three 1) Z (Term.unionTerm three X W)))) (Term.choice (three 1) Y (Term.unionTerm three X (Term.choice (three 2) X (Term.unionTerm three Z W))))) (Term.choice (three 2) X (Term.choice (three 2) Y (Term.choice (three 2) V (Term.choice (three 0) Z W))))) (Term.choice (three 2) Y (Term.choice (three 0) Z (Term.choice (three 1) W V)))) (Term.choice (three 1) X (Term.choice (three 1) Y (Term.choice (three 0) Z V)))) (Term.choice (three 1) X (Term.choice (three 1) Y (Term.choice (three 1) W V)))),
    (Term.unionTerm three (Term.unionTerm three (Term.unionTerm three (Term.unionTerm three (Term.unionTerm three (Term.unionTerm three Z (Term.choice (three 1) X (Term.choice (three 0) Y (Term.choice (three 1) Z V)))) (Term.choice (three 0) (Term.choice (three 1) Z W) (Term.choice (three 1) Y (Term.choice (three 2) X W)))) (Term.choice (three 1) X (Term.choice (three 1) W (Term.choice (three 1) V (Term.choice (three 0) Y Z))))) (Term.choice (three 0) Z (Term.choice (three 2) Y (Term.choice (three 1) W V)))) (Term.choice (three 0) Z (Term.choice (three 2) X (Term.choice (three 2) Y V)))) (Term.choice (three 1) (Term.choice (three 0) Y X) Z)),
    (Term.unionTerm three (Term.unionTerm three (Term.unionTerm three (Term.unionTerm three (Term.choice (three 0) (Term.choice (three 2) Y V) (Term.choice (three 2) W (Term.choice (three 1) X Z))) (Term.choice (three 0) W (Term.choice (three 2) (Term.choice (three 1) X Y) (Term.unionTerm three Y Z)))) (Term.choice (three 0) (Term.choice (three 2) Z W) (Term.choice (three 1) X (Term.choice (three 1) Y V)))) (Term.choice (three 0) (Term.choice (three 2) Z W) (Term.choice (three 2) X (Term.choice (three 2) Y V)))) (Term.choice (three 2) (Term.choice (three 1) (Term.choice (three 0) Y X) Z) W)),
    (Term.unionTerm three (Term.unionTerm three (Term.choice (three 0) V (Term.unionTerm three Y (Term.choice (three 1) Z (Term.unionTerm three X W)))) (Term.choice (three 2) X (Term.choice (three 2) V (Term.unionTerm three W (Term.choice (three 0) Y Z))))) (Term.choice (three 1) V (Term.choice (three 2) Z (Term.choice (three 0) W (Term.choice (three 1) X Y)))))]

private theorem candidate_core {Role : Type*} (three : Fin 3 ↪ Role) (i : Fin 5) :
    (candidateTerm three i).IsCore := by
  fin_cases i <;> trivial

private theorem candidate_eval {Role : Type*} (three : Fin 3 ↪ Role)
    (v : Fin 5 → WinnerSet Role) (i : Fin 5) :
    (candidateTerm three i).eval v =
      image three v (formalCandidates (fun j => code three (v j)) i) := by
  fin_cases i <;> simp [candidateTerm, formalCandidates, Term.eval,
    image_union, image_choice, image_input]

private noncomputable def counterexample {Role : Type*} (three : Fin 3 ↪ Role)
    (v : Fin 5 → WinnerSet Role) : WinnerSet Role :=
  let p := formalCandidates (fun j => code three (v j))
  image three v (if p 0 = p 1 then p 0 else p 2)

private theorem patches {Role : Type*} (three : Fin 3 ↪ Role)
    (v : Fin 5 → WinnerSet Role) :
    ∃ bad : Fin 5, ∀ i, i ≠ bad → (candidateTerm three i).eval v = counterexample three v := by
  obtain ⟨bad, hb⟩ := formal_coherent (fun j => code three (v j))
  refine ⟨bad, fun i hi => ?_⟩
  rw [candidate_eval]
  exact congrArg (image three v) (hb i hi)

private theorem interpolable {Role : Type*} (three : Fin 3 ↪ Role) :
    LocallyInterpolable 4 (counterexample three) :=
  locallyInterpolable_of_patches 4 (candidateTerm three) (candidate_core three)
    (counterexample three) (patches three)

private def critical {Role : Type*} (three : Fin 3 ↪ Role) : Fin 5 → Fin 5 → WinnerSet Role :=
  let a := three 0
  let b := three 1
  let c := three 2
  ![![singleton a, singleton b, singleton b, (singleton b).union (singleton c), singleton c],
    ![singleton a, singleton b, singleton a, singleton a, singleton a],
    ![singleton c, singleton c, singleton b, singleton c, singleton a],
    ![singleton c, (singleton b).union (singleton c), singleton b, singleton a, singleton b],
    ![singleton b, singleton c, (singleton b).union (singleton c),
      (singleton b).union (singleton c), singleton a]]

private def forbidden {Role : Type*} (three : Fin 3 ↪ Role) : Fin 5 → Role :=
  ![three 0, three 1, three 1, three 0, three 0]

set_option maxHeartbeats 2000000 in
private theorem candidate_excludes {Role : Type*} (three : Fin 3 ↪ Role)
    (i j : Fin 5) (hji : j ≠ i) :
    forbidden three i ∉ ((candidateTerm three j).eval (critical three i)).val := by
  classical
  have hab := three.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hac := three.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hbc := three.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  have hba := hab.symm
  have hca := hac.symm
  have hcb := hbc.symm
  fin_cases i <;> fin_cases j <;>
    simp_all [forbidden, critical, candidateTerm, Term.eval, choice,
      singleton_inj, union_eq_singleton_iff, val_union, val_singleton]

private theorem excludes {Role : Type*} (three : Fin 3 ↪ Role) (i : Fin 5) :
    forbidden three i ∉ (counterexample three (critical three i)).val := by
  have pick : ∀ x y : Fin 5, ∃ j, j ≠ x ∧ j ≠ y := by decide
  obtain ⟨bad, hb⟩ := patches three (critical three i)
  obtain ⟨j, hji, hjb⟩ := pick i bad
  rw [← hb j hjb]
  exact candidate_excludes three i j hji

private theorem not_minorant {Role : Type*} (three : Fin 3 ↪ Role) :
    ¬∃ t : Term Role (Fin 5), t.IsCore ∧ ∀ v,
      (t.eval v).val ⊆ (counterexample three v).val := by
  rintro ⟨t, ht, hb⟩
  have cover : ∃ i : Fin 5, forbidden three i ∈ (t.eval (critical three i)).val := by
    rcases five_valuation_minorant_cover three id t ht with h | h | h | h | h
    · exact ⟨0, by simpa [critical, forbidden] using h⟩
    · exact ⟨1, by simpa [critical, forbidden] using h⟩
    · exact ⟨2, by simpa [critical, forbidden] using h⟩
    · exact ⟨3, by simpa [critical, forbidden] using h⟩
    · exact ⟨4, by simpa [critical, forbidden] using h⟩
  obtain ⟨i, hi⟩ := cover
  exact excludes three i (hb _ hi)

end KFOL.Core.FivePatch

namespace KFOL.Core

/-- Four-point interpolation and preservation of every quaternary invariant
relation need not leave any pointwise core minorant. -/
theorem exists_four_local_without_core_minorant {Role : Type*} (three : Fin 3 ↪ Role) :
    ∃ f : (Fin 5 → WinnerSet Role) → WinnerSet Role,
      LocallyInterpolable 4 f ∧ PreservesInvariants 4 f ∧
        ¬∃ t : Term Role (Fin 5), t.IsCore ∧ ∀ v, (t.eval v).val ⊆ (f v).val := by
  refine ⟨FivePatch.counterexample three, FivePatch.interpolable three,
    (locallyInterpolable_iff_preservesInvariants _ _).mp (FivePatch.interpolable three),
    FivePatch.not_minorant three⟩

end KFOL.Core
