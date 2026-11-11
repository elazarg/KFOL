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

private noncomputable def seed {Role : Type*} (three : Fin 3 ↪ Role)
    (v : Fin 5 → WinnerSet Role) (x : Fin 3 ⊕ Fin 5) : WinnerSet Role := by
  classical
  exact match x with
    | .inl r => singleton (three r)
    | .inr j => if ∃ r : Fin 3, v j = singleton (three r) then
        (singleton (three 0)).union (singleton (three 1)) else v j

private noncomputable def code {Role : Type*} (three : Fin 3 ↪ Role)
    (A : WinnerSet Role) : Fin 4 := by
  classical
  exact if A = singleton (three 0) then 0 else
    if A = singleton (three 1) then 1 else
    if A = singleton (three 2) then 2 else 3

private theorem seed_eq_singleton_iff {Role : Type*} (three : Fin 3 ↪ Role)
    (v : Fin 5 → WinnerSet Role) (r : Fin 3) (x : Fin 3 ⊕ Fin 5) :
    seed three v x = singleton (three r) ↔ x = .inl r := by
  classical
  cases x with
  | inl s => simp [seed, singleton_inj, three.injective.eq_iff]
  | inr j =>
    simp only [seed, Sum.inr_ne_inl, iff_false]
    split_ifs with h
    · intro he
      have hh := (union_eq_singleton_iff _ _ _).mp he
      have h₀ := singleton_inj.mp hh.1
      have h₁ := singleton_inj.mp hh.2
      have h01 : three 0 ≠ three 1 := three.injective.ne (by decide)
      exact h01 (h₀.trans h₁.symm)
    · intro he
      exact h ⟨r, he⟩

private theorem expand_formalInput {Role : Type*} (three : Fin 3 ↪ Role)
    (v : Fin 5 → WinnerSet Role) (j : Fin 5) :
    expand (seed three v) (Value.toWinner (formalInput (code three (v j)) j)) = v j := by
  classical
  by_cases h₀ : v j = singleton (three 0)
  · simp [code, h₀, formalInput, seed]
  by_cases h₁ : v j = singleton (three 1)
  · simp [code, h₁, formalInput, seed]
  by_cases h₂ : v j = singleton (three 2)
  · simp [code, h₂, formalInput, seed]
  have h : ¬∃ r : Fin 3, v j = singleton (three r) := by
    rintro ⟨r, hr⟩
    have hcases : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    rcases hcases with rfl | rfl | rfl <;> contradiction
  simp [code, h₀, h₁, h₂, formalInput, seed, h]


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

private noncomputable def image {Role : Type*} (three : Fin 3 ↪ Role)
    (v : Fin 5 → WinnerSet Role) (A : Value (Fin 3 ⊕ Fin 5)) : WinnerSet Role :=
  expand (seed three v) (Value.toWinner A)

private theorem image_union {Role : Type*} (three : Fin 3 ↪ Role)
    (v : Fin 5 → WinnerSet Role) (A B : Value (Fin 3 ⊕ Fin 5)) :
    image three v (Value.union A B) = (image three v A).union (image three v B) := by
  simp only [image, Value.toWinner_union, expand_union]

private theorem image_choice {Role : Type*} (three : Fin 3 ↪ Role)
    (v : Fin 5 → WinnerSet Role) (r : Fin 3) (A B : Value (Fin 3 ⊕ Fin 5)) :
    image three v (Value.choice (.inl r) A B) =
      choice (three r) (image three v A) (image three v B) := by
  simp only [image, Value.toWinner_choice]
  exact expand_choice (seed three v) (.inl r) (three r)
    (seed_eq_singleton_iff three v r) _ _

private theorem image_input {Role : Type*} (three : Fin 3 ↪ Role)
    (v : Fin 5 → WinnerSet Role) (j : Fin 5) :
    image three v (formalInput (code three (v j)) j) = v j :=
  expand_formalInput three v j

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
