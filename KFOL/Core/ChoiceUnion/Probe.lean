module

public import KFOL.Core.ChoiceUnion.Cover

/-! # Complete support tests in the three-element dissemilattice -/

@[expose] public section

namespace KFOL.Dissemilattice

universe v

/-- The separating valuation for support A and variable j: P at j, N at
other members of A, and B outside A. -/
noncomputable def probe {Var : Type v} (A : Finset Var) (j : Var) (x : Var) : Three := by
  classical
  exact if x ∈ A then if x = j then .p else .n else .b

theorem evalSupport_probe {Var : Type v} [DecidableEq Var] (A : Finset Var) (j : Var) (B : Support Var) :
    evalSupport three_laws B (probe A j) =
      if B.val ⊆ A then if j ∈ B.val then Three.p else .n else .b := by
  classical
  let _ := three_laws.meetSemilattice
  suffices ∀ (S : Finset Var) (hS : S.Nonempty), S.inf' hS (probe A j) =
      if S ⊆ A then if j ∈ S then Three.p else .n else .b by
    exact this B.val B.property
  intro S hS
  induction hS using Finset.Nonempty.cons_induction with
  | singleton x =>
    by_cases hxA : x ∈ A <;> by_cases hxj : x = j
    all_goals simp_all [probe,Finset.singleton_subset_iff,eq_comm]
  | cons x S hx hS ih =>
    rw [Finset.inf'_cons hS (probe A j)]
    rw [ih]
    change Three.mul (probe A j x) _ = _
    clear ih
    by_cases hxA : x ∈ A
    · by_cases hSA : S ⊆ A
      · by_cases hxj : x = j
        · subst x
          simp [probe,hxA,hSA,hx,Three.mul,Finset.insert_subset_iff]
        · have hjx : j ≠ x := Ne.symm hxj
          by_cases hjS : j ∈ S
          · simp [probe,hxA,hSA,hxj,hjx,hjS,Three.mul,Finset.insert_subset_iff ]
          · simp [probe,hxA,hSA,hxj,hjx,hjS,Three.mul,Finset.insert_subset_iff ]
      · by_cases hxj : x = j
        · subst x
          simp [probe,hxA,hSA,Three.mul,Finset.insert_subset_iff]
        · simp [probe,hxA,hSA,hxj,Three.mul,Finset.insert_subset_iff]
    · simp [probe,hxA,Three.mul,Finset.insert_subset_iff]

/-- The probe detects exactly the contained monomials that cover j. -/
theorem evalSupport_probe_eq_p {Var : Type v} (A : Finset Var) (j : Var) (B : Support Var) :
    evalSupport three_laws B (probe A j) = Three.p ↔ B.val ⊆ A ∧ j ∈ B.val := by
  classical
  rw [evalSupport_probe]
  split_ifs <;> simp_all

theorem Three.add_eq_p (x y : Three) : Three.add x y = .p ↔ x = .p ∨ y = .p := by
  cases x <;> cases y <;> simp [Three.add]

/-- The largest join value is attained by a finite sum exactly when an
actual monomial summand attains it. -/
theorem three_sup'_eq_p {Index : Type v} (F : Finset Index) (hF : F.Nonempty) (f : Index → Three) :
    letI := three_laws.joinSemilattice
    F.sup' hF f = Three.p ↔ ∃ i ∈ F, f i = .p := by
  let _ := three_laws.joinSemilattice
  induction hF using Finset.Nonempty.cons_induction with
  | singleton i => simp
  | cons i F hi hF ih =>
    rw [Finset.sup'_cons hF f]
    change Three.add (f i) (F.sup' hF f) = Three.p ↔ _
    rw [Three.add_eq_p]
    simpa only [Finset.mem_cons,exists_eq_or_imp] using or_congr Iff.rfl ih

theorem evalNormal_eq_p_iff {Var : Type v} (F : NormalForm Var) (v : Var → Three) :
    evalNormal three_laws F v = Three.p ↔ ∃ B ∈ F.val, evalSupport three_laws B v = .p :=
  three_sup'_eq_p F.val F.property (fun B => evalSupport three_laws B v)

/-- Equality of the actual three-element functions forces the exact support
covering witnesses needed in arbitrary models of the seven laws. -/
theorem cover_of_three_equality {Var : Type v} (F G : NormalForm Var)
    (hFG : ∀ v : Var → Three, evalNormal three_laws F v = evalNormal three_laws G v)
    (A : Support Var) (hA : A ∈ F.val) (j : Var) (hj : j ∈ A.val) :
    ∃ B ∈ G.val, B.val ⊆ A.val ∧ j ∈ B.val := by
  classical
  have hAp : evalSupport three_laws A (probe A.val j) = Three.p :=
    (evalSupport_probe_eq_p A.val j A).mpr ⟨Finset.Subset.refl _,hj⟩
  have hFp : evalNormal three_laws F (probe A.val j) = Three.p :=
    (evalNormal_eq_p_iff F _).mpr ⟨A,hA,hAp⟩
  have hGp : evalNormal three_laws G (probe A.val j) = Three.p := by
    rw [← hFG]
    exact hFp
  obtain ⟨B,hB,hBp⟩ := (evalNormal_eq_p_iff G _).mp hGp
  exact ⟨B,hB,(evalSupport_probe_eq_p A.val j B).mp hBp⟩

end KFOL.Dissemilattice
