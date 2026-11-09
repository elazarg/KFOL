module

public import KFOL.Congruences.Classification

/-! # The equivalent fixed-family classification, with actual intersections -/

@[expose] public section

namespace KFOL.WinnerSet

universe u

variable {Role : Type u}

/-- Intersecting all designated supersets always gives a closure operator;
the empty family is allowed and gives the constant-full closure. -/
def familyClosure (F : Set (WinnerSet Role)) : ClosureOperator (WinnerSet Role) where
  toFun := familyClosureValue F
  monotone' := by
    intro A B hAB owner howner C hC hBC
    exact howner C hC (hAB.trans hBC)
  le_closure' A := by intro owner howner B _ hAB; exact hAB howner
  idempotent' A := by
    apply Subtype.ext
    apply Set.Subset.antisymm
    · intro owner howner B hB hAB
      exact howner B hB (fun i hi => hi B hB hAB)
    · intro owner howner B hB hAB
      exact hAB howner

@[simp] theorem familyClosure_fixed (F : Set (WinnerSet Role)) (A : WinnerSet Role) (hA : A ∈ F) :
    familyClosure F A = A := by
  apply le_antisymm
  · intro owner howner
    exact howner A hA le_rfl
  · exact (familyClosure F).le_closure A

/-- A family satisfying the intersection condition contains every output
of its displayed closure formula. -/
theorem familyClosure_mem [Nonempty Role] (F : Set (WinnerSet Role)) (hF : AdmissibleFamily F)
    (A : WinnerSet Role) : familyClosure F A ∈ F := by
  let G : Set (WinnerSet Role) := {B | B ∈ F ∧ A ≤ B}
  have hG : G.Nonempty := ⟨full,hF.1,le_full A⟩
  have hne : (⋂ B ∈ G, B.val).Nonempty := by
    obtain ⟨owner,howner⟩ := A.property
    refine ⟨owner,?_⟩
    simp only [Set.mem_iInter]
    intro B hB
    exact hB.2 howner
  have hmem := hF.2.1 G hG (fun _ h => h.1) hne
  have he : (⟨⋂ B ∈ G, B.val,hne⟩ : WinnerSet Role) = familyClosure F A := by
    apply Subtype.ext
    ext owner
    simp only [Set.mem_iInter, familyClosure, familyClosureValue, Set.mem_ofPred_eq, G]
    constructor
    · intro h B hB hAB
      exact h B ⟨hB,hAB⟩
    · intro h B hB
      exact h B hB.1 hB.2
  exact he ▸ hmem

theorem familyClosure_atom [Nonempty Role] (F : Set (WinnerSet Role)) (hF : AdmissibleFamily F) :
    AtomClosure (familyClosure F) := by
  intro owner
  by_cases he : familyClosure F (singleton owner) = full
  · exact Or.inr he
  · apply Or.inl
    have howner : owner ∈ (familyClosure F (singleton owner)).val :=
      (familyClosure F).le_closure (singleton owner) rfl
    have hsingle := hF.2.2 _ (familyClosure_mem F hF _) he owner howner
    exact familyClosure_fixed F _ hsingle

/-- The family is exactly the fixed points of the closure constructed from
it, establishing both exhaustiveness and absence of redundant family data. -/
theorem familyClosure_fixed_iff [Nonempty Role] (F : Set (WinnerSet Role)) (hF : AdmissibleFamily F)
    (A : WinnerSet Role) : familyClosure F A = A ↔ A ∈ F := by
  exact ⟨fun he => he ▸ familyClosure_mem F hF A, familyClosure_fixed F A⟩

/-- Every owner-admissible closure has precisely the stated family closure
properties, with arbitrary intersections rather than finite approximations. -/
theorem fixedFamily_admissible [Nonempty Role] (c : ClosureOperator (WinnerSet Role)) (hc : AtomClosure c) :
    AdmissibleFamily {A | c A = A} := by
  refine ⟨ClosureOperator.full c,?_,?_⟩
  · intro G _ hG hne
    apply le_antisymm
    · intro owner howner
      simp only [Set.mem_iInter]
      intro B hB
      have hIB : (⟨⋂ A ∈ G,A.val,hne⟩ : WinnerSet Role) ≤ B := by
        intro i hi
        exact Set.mem_iInter.mp (Set.mem_iInter.mp hi B) hB
      have he : c B = B := hG hB
      have hmono := c.monotone hIB
      rw [he] at hmono
      exact hmono howner
    · exact c.le_closure _
  · intro A hA hproper owner howner
    have hsingle : singleton owner ≤ A := Set.singleton_subset_iff.mpr howner
    have hmono := c.monotone hsingle
    rw [hA] at hmono
    rcases hc owner with he | he
    · exact he
    · rw [he] at hmono
      exact False.elim (hproper (le_antisymm (le_full A) hmono))

/-- Recover the original closure by intersecting its closed supersets. -/
theorem familyClosure_fixedFamily (c : ClosureOperator (WinnerSet Role)) :
    familyClosure {A | c A = A} = c := by
  apply _root_.ClosureOperator.ext
  intro A
  apply le_antisymm
  · intro owner howner
    exact howner (c A) (c.idempotent A) (c.le_closure A)
  · intro owner howner B hB hAB
    have hm := c.monotone hAB
    rw [hB] at hm
    exact hm howner

/-- Complete fixed-family version of the closure classification. -/
noncomputable def atomClosuresEquivFamilies [Nonempty Role] :
    {c : ClosureOperator (WinnerSet Role) // AtomClosure c} ≃
      {F : Set (WinnerSet Role) // AdmissibleFamily F} where
  toFun c := ⟨{A | c.val A = A},fixedFamily_admissible c.val c.property⟩
  invFun F := ⟨familyClosure F.val,familyClosure_atom F.val F.property⟩
  left_inv c := Subtype.ext (familyClosure_fixedFamily c.val)
  right_inv F := by
    apply Subtype.ext
    ext A
    exact familyClosure_fixed_iff F.val F.property A

noncomputable def Congruence.equivFamilies [Finite Role] [Nonempty Role] (three : Fin 3 ↪ Role) :
    Congruence Role ≃ {F : Set (WinnerSet Role) // AdmissibleFamily F} :=
  (Congruence.equivAtomClosures three).trans atomClosuresEquivFamilies

/-- The displayed family correspondence realizes the original relation by
exactly the intersection-of-supersets formula from the paper. -/
theorem Congruence.equivFamilies_rel_iff [Finite Role] [Nonempty Role] (three : Fin 3 ↪ Role)
    (θ : Congruence Role) (A B : WinnerSet Role) :
    θ.r A B ↔ familyClosureValue ((Congruence.equivFamilies three) θ).val A =
      familyClosureValue ((Congruence.equivFamilies three) θ).val B := by
  change θ.r A B ↔ familyClosure {C | θ.closureOperator three C = C} A =
    familyClosure {C | θ.closureOperator three C = C} B
  rw [familyClosure_fixedFamily]
  exact (θ.closureOperator_rel_iff three A B).symm

/-- Every congruence has exactly one admissible fixed family. -/
theorem Congruence.exists_unique_family [Finite Role] [Nonempty Role] (three : Fin 3 ↪ Role)
    (θ : Congruence Role) :
    ∃! F : Set (WinnerSet Role), AdmissibleFamily F ∧
      ∀ A B, θ.r A B ↔ familyClosureValue F A = familyClosureValue F B := by
  let F := (Congruence.equivFamilies three) θ
  refine ⟨F.val,⟨F.property,θ.equivFamilies_rel_iff three⟩,?_⟩
  intro G hG
  have he : familyClosure G = familyClosure F.val := by
    apply closure_eq_of_kernel_eq
    intro A B
    exact (hG.2 A B).symm.trans (θ.equivFamilies_rel_iff three A B)
  apply Set.ext
  intro A
  rw [← familyClosure_fixed_iff G hG.1 A,← familyClosure_fixed_iff F.val F.property A,he]

end KFOL.WinnerSet
