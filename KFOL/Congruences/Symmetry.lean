module

public import KFOL.Congruences.Classification
public import Mathlib.Logic.Equiv.Fintype

/-! # Permutation invariance and the collapse of every nonclosed set to full -/

@[expose] public section

namespace KFOL.WinnerSet

universe u

variable {Role : Type u}

theorem rename_mono (p : Equiv.Perm Role) {A B : WinnerSet Role} (h : A ≤ B) : rename p A ≤ rename p B :=
  Set.image_mono h

@[simp] theorem rename_symm_rename (p : Equiv.Perm Role) (A : WinnerSet Role) :
    rename p.symm (rename p A) = A := by
  apply Subtype.ext
  exact p.symm_image_image A.val

@[simp] theorem rename_rename_symm (p : Equiv.Perm Role) (A : WinnerSet Role) :
    rename p (rename p.symm A) = A := by
  apply Subtype.ext
  exact p.image_symm_image A.val

/-- The finite class-maximum closure of a symmetric congruence commutes
with every internal role permutation. -/
theorem SymmetricCongruence.closureOperator_invariant [Finite Role]
    (θ : SymmetricCongruence Role) (three : Fin 3 ↪ Role) :
    PermutationInvariant (θ.toCongruence.closureOperator three) := by
  intro p A
  change θ.toCongruence.classMaximum three (WinnerSet.rename p A) =
    WinnerSet.rename p (θ.toCongruence.classMaximum three A)
  apply le_antisymm
  · have hh := θ.rename p.symm (θ.toCongruence.related_classMaximum three (WinnerSet.rename p A))
    rw [rename_symm_rename] at hh
    have hm := rename_mono p (θ.toCongruence.le_classMaximum three hh)
    simpa only [rename_rename_symm] using hm
  · exact θ.toCongruence.le_classMaximum three (θ.rename p (θ.toCongruence.related_classMaximum three A))

/-- Conversely an invariant owner-admissible closure gives a congruence
of the entire expansion, not only the underlying owned-choice reduct. -/
def ClosureOperator.symmetricKernel [Nonempty Role] (c : ClosureOperator (WinnerSet Role))
    (hc : AtomClosure c) (hp : PermutationInvariant c) : SymmetricCongruence Role where
  toCongruence := ClosureOperator.kernel c hc
  rename p := by
    intro A B hAB
    change c A = c B at hAB
    change c (rename p A) = c (rename p B)
    rw [hp p A,hp p B,hAB]

/-- Swapping two absent roles leaves a winner set fixed. -/
theorem rename_swap_of_notMem [DecidableEq Role] (A : WinnerSet Role) (x y : Role) (hx : x ∉ A.val) (hy : y ∉ A.val) :
    rename (Equiv.swap x y) A = A := by
  classical
  have hfix (a : Role) (ha : a ∈ A.val) : Equiv.swap x y a = a := by
    exact Equiv.swap_apply_of_ne_of_ne (fun he => hx (he ▸ ha)) (fun he => hy (he ▸ ha))
  apply Subtype.ext
  ext a
  constructor
  · rintro ⟨b,hb,rfl⟩
    rw [hfix b hb]
    exact hb
  · intro ha
    exact ⟨a,ha,hfix a ha⟩

/-- A permutation-invariant closure either fixes a nonempty set or sends it
all the way to full. A single extra role spreads to every absent role by a
swap fixing the original set. No atom assumption or finiteness is used. -/
theorem invariant_closure_eq_or_full [Nonempty Role] (c : ClosureOperator (WinnerSet Role))
    (hp : PermutationInvariant c) (A : WinnerSet Role) : c A = A ∨ c A = full := by
  classical
  by_cases he : c A = A
  · exact Or.inl he
  · apply Or.inr
    have hn : ¬ (c A).val ⊆ A.val := fun h => he (le_antisymm h (c.le_closure A))
    obtain ⟨x,hx,hxA⟩ := Set.not_subset.mp hn
    apply le_antisymm (le_full _)
    intro y _
    by_cases hyA : y ∈ A.val
    · exact c.le_closure A hyA
    · have hi := hp (Equiv.swap x y) A
      rw [rename_swap_of_notMem A x y hxA hyA] at hi
      have hm : y ∈ (rename (Equiv.swap x y) (c A)).val :=
        ⟨x,hx,Equiv.swap_apply_left x y⟩
      rw [← hi] at hm
      exact hm

/-- Every smaller set can be carried inside a larger one by an actual
permutation of the ambient finite role set. -/
theorem exists_rename_le_of_ncard_le [Finite Role] (A B : WinnerSet Role)
    (h : A.val.ncard ≤ B.val.ncard) : ∃ p : Equiv.Perm Role, rename p A ≤ B := by
  classical
  obtain ⟨D,hDB,hD⟩ := Set.exists_subset_card_eq h
  let _ : Fintype A.val := Fintype.ofFinite _
  let _ : Fintype D := Fintype.ofFinite _
  have hcard : Fintype.card A.val = Fintype.card D := by
    rw [Set.fintypeCard_eq_ncard,Set.fintypeCard_eq_ncard,hD]
  let e : A.val ≃ D := Fintype.equivOfCardEq hcard
  refine ⟨e.extendSubtype,?_⟩
  rintro owner ⟨a,ha,rfl⟩
  exact hDB (Equiv.extendSubtype_mem e a ha)

/-- Proper closed supersets force every smaller cardinality to be closed,
using actual ambient permutations and the preceding fixed-or-full law. -/
theorem invariant_closed_of_ncard_le [Finite Role] [Nonempty Role]
    (c : ClosureOperator (WinnerSet Role)) (hp : PermutationInvariant c)
    (A B : WinnerSet Role) (hB : c B = B) (hproper : B ≠ full)
    (hcard : A.val.ncard ≤ B.val.ncard) : c A = A := by
  obtain ⟨p,hpAB⟩ := exists_rename_le_of_ncard_le A B hcard
  have hmon := c.monotone hpAB
  rw [hB] at hmon
  rcases invariant_closure_eq_or_full c hp (rename p A) with he | he
  · apply rename_injective p
    rw [← hp p A,he]
  · rw [he] at hmon
    exact False.elim (hproper (le_antisymm (le_full B) hmon))

end KFOL.WinnerSet
