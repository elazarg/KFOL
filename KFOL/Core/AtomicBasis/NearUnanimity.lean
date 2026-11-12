module

public import KFOL.Core.AtomicBasis.Quotient
public import KFOL.Core.ProfileSynthesis

/-! # The exact near-unanimity arity of the atomic quotient -/

@[expose] public section

namespace KFOL.Core.AtomicBasis

universe u

variable {Role : Type u} [Fintype Role] [DecidableEq Role]

omit [DecidableEq Role] in
theorem almostAll_admissible :
    AdmissibleProfiles (fun (_ : Role) (v : Fin (Fintype.card Role + 1) → Bool) => almostAll v) := by
  classical
  constructor
  · intro r v w hvw hv
    simp only [almostAll, decide_eq_true_eq] at hv ⊢
    intro i j hi hj
    apply hv i j
    · cases he : v i
      · rfl
      · have := hvw i he
        simp_all
    · cases he : v j
      · rfl
      · have := hvw j he
        simp_all
  · intro r
    simp [almostAll]
  · intro v hv
    by_contra hn
    push Not at hn
    choose owner ho using hn
    have hinj : Function.Injective owner := by
      intro i j hij
      have h := hv (owner i)
      simp only [almostAll, decide_eq_true_eq] at h
      apply h i j
      · simpa using ho i
      · simpa [hij] using ho j
    have hc := Fintype.card_le_of_injective owner hinj
    simp only [Fintype.card_fin] at hc
    omega

/-- The existing constructive profile compiler supplies a concrete threshold
term; no fixed-point or external existence theorem enters the construction. -/
noncomputable def nearUnanimityTerm (three : Fin 3 ↪ Role) :
    Equational.Term (Equational.CoreSymbol Role) (Fin (Fintype.card Role + 1)) :=
  synthesizeProfiles three (fun _ v => almostAll v) almostAll_admissible

theorem nearUnanimityTerm_profile (three : Fin 3 ↪ Role) (i : Role)
    (v : Fin (Fintype.card Role + 1) → Bool) :
    profile i v (nearUnanimityTerm three) = almostAll v :=
  profile_synthesizeProfiles three _ almostAll_admissible i v

private theorem almostAll_single_exception {Var : Type*} [DecidableEq Var]
    (j : Var) (b : Bool) : almostAll (fun i => if i = j then b else true) = true := by
  simp only [almostAll, decide_eq_true_eq]
  intro i l hi hl
  have hij : i = j := by by_contra h; simp [h] at hi
  have hlj : l = j := by by_contra h; simp [h] at hl
  exact hij.trans hlj.symm

private theorem almostAll_single_true {n : ℕ} (hn : 3 ≤ n) (j : Fin n) (b : Bool) :
    almostAll (fun i => if i = j then b else false) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  simp only [almostAll, decide_eq_true_eq] at h
  let a : Fin n := ⟨0, by omega⟩
  let c : Fin n := ⟨1, by omega⟩
  let d : Fin n := ⟨2, by omega⟩
  have hac : a ≠ c := by simp [a, c]
  have had : a ≠ d := by simp [a, d]
  have hcd : c ≠ d := by simp [c, d]
  by_cases ha : a = j
  · have hc : c ≠ j := fun he => hac (ha.trans he.symm)
    have hd : d ≠ j := fun he => had (ha.trans he.symm)
    exact hcd (h c d (by simp [hc]) (by simp [hd]))
  · by_cases hc : c = j
    · have hd : d ≠ j := fun he => hcd (hc.trans he.symm)
      exact had (h a d (by simp [ha]) (by simp [hd]))
    · exact hac (h a c (by simp [ha]) (by simp [hc]))

theorem nearUnanimityTerm_isNearUnanimity (three : Fin 3 ↪ Role) :
    NearUnanimity (nearUnanimityTerm three) := by
  let _ := structureOf Role
  have hc : 3 ≤ Fintype.card Role := by
    simpa using Fintype.card_le_of_injective three three.injective
  intro x y j
  apply indicators_separate
  intro i
  rw [realize_indicator, nearUnanimityTerm_profile]
  have he : (fun l => indicator i (if l = j then y else x)) =
      fun l => if l = j then indicator i y else indicator i x := by
    funext l
    split <;> rfl
  rw [he]
  cases hx : indicator i x
  · exact almostAll_single_true (by omega) j (indicator i y)
  · exact almostAll_single_exception j (indicator i y)

/-- No smaller positive arity can be near-unanimity: its owner profiles
would have a common source, while each source has its own exceptional row. -/
theorem not_nearUnanimity_of_arity_le {n : ℕ} (hn : n ≤ Fintype.card Role)
    (t : Equational.Term (Equational.CoreSymbol Role) (Fin n)) : ¬NearUnanimity t := by
  intro hnu
  let _ := structureOf Role
  obtain ⟨owners⟩ := Function.Embedding.nonempty_of_card_le (α := Fin n) (β := Role) (by simpa using hn)
  have hp : ∀ r : Fin n,
      profile (owners r) (fun j => decide (j ≠ r)) t = true := by
    intro r
    have he := hnu (some (owners r)) none r
    have hi := congrArg (indicator (owners r)) he
    rw [realize_indicator] at hi
    simpa [indicator] using hi
  obtain ⟨j, hj⟩ := profile_common_source owners owners.injective
    (fun r j => decide (j ≠ r)) t hp
  simpa using hj j

end KFOL.Core.AtomicBasis
