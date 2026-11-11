module

public import KFOL.Core.ProfileEnvelope
public import KFOL.Equational.Native

/-! # Core completions of a monotone two-owner Boolean profile

The two named profiles are Boolean duals. All remaining singleton profiles
are unanimity, so greatest profile completion fills every Boolean interval
separated by the profile with the full union of the input values.
-/

@[expose] public section

namespace KFOL.Core.Crown

open WinnerSet

universe u v
variable {Role : Type u} {Var : Type v}

private noncomputable def booleanProfiles (b c : Role) (φ : (Var → Bool) → Bool)
    (r : Role) (x : Var → Bool) : Bool := by
  classical
  exact if r = c then φ x else if r = b then !(φ (fun j => !x j))
    else decide (∀ j, x j = true)

private theorem booleanProfiles_admissible [Fintype Role] [Fintype Var]
    (b c : Role) (hbc : b ≠ c) (φ : (Var → Bool) → Bool)
    (hmono : Monotone φ) (hbot : φ (fun _ => false) = false)
    (htop : φ (fun _ => true) = true) :
    AdmissibleProfiles (booleanProfiles b c φ) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro r x y hxy hx
    have hle : x ≤ y := by
      intro j
      cases hxj : x j <;> cases hyj : y j <;> simp_all
    by_cases hrc : r = c
    · subst r
      simp only [booleanProfiles, ite_true] at hx ⊢
      apply Bool.eq_true_of_true_le
      simpa only [hx] using hmono hle
    by_cases hrb : r = b
    · subst r
      have hanti : (fun j => !y j) ≤ fun j => !x j := by
        intro j
        cases hxj : x j <;> cases hyj : y j <;> simp_all
      have hh := hmono hanti
      simp only [booleanProfiles, ite_eq_right hrc, ite_true, Bool.not_eq_true_eq_eq_false] at hx ⊢
      rw [hx] at hh
      exact Bool.eq_false_of_le_false hh
    · simp only [booleanProfiles, ite_eq_right hrc, ite_eq_right hrb, decide_eq_true_eq] at hx ⊢
      exact fun j => hxy j (hx j)
  · intro r
    by_cases hrc : r = c
    · simp [booleanProfiles, hrc, htop]
    by_cases hrb : r = b
    · subst r
      simp [booleanProfiles, hbc, hbot]
    · simp [booleanProfiles, hrc, hrb]
  · intro x hx
    have hc : φ (x c) = true := by simpa [booleanProfiles] using hx c
    have hb : φ (fun j => !x b j) = false := by
      simpa [booleanProfiles, hbc] using hx b
    have hpoint : ∃ j, x b j = true ∧ x c j = true := by
      by_contra hn
      have hle : x c ≤ fun j => !x b j := by
        intro j
        cases hbj : x b j <;> cases hcj : x c j <;> simp_all
      have hh : true ≤ false := by simpa only [hc, hb] using hmono hle
      have hf : (false : Bool) = true := Bool.eq_true_of_true_le hh
      cases hf
    obtain ⟨j, hjb, hjc⟩ := hpoint
    refine ⟨j, fun r => ?_⟩
    by_cases hrc : r = c
    · simpa [hrc] using hjc
    by_cases hrb : r = b
    · simpa [hrb] using hjb
    · have hh : ∀ i, x r i = true := by
        simpa [booleanProfiles, hrc, hrb] using hx r
      exact hh j

/-- Complete a nonconstant monotone Boolean profile to an actual core term.
The named-owner profiles are dual, and every other owner has unanimity.
A strict Boolean interval is evaluated as the union of all input values. -/
theorem exists_boolean_completion [Fintype Role] [Fintype Var]
    (three : Fin 3 ↪ Role) (b c : Role) (hbc : b ≠ c)
    (φ : (Var → Bool) → Bool) (hmono : Monotone φ)
    (hbot : φ (fun _ => false) = false) (htop : φ (fun _ => true) = true) :
    ∃ e : Term Role Var, e.IsCore ∧
      (∀ (v : Var → WinnerSet Role), e.eval v = WinnerSet.singleton c ↔
        φ (fun j => decide (v j = WinnerSet.singleton c)) = true) ∧
      (∀ (v : Var → WinnerSet Role), e.eval v = WinnerSet.singleton b ↔
        φ (fun j => decide (v j ≠ WinnerSet.singleton b)) = false) ∧
      (∀ (v : Var → WinnerSet Role) (r : Role), r ≠ b → r ≠ c →
        (e.eval v = WinnerSet.singleton r ↔ ∀ j, v j = WinnerSet.singleton r)) ∧
      ∀ (v : Var → WinnerSet Role),
        φ (fun j => decide (v j = WinnerSet.singleton c)) = false →
        φ (fun j => decide (v j ≠ WinnerSet.singleton b)) = true →
        (e.eval v).val = ⋃ j, (v j).val := by
  classical
  obtain ⟨q, hq⟩ := (exists_term_iff_admissibleProfiles three (booleanProfiles b c φ)).mpr
    (booleanProfiles_admissible b c hbc φ hmono hbot htop)
  let t := Equational.Core.decode q
  have ht : t.IsCore := Equational.Core.isCore_decode q
  have hsingle (v : Var → WinnerSet Role) (r : Role) :
      t.eval v = WinnerSet.singleton r ↔
        booleanProfiles b c φ r (fun j => decide (v j = WinnerSet.singleton r)) = true := by
    dsimp [t]
    rw [Equational.Core.eval_decode, winnerSet_eq_singleton_iff_profile, hq]
  obtain ⟨e, he, hprofile, hamb, _⟩ := exists_profile_maximum three t ht
  have hc (v : Var → WinnerSet Role) : e.eval v = WinnerSet.singleton c ↔
      φ (fun j => decide (v j = WinnerSet.singleton c)) = true := by
    rw [hprofile, hsingle]
    simp [booleanProfiles]
  have hb (v : Var → WinnerSet Role) : e.eval v = WinnerSet.singleton b ↔
      φ (fun j => decide (v j ≠ WinnerSet.singleton b)) = false := by
    rw [hprofile, hsingle]
    simp [booleanProfiles, hbc]
  have hother (v : Var → WinnerSet Role) (r : Role) (hrb : r ≠ b) (hrc : r ≠ c) :
      e.eval v = WinnerSet.singleton r ↔ ∀ j, v j = WinnerSet.singleton r := by
    rw [hprofile, hsingle]
    simp [booleanProfiles, hrb, hrc]
  refine ⟨e, he, hc, hb, hother, ?_⟩
  intro v hL hU
  by_cases ha : (t.eval v).Ambiguous
  · exact hamb v ha
  · obtain ⟨r, hr⟩ : ∃ r, t.eval v = WinnerSet.singleton r := by
      simpa only [WinnerSet.Ambiguous, not_forall, not_not] using ha
    have her : e.eval v = WinnerSet.singleton r := (hprofile v r).mpr hr
    have hrc : r ≠ c := by
      intro h
      subst r
      exact Bool.false_ne_true (hL.symm.trans ((hc v).mp her))
    have hrb : r ≠ b := by
      intro h
      subst r
      have hf : (true : Bool) = false := hU.symm.trans ((hb v).mp her)
      cases hf
    have hv : ∀ j, v j = WinnerSet.singleton r := (hother v r hrb hrc).mp her
    obtain ⟨base, _⟩ := ht.vars_nonempty
    rw [her]
    ext k
    constructor
    · intro hk
      exact Set.mem_iUnion.mpr ⟨base, by simpa [hv base] using hk⟩
    · intro hk
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hk
      simpa [hv j] using hj

/-- Finite-set form of the Boolean completion, for interval-separating families. -/
theorem exists_set_completion [Fintype Role] [Fintype Var]
    (three : Fin 3 ↪ Role) (b c : Role) (hbc : b ≠ c)
    (φ : Finset Var → Bool) (hmono : Monotone φ)
    (hbot : φ ∅ = false) (htop : φ Finset.univ = true) :
    ∃ e : Term Role Var, e.IsCore ∧
      (∀ (v : Var → WinnerSet Role), e.eval v = WinnerSet.singleton c ↔
        φ (Finset.univ.filter (fun j => v j = WinnerSet.singleton c)) = true) ∧
      (∀ (v : Var → WinnerSet Role), e.eval v = WinnerSet.singleton b ↔
        φ (Finset.univ.filter (fun j => v j ≠ WinnerSet.singleton b)) = false) ∧
      (∀ (v : Var → WinnerSet Role) (r : Role), r ≠ b → r ≠ c →
        (e.eval v = WinnerSet.singleton r ↔ ∀ j, v j = WinnerSet.singleton r)) ∧
      ∀ (v : Var → WinnerSet Role),
        φ (Finset.univ.filter (fun j => v j = WinnerSet.singleton c)) = false →
        φ (Finset.univ.filter (fun j => v j ≠ WinnerSet.singleton b)) = true →
        (e.eval v).val = ⋃ j, (v j).val := by
  classical
  let ψ (x : Var → Bool) := φ (Finset.univ.filter (fun j => x j = true))
  have hψmono : Monotone ψ := by
    intro x y hxy
    apply hmono
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    apply Bool.eq_true_of_true_le
    simpa only [hj] using hxy j
  have hψbot : ψ (fun _ => false) = false := by simpa [ψ] using hbot
  have hψtop : ψ (fun _ => true) = true := by simpa [ψ] using htop
  obtain ⟨e, he, hc, hb, ho, hgap⟩ :=
    exists_boolean_completion three b c hbc ψ hψmono hψbot hψtop
  refine ⟨e, he, ?_, ?_, ho, ?_⟩
  · intro v
    simpa [ψ] using hc v
  · intro v
    simpa [ψ] using hb v
  · intro v hL hU
    apply hgap v
    · simpa [ψ] using hL
    · simpa [ψ] using hU

end KFOL.Core.Crown
