module

public import KFOL.Core.SixPatchCertificate
public import KFOL.Core.SixValuation
public import KFOL.Core.ProfileEnvelope
public import KFOL.Core.RelationalInterpolation
public import KFOL.Algebra.TestDomains
public import Mathlib.Tactic.FinCases

/-! # A five-point interpolation obstruction

Six explicit core operations agree five at a time, and the first is below their
common value. A separately certified six-row law excludes global realization.
-/

@[expose] public section

namespace KFOL.Core.SixPatch

open WinnerSet WinnerSet.StatusModel

private def candidateTerm {Role : Type*} (three : Fin 3 ↪ Role) : Fin 6 → Term Role (Fin 5) :=
  let X := Term.var 0
  let Y := Term.var 1
  let Z := Term.var 2
  let W := Term.var 3
  let V := Term.var 4
  ![(Term.unionTerm three (Term.unionTerm three (Term.choice (three 1) (Term.choice (three 1) (Term.choice (three 0) (Term.choice (three 1) X V) Y) W) V) (Term.choice (three 2) (Term.unionTerm three (Term.choice (three 1) (Term.choice (three 2) X Y) W) (Term.choice (three 2) (Term.choice (three 1) X W) Y)) Z)) (Term.choice (three 2) (Term.unionTerm three (Term.choice (three 2) (Term.choice (three 0) (Term.unionTerm three Y V) W) V) (Term.choice (three 2) (Term.choice (three 1) Y W) (Term.unionTerm three Z V))) X)),
    (Term.unionTerm three (Term.unionTerm three (Term.choice (three 1) (Term.unionTerm three (Term.unionTerm three (Term.choice (three 1) (Term.unionTerm three (Term.unionTerm three (Term.unionTerm three (Term.choice (three 0) X Y) (Term.choice (three 0) (Term.choice (three 0) X Y) Z)) (Term.choice (three 2) Y Z)) Y) V) (Term.choice (three 2) (Term.choice (three 0) (Term.choice (three 1) Y Z) X) V)) (Term.choice (three 2) (Term.choice (three 0) X Z) V)) W) (Term.choice (three 2) (Term.unionTerm three (Term.choice (three 2) X V) (Term.choice (three 2) Z W)) Y)) (Term.choice (three 2) Z W)),
    (Term.unionTerm three (Term.unionTerm three (Term.choice (three 1) (Term.unionTerm three (Term.unionTerm three (Term.choice (three 0) (Term.choice (three 1) (Term.unionTerm three Z V) Y) X) (Term.choice (three 1) (Term.unionTerm three (Term.choice (three 0) X Z) V) X)) (Term.choice (three 2) X Y)) W) (Term.choice (three 2) (Term.choice (three 2) (Term.choice (three 1) Y W) (Term.unionTerm three Z V)) X)) (Term.choice (three 2) (Term.unionTerm three (Term.choice (three 1) (Term.choice (three 2) X Y) W) (Term.choice (three 2) (Term.choice (three 1) X W) Y)) Z)),
    (Term.unionTerm three (Term.unionTerm three (Term.unionTerm three (Term.choice (three 1) (Term.unionTerm three (Term.choice (three 1) (Term.choice (three 0) X Y) (Term.unionTerm three W V)) (Term.choice (three 1) (Term.choice (three 0) (Term.choice (three 0) X Y) Z) Y)) W) (Term.choice (three 2) (Term.choice (three 1) (Term.choice (three 2) X W) Y) Z)) (Term.choice (three 2) (Term.choice (three 1) Y W) (Term.unionTerm three (Term.choice (three 2) X V) Z))) (Term.choice (three 2) (Term.choice (three 2) (Term.unionTerm three (Term.choice (three 2) W V) Z) X) Y)),
    (Term.unionTerm three (Term.unionTerm three (Term.unionTerm three (Term.choice (three 1) (Term.unionTerm three (Term.choice (three 1) (Term.unionTerm three (Term.choice (three 0) (Term.choice (three 1) X V) Y) (Term.choice (three 1) (Term.choice (three 0) (Term.choice (three 0) X Y) Z) Y)) W) (Term.choice (three 2) (Term.choice (three 2) (Term.unionTerm three X Y) Y) Z)) V) (Term.choice (three 2) (Term.choice (three 1) (Term.choice (three 2) X Y) (Term.choice (three 2) X W)) Z)) (Term.choice (three 2) (Term.choice (three 1) (Term.choice (three 2) X Y) W) (Term.unionTerm three Z V))) (Term.choice (three 2) (Term.unionTerm three (Term.unionTerm three (Term.choice (three 0) (Term.choice (three 1) Y Z) X) (Term.choice (three 0) (Term.unionTerm three (Term.choice (three 2) Y W) Z) X)) (Term.choice (three 2) Y W)) V)),
    (Term.unionTerm three (Term.unionTerm three (Term.unionTerm three (Term.choice (three 1) (Term.choice (three 1) (Term.choice (three 0) X Y) (Term.unionTerm three Z V)) W) (Term.choice (three 2) (Term.choice (three 2) (Term.choice (three 1) X W) (Term.unionTerm three X Y)) Z)) (Term.choice (three 2) (Term.choice (three 2) (Term.unionTerm three Y W) X) V)) Z)]

private theorem candidate_core {Role : Type*} (three : Fin 3 ↪ Role) (i : Fin 6) :
    (candidateTerm three i).IsCore := by
  fin_cases i <;> trivial

private theorem candidate_eval {Role : Type*} (three : Fin 3 ↪ Role)
    (v : Fin 5 → WinnerSet Role) (i : Fin 6) :
    (candidateTerm three i).eval v =
      image three v (formalCandidates (fun j => code three (v j)) i) := by
  fin_cases i <;> simp [candidateTerm, formalCandidates, candidates, Term.eval,
    image_union, image_choice, image_input]

private noncomputable def counterexample {Role : Type*} (three : Fin 3 ↪ Role)
    (v : Fin 5 → WinnerSet Role) : WinnerSet Role :=
  let p := formalCandidates (fun j => code three (v j))
  image three v (if p 0 = p 1 then p 0 else p 2)

private theorem patches {Role : Type*} (three : Fin 3 ↪ Role)
    (v : Fin 5 → WinnerSet Role) :
    ∃ bad : Fin 6, ∀ i, i ≠ bad → (candidateTerm three i).eval v = counterexample three v := by
  obtain ⟨bad, hb⟩ := (formal_certificate (fun j => code three (v j))).1
  refine ⟨bad, fun i hi => ?_⟩
  rw [candidate_eval]
  exact congrArg (image three v) (hb i hi)

private theorem interpolable {Role : Type*} (three : Fin 3 ↪ Role) :
    LocallyInterpolable 5 (counterexample three) :=
  locallyInterpolable_of_patches 5 (candidateTerm three) (candidate_core three)
    (counterexample three) (patches three)

private theorem lifted_formal_minorant {Role : Type*} (three : Fin 3 ↪ Role)
    (v : Fin 5 → WinnerSet Role) (s : Fin 5 → Fin 4) :
    let p := formalCandidates s
    (image three v (p 0)).val ⊆
      (image three v (if p 0 = p 1 then p 0 else p 2)).val := by
  exact @image_mono (Fin 5) Role three v _ _ (formal_certificate s).2

private theorem has_minorant {Role : Type*} (three : Fin 3 ↪ Role) :
    ∃ t : Term Role (Fin 5), t.IsCore ∧ ∀ v,
      (t.eval v).val ⊆ (counterexample three v).val := by
  refine ⟨candidateTerm three 0, candidate_core three 0, ?_⟩
  intro v
  rw [candidate_eval]
  exact lifted_formal_minorant three v (fun j => code three (v j))


private noncomputable def namedImage {Role : Type*} (three : Fin 3 ↪ Role)
    (A : Value (Fin 3)) : WinnerSet Role :=
  expand (fun r => singleton (three r)) (Value.toWinner A)

private theorem namedImage_union {Role : Type*} (three : Fin 3 ↪ Role)
    (A B : Value (Fin 3)) :
    namedImage three (Value.union A B) = (namedImage three A).union (namedImage three B) := by
  simp only [namedImage, Value.toWinner_union, expand_union]

private theorem namedImage_choice {Role : Type*} (three : Fin 3 ↪ Role)
    (r : Fin 3) (A B : Value (Fin 3)) :
    namedImage three (Value.choice r A B) =
      choice (three r) (namedImage three A) (namedImage three B) := by
  simp only [namedImage, Value.toWinner_choice]
  exact expand_choice _ r (three r)
    (fun x => by simp only [singleton_inj, three.injective.eq_iff]) _ _

private theorem candidate_eval_named {Role : Type*} (three : Fin 3 ↪ Role)
    (v : Fin 5 → Value (Fin 3)) (i : Fin 6) :
    (candidateTerm three i).eval (fun j => namedImage three (v j)) =
      namedImage three (candidates id v i) := by
  fin_cases i <;> simp [candidateTerm, candidates, Term.eval,
    namedImage_union, namedImage_choice]

private def expected : Fin 6 → Value (Fin 3) :=
  let a := Value.singleton 0
  let b := Value.singleton 1
  let c := Value.singleton 2
  ![Value.union (Value.union a b) c, Value.union b c, Value.union a c,
    Value.union b c, Value.union b c, Value.union a c]

set_option maxRecDepth 100000 in
private theorem critical_checked : ∀ i j : Fin 6, j ≠ i →
    candidates id (SixValuation.values i) j = expected i := by
  decide +kernel

private theorem candidate_critical {Role : Type*} (three : Fin 3 ↪ Role)
    (i j : Fin 6) (hji : j ≠ i) :
    (candidateTerm three j).eval (SixValuation.namedValues three i) =
      namedImage three (expected i) := by
  change (candidateTerm three j).eval
    (fun x => namedImage three (SixValuation.values i x)) = _
  rw [candidate_eval_named, critical_checked i j hji]

private theorem counterexample_critical {Role : Type*} (three : Fin 3 ↪ Role) (i : Fin 6) :
    counterexample three (SixValuation.namedValues three i) =
      namedImage three (expected i) := by
  have pick : ∀ x y : Fin 6, ∃ j, j ≠ x ∧ j ≠ y := by decide
  obtain ⟨bad, hb⟩ := patches three (SixValuation.namedValues three i)
  obtain ⟨j, hji, hjb⟩ := pick i bad
  exact (hb j hjb).symm.trans (candidate_critical three i j hji)

private theorem not_core {Role : Type*} (three : Fin 3 ↪ Role) :
    ¬∃ t : Term Role (Fin 5), t.IsCore ∧ ∀ v, t.eval v = counterexample three v := by
  rintro ⟨t, ht, he⟩
  have hv (i : Fin 6) : t.eval (SixValuation.namedValues three i) =
      namedImage three (expected i) :=
    (he _).trans (counterexample_critical three i)
  have hq : three 0 ∈ (t.eval (SixValuation.namedValues three 0)).val := by
    rw [hv]
    simp [namedImage, expected, Value.toWinner, Value.union, Value.singleton]
  have hout := SixValuation.persistence three id t ht hq
  rcases hout with h | h | h | h | h <;>
    simp [id_eq, hv, namedImage, expected, Value.toWinner, Value.union, Value.singleton] at h

end KFOL.Core.SixPatch

namespace KFOL.Core

/-- Five-point interpolation can fail global core realizability even above a
core operation, uniformly in every role type containing three distinct roles. -/
theorem exists_five_local_noncore {Role : Type*} (three : Fin 3 ↪ Role) :
    ∃ f : (Fin 5 → WinnerSet Role) → WinnerSet Role,
      LocallyInterpolable 5 f ∧ PreservesInvariants 5 f ∧
      (∃ s : Term Role (Fin 5), s.IsCore ∧ ∀ v, (s.eval v).val ⊆ (f v).val) ∧
        ¬∃ t : Term Role (Fin 5), t.IsCore ∧ ∀ v, t.eval v = f v := by
  refine ⟨SixPatch.counterexample three, SixPatch.interpolable three,
    (locallyInterpolable_iff_preservesInvariants _ _).mp (SixPatch.interpolable three),
    SixPatch.has_minorant three, SixPatch.not_core three⟩

/-- Five-point agreement with core terms does not characterize a core
operation. This is the local-test lower bound used in the discussion. -/
theorem exists_five_local_obstruction {Role : Type*} (three : Fin 3 ↪ Role) :
    ∃ f : (Fin 5 → WinnerSet Role) → WinnerSet Role,
      LocallyInterpolable 5 f ∧
        ¬∃ t : Term Role (Fin 5), t.IsCore ∧ ∀ v, t.eval v = f v := by
  obtain ⟨f, hf, _, _, hn⟩ := exists_five_local_noncore three
  exact ⟨f, hf, hn⟩

end KFOL.Core

namespace KFOL.Core

/-- Failure of five-point local tests persists inside one singleton-profile
fiber, between two actual core operations. -/
theorem exists_five_local_profile_fiber_nonconvex {Role : Type*} [Fintype Role]
    (three : Fin 3 ↪ Role) :
    ∃ s t : Term Role (Fin 5), ∃ f : (Fin 5 → WinnerSet Role) → WinnerSet Role,
      s.IsCore ∧ t.IsCore ∧ LocallyInterpolable 5 f ∧ PreservesInvariants 5 f ∧
      (∀ v r, s.eval v = WinnerSet.singleton r ↔ t.eval v = WinnerSet.singleton r) ∧
      (∀ v r, f v = WinnerSet.singleton r ↔ s.eval v = WinnerSet.singleton r) ∧
      (∀ v, (s.eval v).val ⊆ (f v).val ∧ (f v).val ⊆ (t.eval v).val) ∧
      ¬∃ u : Term Role (Fin 5), u.IsCore ∧ ∀ v, u.eval v = f v := by
  classical
  let G := SixPatch.candidateTerm three 0
  let F := SixPatch.counterexample three
  let H := fun v => (F v).reset (G.eval v)
  have hG : G.IsCore := SixPatch.candidate_core three 0
  have hGF (v) : (G.eval v).val ⊆ (F v).val := by
    dsimp [G, F]
    rw [SixPatch.candidate_eval]
    exact SixPatch.lifted_formal_minorant three v (fun j => WinnerSet.StatusModel.code three (v j))
  have hloc : LocallyInterpolable 5 H :=
    locallyInterpolable_reset_right three 5 F (SixPatch.interpolable three) G hG
  have hprofile (v) (r) : H v = WinnerSet.singleton r ↔ G.eval v = WinnerSet.singleton r :=
    WinnerSet.reset_eq_singleton _ _ _
  have hlow (v) : (G.eval v).val ⊆ (H v).val := by
    intro r hr
    exact (WinnerSet.mem_reset _ _ _).mpr (Or.inl hr)
  have hHF (v) : (H v).val ⊆ (F v).val := by
    intro r hr
    exact ((WinnerSet.mem_reset _ _ _).mp hr).elim (fun h => hGF v h) (fun h => h.2)
  have hGQ : G.eval (SixValuation.namedValues three 0) =
      SixPatch.namedImage three
        (WinnerSet.StatusModel.Value.union (WinnerSet.StatusModel.Value.singleton 1)
          (WinnerSet.StatusModel.Value.singleton 2)) := by
    change (SixPatch.candidateTerm three 0).eval
      (fun j => SixPatch.namedImage three (SixValuation.values 0 j)) = _
    rw [SixPatch.candidate_eval_named]
    congr 1
  have hGQamb : (G.eval (SixValuation.namedValues three 0)).Ambiguous := by
    rw [hGQ]
    intro r he
    have hb : three 1 ∈ (SixPatch.namedImage three
        (WinnerSet.StatusModel.Value.union (WinnerSet.StatusModel.Value.singleton 1)
          (WinnerSet.StatusModel.Value.singleton 2))).val := by
      simp [SixPatch.namedImage, WinnerSet.StatusModel.expand,
        WinnerSet.StatusModel.Value.toWinner, WinnerSet.StatusModel.Value.union,
        WinnerSet.StatusModel.Value.singleton]
    have hc : three 2 ∈ (SixPatch.namedImage three
        (WinnerSet.StatusModel.Value.union (WinnerSet.StatusModel.Value.singleton 1)
          (WinnerSet.StatusModel.Value.singleton 2))).val := by
      simp [SixPatch.namedImage, WinnerSet.StatusModel.expand,
        WinnerSet.StatusModel.Value.toWinner, WinnerSet.StatusModel.Value.union,
        WinnerSet.StatusModel.Value.singleton]
    have hbr : three 1 = r := by simpa [he] using hb
    have hcr : three 2 = r := by simpa [he] using hc
    exact three.injective.ne (by decide : (1 : Fin 3) ≠ 2) (hbr.trans hcr.symm)
  have hnot : ¬∃ u : Term Role (Fin 5), u.IsCore ∧ ∀ v, u.eval v = H v := by
    rintro ⟨u, hu, he⟩
    have hQ : three 0 ∈ (u.eval (SixValuation.namedValues three 0)).val := by
      rw [he]
      change three 0 ∈ ((F _).reset (G.eval _)).val
      rw [WinnerSet.reset_of_ambiguous _ _ hGQamb]
      apply Or.inl
      dsimp [F]
      rw [SixPatch.counterexample_critical]
      simp [SixPatch.namedImage, SixPatch.expected, WinnerSet.StatusModel.expand,
        WinnerSet.StatusModel.Value.toWinner, WinnerSet.StatusModel.Value.union,
        WinnerSet.StatusModel.Value.singleton]
    have hout := SixValuation.persistence three id u hu hQ
    rcases hout with h | h | h | h | h
    all_goals
      have hh := hHF _ (by simpa only [← he] using h)
      simp [F, id_eq, SixPatch.counterexample_critical, SixPatch.namedImage,
        SixPatch.expected, WinnerSet.StatusModel.Value.toWinner,
        WinnerSet.StatusModel.Value.union, WinnerSet.StatusModel.Value.singleton] at hh
  obtain ⟨E, hE, hEp, _, hmax⟩ := exists_profile_maximum three G hG
  have hprov (v : Fin 5 → WinnerSet Role) : (H v).val ⊆ ⋃ j, (v j).val := by
    obtain ⟨u, hu, he⟩ := hloc (fun _ => v)
    rw [← he 0]
    exact hu.eval_subset_of_support v _ (fun j _ r hr => Set.mem_iUnion.mpr ⟨j, hr⟩)
  exact ⟨G, E, H, hG, hE, hloc,
    (locallyInterpolable_iff_preservesInvariants _ _).mp hloc,
    fun v r => (hEp v r).symm, hprofile,
    fun v => ⟨hlow v, hmax _ hprov hprofile v⟩, hnot⟩

end KFOL.Core
