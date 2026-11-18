module

public import KFOL.Core.AtomicInterpolation
public import KFOL.Core.CompletionDepth

/-! # Interpolation by one greatest completion gate

The children are fixed columns. The gate must meet the designated singleton
demands and retain one optional winner at the observed rows.
-/

@[expose] public section
namespace KFOL.Core.CompletionDepth
open Interpolation
universe u v
variable {Role : Type u} [Fintype Role] {Row : Type v} {n : ℕ}
attribute [local instance] Equational.coreStructure

/-- The generators selected from the desired positive profile tests define
one completion gate on the same ports. Rainbow witnesses ensure
admissibility and gap witnesses separate the negative tests. -/
theorem exists_gate_with_profiles {Var : Type*} (three : Fin 3 ↪ Role)
    (F : Role → (Var → Bool) → Bool)
    (port : Fin (n + 1) → Role → (Var → Bool) → Bool)
    (top : ∀ r, F r (fun _ => true) = true)
    (rainbow : ∀ A : Role → Var → Bool, (∀ r, F r (A r) = true) →
      ∃ j, ∀ r, port j r (A r) = true)
    (gap : ∀ r A B, F r A = true → F r B = false →
      ∃ j, port j r A = true ∧ port j r B = false) :
    ∃ g : Gate Role n, ∀ r A, g.profiles r (fun j => port j r A) = F r A := by
  classical
  let P (r : Role) (S : Fin (n + 1) → Bool) : Bool :=
    decide (∃ A, F r A = true ∧ ∀ j, port j r A = true → S j = true)
  have mem (r) (S) : P r S = true ↔
      ∃ A, F r A = true ∧ ∀ j, port j r A = true → S j = true := by
    simp only [P, decide_eq_true_eq]
  have admissible : AdmissibleProfiles P := by
    refine ⟨?_, fun r => (mem r _).mpr ⟨_, top r, fun _ _ => rfl⟩, ?_⟩
    · intro r S T sub hS
      obtain ⟨A, ha, hs⟩ := (mem r S).mp hS
      exact (mem r T).mpr ⟨A, ha, fun j hj => sub j (hs j hj)⟩
    · intro S wins
      choose A hA sub using fun r => (mem r (S r)).mp (wins r)
      obtain ⟨j, hj⟩ := rainbow A hA
      exact ⟨j, fun r => sub r j (hj r)⟩
  obtain ⟨g, hg⟩ := Gate.exists_of_admissible three P admissible
  refine ⟨g, fun r B => ?_⟩
  rw [hg]
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro pos
    obtain ⟨A, ha, sub⟩ := (mem r (fun j => port j r B)).mp pos
    by_contra no
    have hb : F r B = false := Bool.eq_false_iff.mpr no
    obtain ⟨j, hj, hnot⟩ := gap r A B ha hb
    exact Bool.noConfusion ((sub j hj).symm.trans hnot)
  · intro hb
    exact (mem r (fun j => port j r B)).mpr ⟨B, hb, fun _ => id⟩

omit [Fintype Role] in
/-- Once the prescribed profiles are attained, the same gate can supply
all requested winners at non-atomic outputs. Each such request only
needs a witness in one port. -/
theorem Gate.winners_of_profiles {Var : Type*} {Query : Type*} (g : Gate Role n)
    (F : Role → (Var → Bool) → Bool)
    (port : Fin (n + 1) → Role → (Var → Bool) → Bool)
    (values : Query → Var → WinnerSet Role) (winner : Query → Role)
    (args : Query → Fin (n + 1) → WinnerSet Role)
    (profile_eq : ∀ r A, g.profiles r (fun j => port j r A) = F r A)
    (atomic_eq : ∀ q r j, ProfileBounds.atomicBits r (args q) j =
      port j r (ProfileBounds.atomicBits r (values q)))
    (ambiguous : ∀ q r, F r (ProfileBounds.atomicBits r (values q)) = false)
    (witness : ∀ q, ∃ j, winner q ∈ (args q j).val) :
    ∀ q, winner q ∈ (g.eval (args q)).val := by
  intro q
  have no : (g.eval (args q)).Ambiguous := by
    intro r atom
    have h := (g.singleton_iff (args q) r).mp atom
    rw [funext (atomic_eq q r), profile_eq, ambiguous] at h
    exact Bool.noConfusion h
  rw [g.union_of_ambiguous _ no]
  exact Set.mem_iUnion.mpr (witness q)

/-- A single completion gate meets the atomic demands and the optional
positive query precisely under the profile test on its input columns. -/
theorem exists_gate_iff_profileCondition (three : Fin 3 ↪ Role)
    (values : Row → Fin (n + 1) → WinnerSet Role) (D : Finset (Row × Role))
    (p : Option (Row × Role)) :
    (∃ g : Gate Role n, Atomic D (fun i => g.eval (values i)) ∧
      Positive p (fun i => g.eval (values i))) ↔
    ProfileCondition (fun E o => ∃ j, Atomic E (fun i => values i j) ∧
      Positive o (fun i => values i j)) D p := by
  classical
  rw [← atomic_positive_iff three values D p]
  constructor
  · rintro ⟨g, hD, hp⟩
    obtain ⟨t, ht⟩ := g.exists_core three
    have hrows : (fun i => (Equational.Core.decode t).eval (values i)) =
        fun i => g.eval (values i) := funext fun i =>
      (Equational.Core.eval_decode t (values i)).trans (ht (values i))
    exact ⟨_, Equational.Core.isCore_decode t, hrows.symm ▸ hD, hrows.symm ▸ hp⟩
  · rintro ⟨t, ht, hD, hp⟩
    let e := Equational.Core.encode t ht
    obtain ⟨g, hg⟩ := Gate.exists_of_admissible three _ (admissibleProfiles_profile e)
    have hs (v : Fin (n + 1) → WinnerSet Role) (r : Role) :
        g.eval v = WinnerSet.singleton r ↔ t.eval v = WinnerSet.singleton r := by
      rw [g.singleton_iff, hg]
      have h := winnerSet_eq_singleton_iff_profile e r v
      rw [← Equational.Core.eval_decode, Equational.Core.decode_encode] at h
      exact h.symm
    refine ⟨g, fun d hd => (hs _ _).2 (hD d hd), ?_⟩
    cases p with
    | none => trivial
    | some query =>
      exact g.greatest t.eval
        (fun v => ht.eval_subset_of_support v _ (fun j _ _ hj => Set.mem_iUnion.mpr ⟨j, hj⟩))
        (fun v r => (hs v r).1) (values query.1) hp

end KFOL.Core.CompletionDepth
