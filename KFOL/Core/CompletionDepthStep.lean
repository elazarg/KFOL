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
