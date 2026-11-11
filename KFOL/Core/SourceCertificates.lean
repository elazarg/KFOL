module

public import KFOL.Core.OwnerEliminationComplete
public import KFOL.Core.SourceNormalForm

/-! # Intrinsic certificates on canonical source probes

Source-probe reconstruction and checked membership clauses characterize core
operations. For canonical guard families the same clause criterion applies to
raw set semantics: it forces nonempty probe values and yields a realizing term.
The criterion permits auxiliary clauses and does not assert a short guard law.
-/

@[expose] public section

namespace KFOL.Core.OwnerElimination
open WinnerSet
universe u
variable {Role : Type u} [DecidableEq Role] [Fintype Role]

theorem source_probes_iff_checked_clauses {Var : Type*} [Fintype Var] [DecidableEq Var]
    (three : Fin 3 ↪ Role) (f : (Var → WinnerSet Role) → WinnerSet Role) :
    (∃ t : Term Role Var, t.IsCore ∧ ∀ v, t.eval v = f v) ↔
      (∀ v, Sources.meaning (Sources.normalForm three f) v = (f v).val) ∧
      (∀ (F : Finset (Clause (Sources.ProbeIndex Role Var) Role))
        (orders : Clause (Sources.ProbeIndex Role Var) Role → Role →
          List (Atom (Sources.ProbeIndex Role Var) Role)),
        checkFamily F orders = true →
        (∀ j, Satisfies F (fun q => Sources.probe three q.1 q.2.1 q.2.2 j)) →
        Satisfies F (fun q => f (Sources.probe three q.1 q.2.1 q.2.2))) := by
  classical
  constructor
  · rintro ⟨t, ht, he⟩
    have hfe : f = fun v => t.eval v := (funext he).symm
    refine ⟨?_, ?_⟩
    · intro v
      rw [hfe]
      exact Sources.normalForm_correct three t ht v
    · apply (finite_sample_iff_checked_clauses three
        (fun q : Sources.ProbeIndex Role Var => Sources.probe three q.1 q.2.1 q.2.2)
        (fun q => f (Sources.probe three q.1 q.2.1 q.2.2))).mp
      exact ⟨t, ht, fun q => he _⟩
  · rintro ⟨hreconstruct, htests⟩
    obtain ⟨t, ht, he⟩ := (finite_sample_iff_checked_clauses three
      (fun q : Sources.ProbeIndex Role Var => Sources.probe three q.1 q.2.1 q.2.2)
      (fun q => f (Sources.probe three q.1 q.2.1 q.2.2))).mpr htests
    have hnf : Sources.normalForm three (fun v => t.eval v) = Sources.normalForm three f := by
      funext k j
      apply Finset.ext
      intro g
      simp only [Sources.mem_normalForm]
      have hp : (fun p => k ∈ (t.eval (Sources.probe three k j p)).val) =
          (fun p => k ∈ (f (Sources.probe three k j p)).val) := by
        funext p
        rw [he ⟨k,j,p⟩]
      rw [hp]
    refine ⟨t, ht, fun v => ?_⟩
    apply Subtype.ext
    rw [← Sources.normalForm_correct three t ht v, hnf, hreconstruct v]



end KFOL.Core.OwnerElimination

namespace KFOL.Core.Sources
open WinnerSet OwnerElimination
variable {Role Var : Type*}

theorem guard_table_iff_checked_clauses [Fintype Role] [DecidableEq Role]
    [Fintype Var] [DecidableEq Var] (three : Fin 3 ↪ Role)
    (G : ∀ (k : Role) (j : Var), Finset (Guard k j)) :
    (∃ t : Term Role Var, t.IsCore ∧ normalForm three (fun v => t.eval v) = G) ↔
      Canonical G ∧
      (∀ (F : Finset (Clause (ProbeIndex Role Var) Role))
        (orders : Clause (ProbeIndex Role Var) Role → Role →
          List (Atom (ProbeIndex Role Var) Role)),
        checkFamily F orders = true →
        (∀ j, Satisfies F (fun q => probe three q.1 q.2.1 q.2.2 j)) →
        SatisfiesSets F (fun q => meaning G (probe three q.1 q.2.1 q.2.2))) := by
  classical
  constructor
  · rintro ⟨t, ht, hnf⟩
    refine ⟨?_, ?_⟩
    · rw [← hnf]
      intro k j g
      rw [mem_normalForm]
      have hp : coefficients (normalForm three (fun v => t.eval v)) k j =
          (fun p => k ∈ (t.eval (probe three k j p)).val) := by
        funext p
        exact propext (coefficient_iff_guard three t k j p).symm
      rw [hp]
    · apply (finite_sample_sets_iff_checked_clauses three
        (fun q : ProbeIndex Role Var => probe three q.1 q.2.1 q.2.2)
        (fun q => meaning G (probe three q.1 q.2.1 q.2.2))).mp
      refine ⟨t, ht, fun q => ?_⟩
      rw [← hnf]
      exact (normalForm_correct three t ht _).symm
  · rintro ⟨hcanonical, htests⟩
    obtain ⟨t, ht, he⟩ := (finite_sample_sets_iff_checked_clauses three
      (fun q : ProbeIndex Role Var => probe three q.1 q.2.1 q.2.2)
      (fun q => meaning G (probe three q.1 q.2.1 q.2.2))).mpr htests
    refine ⟨t, ht, ?_⟩
    funext k j
    apply Finset.ext
    intro g
    rw [mem_normalForm, hcanonical k j g]
    have hp : (fun p => k ∈ (t.eval (probe three k j p)).val) = coefficients G k j := by
      funext p
      apply propext
      rw [he ⟨k,j,p⟩]
      exact mem_meaning_probe_iff three G k j p
    rw [hp]

end KFOL.Core.Sources

namespace KFOL.Core.Sources

open OwnerElimination

/-- A canonical family is realizable exactly when its probe table satisfies
all clauses with a checked proof from the projection columns. -/
theorem guard_table_iff_certified_clauses {Role Var : Type*}
    [Fintype Role] [DecidableEq Role] [Fintype Var] [DecidableEq Var]
    (three : Fin 3 ↪ Role)
    (G : ∀ (k : Role) (j : Var), Finset (Guard k j)) :
    (∃ t : Term Role Var, t.IsCore ∧ normalForm three (fun v => t.eval v) = G) ↔
      Canonical G ∧ ∀ C : Clause (ProbeIndex Role Var) Role,
        Certifies (fun j q => probeAt three q j) C →
          C.HoldsSets (fun q => meaning G (probeAt three q)) := by
  rw [guard_table_iff_checked_clauses]
  apply and_congr_right
  intro _
  constructor
  · rintro h C ⟨F, orders, hC, ho, hc⟩
    exact h F orders ho hc C hC
  · intro h F orders ho hc C hC
    exact h C ⟨F, orders, hC, ho, hc⟩

end KFOL.Core.Sources
