import KFOL.Core.SourceCertificates
import KFOL.Algebra.SemilatticeTrace

open KFOL Core Core.OwnerElimination Core.Sources WinnerSet

namespace CoreOwnerCertificatesTests

-- Raw-set targets must really be nonempty. This uses semantic completeness,
-- rather than a special case of the Boolean checker.
example (values : Fin 1 → Fin 1 → WinnerSet (Fin 3)) :
    ¬ (∀ (F : Finset (Clause (Fin 1) (Fin 3)))
      (orders : Clause (Fin 1) (Fin 3) → Fin 3 → List (Atom (Fin 1) (Fin 3))),
      checkFamily F orders = true →
      (∀ j, Satisfies F (fun i => values i j)) →
      SatisfiesSets F (fun _ => ∅)) := by
  intro h
  obtain ⟨t, _, he⟩ := (finite_sample_sets_iff_checked_clauses
    (Function.Embedding.refl (Fin 3)) values (fun _ => ∅)).mpr h
  have hn := (t.eval (values 0)).property
  rw [he 0] at hn
  exact Set.not_nonempty_empty hn

private def emptyGuards (Var : Type*) : ∀ (k : Fin 3) (j : Var), Finset (Guard k j) :=
  fun _ _ => ∅

private theorem emptyGuards_canonical (Var : Type*) : Canonical (emptyGuards Var) := by
  intro k j g
  constructor
  · intro h
    simp [emptyGuards] at h
  · intro h
    have hf := h.1 (fun _ => .neutral) (by intro a ha; simp)
    simp [coefficients, emptyGuards] at hf

-- Empty guards do not accidentally acquire realizability from the clause
-- criterion: reconstruction would force an actual winner set to be empty.
example :
    ¬ (∀ C : Clause (ProbeIndex (Fin 3) (Fin 1)) (Fin 3),
        Certifies (fun j q => probeAt (Function.Embedding.refl _) q j) C →
        C.HoldsSets (fun q => meaning (emptyGuards (Fin 1))
          (probeAt (Function.Embedding.refl _) q))) := by
  intro h
  obtain ⟨t, ht, he⟩ :=
    (guard_table_iff_certified_clauses (Function.Embedding.refl _)
      (emptyGuards (Fin 1))).mpr ⟨emptyGuards_canonical _, h⟩
  let v : Fin 1 → WinnerSet (Fin 3) := fun _ => singleton 0
  have hc := normalForm_correct (Function.Embedding.refl _) t ht v
  rw [he] at hc
  have hn := (t.eval v).property
  rw [← hc] at hn
  simp [meaning, emptyGuards] at hn

-- The nullary boundary cannot become vacuously realizable. There is no
-- constant-free core term on zero input variables.
example :
    ¬ (∀ C : Clause (ProbeIndex (Fin 3) (Fin 0)) (Fin 3),
        Certifies (fun j q => probeAt (Function.Embedding.refl _) q j) C →
        C.HoldsSets (fun q => meaning (emptyGuards (Fin 0))
          (probeAt (Function.Embedding.refl _) q))) := by
  intro h
  obtain ⟨t, ht, _⟩ :=
    (guard_table_iff_certified_clauses (Function.Embedding.refl _)
      (emptyGuards (Fin 0))).mpr ⟨emptyGuards_canonical _, h⟩
  obtain ⟨j, _⟩ := ht.vars_nonempty
  exact Fin.elim0 j

private def transfer : Clause (Fin 2) (Fin 3) := ⟨some (1, 0), {(0, 0)}⟩
private def left : Fin 2 → WinnerSet (Fin 3) := ![singleton 0, singleton 0]
private def right : Fin 2 → WinnerSet (Fin 3) := ![singleton 1, singleton 2]

private theorem left_satisfies : Satisfies {transfer} left := by
  simp [Satisfies, transfer, Clause.Holds, Clause.Premise, Clause.Head, left]

private theorem right_satisfies : Satisfies {transfer} right := by
  simp [Satisfies, transfer, Clause.Holds, Clause.Premise, Clause.Head, right]

private theorem choice_fails : ¬ transfer.Holds (fun i => choice 1 (left i) (right i)) := by
  simp [transfer, Clause.Holds, Clause.Premise, Clause.Head, left, right,
    choice, singleton_inj]

-- Both input tuples satisfy the proposed implication, but owned choice at b
-- turns them into (b,ac), violating it. Soundness therefore excludes EVERY
-- proposed owner order; this does not enumerate or unfold the checker.
example (orders : Clause (Fin 2) (Fin 3) → Fin 3 → List (Atom (Fin 2) (Fin 3))) :
    checkFamily {transfer} orders = false := by
  cases hc : checkFamily {transfer} orders with
  | false => rfl
  | true =>
    exfalso
    have hh := choice_preserves hc left_satisfies right_satisfies (1 : Fin 3)
    exact choice_fails (hh transfer (Finset.mem_singleton_self _))

end CoreOwnerCertificatesTests
