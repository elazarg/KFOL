module

public import KFOL.Core.Peeling
public import KFOL.Core.SourceNormalForm

/-! # A hereditary characterization of canonical source guards

The direct row-deletion test is applied to the canonical source probes. Its
inputs are computed from the guard table, with no auxiliary clauses or graph.
-/

@[expose] public section
namespace KFOL.Core.Sources
open WinnerSet
universe u v
variable {Role : Type u} {Var : Type v}

/-- Canonical guards are jointly realizable exactly when their own raw probe
values satisfy the direct hereditary interpolation condition. -/
theorem guard_table_iff_peels [Fintype Role] [DecidableEq Role]
    [Fintype Var] [DecidableEq Var] (three : Fin 3 ↪ Role)
    (G : ∀ (k : Role) (j : Var), Finset (Guard k j)) :
    (∃ t : Term Role Var, t.IsCore ∧ normalForm three (fun v => t.eval v) = G) ↔
      Canonical G ∧ Interpolation.Recognizes
        (fun q : ProbeIndex Role Var => probeAt three q)
        (fun q => meaning G (probeAt three q)) := by
  classical
  rw [Interpolation.recognizes_iff three]
  constructor
  · rintro ⟨t, ht, hnf⟩
    have hc : Canonical G := by
      rw [← hnf]
      intro k j g
      rw [mem_normalForm]
      have hp : coefficients (normalForm three (fun v => t.eval v)) k j =
          (fun p => k ∈ (t.eval (probe three k j p)).val) := by
        funext p
        exact propext (coefficient_iff_guard three t k j p).symm
      rw [hp]
    refine ⟨hc, t, ht, fun q => ?_⟩
    rw [← hnf]
    exact (normalForm_correct three t ht _).symm
  · rintro ⟨hc, t, ht, he⟩
    refine ⟨t, ht, ?_⟩
    funext k j
    apply Finset.ext
    intro g
    rw [mem_normalForm, hc k j g]
    have hp : (fun p => k ∈ (t.eval (probe three k j p)).val) = coefficients G k j := by
      funext p
      apply propext
      have heq : (t.eval (probe three k j p)).val = meaning G (probe three k j p) := by
        simpa only [probeAt] using he ⟨k,j,p⟩
      rw [heq]
      exact mem_meaning_probe_iff three G k j p
    rw [hp]


private theorem join_positive_probes (three : Fin 3 ↪ Role)
    (N : Finset (ProbeIndex Role Var)) (base : Term Role Var) (hb : base.IsCore)
    (hbb : Interpolation.Bounded N exclusionBounds (fun q => base.eval (probeAt three q)))
    (P : Finset (ProbeIndex Role Var))
    (hw : ∀ q ∈ P, ∃ t : Term Role Var, t.IsCore ∧
      Interpolation.Bounded N exclusionBounds (fun q => t.eval (probeAt three q)) ∧
        q.1 ∈ (t.eval (probeAt three q)).val) :
    ∃ t : Term Role Var, t.IsCore ∧
      Interpolation.Bounded N exclusionBounds (fun q => t.eval (probeAt three q)) ∧
        ∀ q ∈ P, q.1 ∈ (t.eval (probeAt three q)).val := by
  classical
  let S := P.image (fun q => (q,q.1))
  have hw' (p : ProbeIndex Role Var × Role) (hp : p ∈ S) :
      ∃ t : Term Role Var, t.IsCore ∧
        Interpolation.Bounded N exclusionBounds (fun q => t.eval (probeAt three q)) ∧
          p.2 ∈ (t.eval (probeAt three p.1)).val := by
    obtain ⟨q,hq,he⟩ := Finset.mem_image.mp hp
    subst p
    exact hw q hq
  obtain ⟨t,ht,htb,htp⟩ := Interpolation.join_memberships three (fun q => probeAt three q)
    N exclusionBounds S ⟨base,hb,hbb⟩ hw'
  exact ⟨t,ht,htb,fun q hq => htp (q,q.1) (Finset.mem_image.mpr ⟨q,hq,rfl⟩)⟩

/-- Only negative observer bits need upper bounds. Separate witnesses for the
positive bits are joined without changing any negative observation. -/
theorem guard_table_iff_negative_peels [Fintype Role] [DecidableEq Role]
    [Fintype Var] [DecidableEq Var] (three : Fin 3 ↪ Role)
    (G : ∀ (k : Role) (j : Var), Finset (Guard k j)) :
    (∃ t : Term Role Var, t.IsCore ∧ normalForm three (fun v => t.eval v) = G) ↔
      Canonical G ∧
      Interpolation.Peels (fun q => probeAt three q) exclusionBounds (negativeProbes G) ∅ none ∧
      ∀ q : ProbeIndex Role Var, coefficients G q.1 q.2.1 q.2.2 →
        Interpolation.Peels (fun q => probeAt three q) exclusionBounds (negativeProbes G) ∅
          (some (q,q.1)) := by
  classical
  constructor
  · intro hreal
    obtain ⟨t,ht,hnf⟩ := hreal
    have hc := ((guard_table_iff_peels three G).mp ⟨t,ht,hnf⟩).1
    have hcoeff (q : ProbeIndex Role Var) :
        q.1 ∈ (t.eval (probeAt three q)).val ↔ coefficients G q.1 q.2.1 q.2.2 := by
      rw [← hnf]
      exact coefficient_iff_guard three t q.1 q.2.1 q.2.2
    have hb : Interpolation.Bounded (negativeProbes G) exclusionBounds
        (fun q => t.eval (probeAt three q)) := by
      intro q hq r hr
      have hn : ¬coefficients G q.1 q.2.1 q.2.2 := by
        simpa only [negativeProbes, Finset.mem_filter, Finset.mem_univ, true_and] using hq
      intro he
      exact hn ((hcoeff q).mp (he ▸ hr))
    refine ⟨hc, ?_, fun q hq => ?_⟩
    · apply (Interpolation.peels_iff three _ _ _ _ _).mpr
      exact ⟨t,ht,hb,by intro d hd; exact (Finset.notMem_empty _ hd).elim,trivial⟩
    · apply (Interpolation.peels_iff three _ _ _ _ _).mpr
      exact ⟨t,ht,hb,by intro d hd; exact (Finset.notMem_empty _ hd).elim,(hcoeff q).mpr hq⟩
  · rintro ⟨hc,hbase,hpositive⟩
    obtain ⟨base,hbc,hbb,_,_⟩ := (Interpolation.peels_iff three _ _ _ _ _).mp hbase
    let P : Finset (ProbeIndex Role Var) := Finset.univ.filter
      (fun q => coefficients G q.1 q.2.1 q.2.2)
    have hw (q : ProbeIndex Role Var) (hq : q ∈ P) :
        ∃ t : Term Role Var, t.IsCore ∧
          Interpolation.Bounded (negativeProbes G) exclusionBounds
            (fun q => t.eval (probeAt three q)) ∧ q.1 ∈ (t.eval (probeAt three q)).val := by
      have hcp := (Finset.mem_filter.mp hq).2
      obtain ⟨t,ht,hb,_,hp⟩ := (Interpolation.peels_iff three _ _ _ _ _).mp (hpositive q hcp)
      exact ⟨t,ht,hb,hp⟩
    obtain ⟨t,ht,hb,hm⟩ := join_positive_probes three _ base hbc hbb P hw
    have he (q : ProbeIndex Role Var) :
        q.1 ∈ (t.eval (probeAt three q)).val ↔ coefficients G q.1 q.2.1 q.2.2 := by
      constructor
      · intro hmem
        by_contra hn
        have hq : q ∈ negativeProbes G := by simp only [negativeProbes,
          Finset.mem_filter, Finset.mem_univ, true_and]; exact hn
        exact hb q hq hmem rfl
      · intro hcp
        exact hm q (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hcp⟩)
    refine ⟨t,ht,?_⟩
    funext k j
    apply Finset.ext
    intro g
    rw [mem_normalForm,hc k j g]
    have hp : (fun p => k ∈ (t.eval (probe three k j p)).val) = coefficients G k j := by
      funext p
      exact propext (he ⟨k,j,p⟩)
    rw [hp]

end KFOL.Core.Sources
