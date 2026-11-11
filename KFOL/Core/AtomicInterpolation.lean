module

public import KFOL.Definitions.CoreInterpolation
public import KFOL.Core.ProfileEnvelope
public import KFOL.Equational.Native
public import KFOL.Algebra.ChoiceSupport

/-! # Atomic demands and one possible winner

Singleton profiles turn simultaneous atomic demands into a rainbow
common-source test. Their greatest completion retains a requested winner
exactly when provenance and every forced competing atom permit it.
-/

@[expose] public section

namespace KFOL.Core.Interpolation
open WinnerSet
universe u v w
variable {Role : Type u} {Row : Type v} {Gen : Type w}
variable [DecidableEq Role] [DecidableEq Row] [Fintype Role] [Fintype Gen]

omit [Fintype Role] [Fintype Gen] in
private theorem singleton_iff_profile (t : Term Role Gen) (ht : t.IsCore)
    (v : Gen → WinnerSet Role) (r : Role) :
    t.eval v = WinnerSet.singleton r ↔
      profile r (fun g => decide (v g = WinnerSet.singleton r)) (Equational.Core.encode t ht) = true := by
  classical
  have h := winnerSet_eq_singleton_iff_profile (Equational.Core.encode t ht) r v
  simpa only [← Equational.Core.eval_decode, Equational.Core.decode_encode] using h

private noncomputable def leastProfiles (values : Row → Gen → WinnerSet Role)
    (D : Finset (Row × Role)) (r : Role) (v : Gen → Bool) : Bool := by
  classical
  exact decide ((∀ g, v g = true) ∨ ∃ d ∈ D, d.2 = r ∧
    ∀ g, values d.1 g = WinnerSet.singleton r → v g = true)

omit [Fintype Role] in
private theorem leastProfiles_admissible (values : Row → Gen → WinnerSet Role)
    (D : Finset (Row × Role))
    (h : ∀ S, S ⊆ D → Rainbow S → ∃ g, Atomic S (fun i => values i g)) :
    AdmissibleProfiles (leastProfiles values D) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro r v w hvw hv
    simp only [leastProfiles, decide_eq_true_eq] at hv ⊢
    rcases hv with ht | ⟨d, hd, hdr, hsub⟩
    · exact Or.inl (fun g => hvw g (ht g))
    · exact Or.inr ⟨d, hd, hdr, fun g hg => hvw g (hsub g hg)⟩
  · intro r
    simp only [leastProfiles, decide_eq_true_eq]
    exact Or.inl (fun _ => trivial)
  · intro v hv
    let sel (r : Role) : Option (Row × Role) :=
      if h : ∃ d ∈ D, d.2 = r ∧ ∀ g, values d.1 g = WinnerSet.singleton r → v r g = true
      then some h.choose else none
    have selected (r : Role) (d : Row × Role) (hd : sel r = some d) :
        d ∈ D ∧ d.2 = r ∧ ∀ g, values d.1 g = WinnerSet.singleton r → v r g = true := by
      dsimp [sel] at hd
      split_ifs at hd with hh
      · have he := Option.some.inj hd
        subst d
        exact hh.choose_spec
    let S := D.filter (fun d => sel d.2 = some d)
    have hS : S ⊆ D := Finset.filter_subset _ _
    have hrain : Rainbow S := by
      intro d hd e he hde
      have hd' := (Finset.mem_filter.mp hd).2
      have he' := (Finset.mem_filter.mp he).2
      exact Option.some.inj (hd'.symm.trans (hde ▸ he'))
    obtain ⟨g, hg⟩ := h S hS hrain
    refine ⟨g, fun r => ?_⟩
    cases hs : sel r with
    | none =>
      have hn : ¬∃ d ∈ D, d.2 = r ∧
          ∀ g, values d.1 g = WinnerSet.singleton r → v r g = true := by
        intro hh
        simp only [sel, dite_eq_left hh] at hs
        cases hs
      have hv' : (∀ g, v r g = true) ∨ ∃ d ∈ D, d.2 = r ∧
          ∀ g, values d.1 g = WinnerSet.singleton r → v r g = true := by
        simpa only [leastProfiles, decide_eq_true_eq] using hv r
      exact hv'.elim (fun ht => ht g) (fun hh => (hn hh).elim)
    | some d =>
      obtain ⟨hd, hdr, hsub⟩ := selected r d hs
      have hdS : d ∈ S := Finset.mem_filter.mpr ⟨hd, by simpa [hdr] using hs⟩
      exact hsub g (by simpa [hdr] using hg d hdS)


private theorem exists_least_profile_term (three : Fin 3 ↪ Role)
    (values : Row → Gen → WinnerSet Role) (D : Finset (Row × Role))
    (h : ∀ S, S ⊆ D → Rainbow S → ∃ g, Atomic S (fun i => values i g)) :
    ∃ t : Term Role Gen, t.IsCore ∧ ∀ (v : Gen → WinnerSet Role) r,
      t.eval v = WinnerSet.singleton r ↔
        (∀ g, v g = WinnerSet.singleton r) ∨ ∃ d ∈ D, d.2 = r ∧
          ∀ g, values d.1 g = WinnerSet.singleton r → v g = WinnerSet.singleton r := by
  classical
  obtain ⟨t, ht⟩ := (exists_term_iff_admissibleProfiles three (leastProfiles values D)).mpr
    (leastProfiles_admissible values D h)
  refine ⟨Equational.Core.decode t, Equational.Core.isCore_decode t, fun v r => ?_⟩
  rw [Equational.Core.eval_decode]
  rw [winnerSet_eq_singleton_iff_profile, ht]
  simp only [leastProfiles, decide_eq_true_eq]

omit [DecidableEq Row] [Fintype Role] [Fintype Gen] in
private theorem atomic_rainbow_necessary (t : Term Role Gen) (ht : t.IsCore)
    (values : Row → Gen → WinnerSet Role) (D : Finset (Row × Role))
    (hD : Atomic D (fun i => t.eval (values i))) :
    ∀ S, S ⊆ D → Rainbow S → ∃ g, Atomic S (fun i => values i g) := by
  classical
  intro S hSD hrain
  let owners : S → Role := fun d => d.val.2
  have hinj : Function.Injective owners := by
    intro d e he
    exact Subtype.ext (hrain d.property e.property he)
  have hp (d : S) : profile (owners d)
      (fun g => decide (values d.val.1 g = WinnerSet.singleton (owners d)))
      (Equational.Core.encode t ht) = true :=
    (singleton_iff_profile t ht _ _).mp (hD d.val (hSD d.property))
  obtain ⟨g, hg⟩ := profile_common_source owners hinj _ (Equational.Core.encode t ht) hp
  refine ⟨g, fun d hd => ?_⟩
  exact of_decide_eq_true (hg ⟨d,hd⟩)

omit [DecidableEq Row] [Fintype Role] in
private theorem atomic_positive_necessary (t : Term Role Gen) (ht : t.IsCore)
    (values : Row → Gen → WinnerSet Role) (D : Finset (Row × Role))
    (hD : Atomic D (fun i => t.eval (values i))) (q : Row) (k : Role)
    (hk : k ∈ (t.eval (values q)).val) :
    (∃ g, k ∈ (values q g).val) ∧
      ∀ d ∈ D, d.2 ≠ k → ∃ s, s ≠ d.2 ∧ ∃ g,
        Atomic {d} (fun i => values i g) ∧ Positive (some (q,s)) (fun i => values i g) := by
  classical
  have hprov := ht.eval_subset_of_support (values q) (⋃ g, (values q g).val)
    (fun g _ r hr => Set.mem_iUnion.mpr ⟨g,hr⟩) hk
  refine ⟨Set.mem_iUnion.mp hprov, fun d hd hdk => ?_⟩
  have hw : ∃ g, values d.1 g = WinnerSet.singleton d.2 ∧
      values q g ≠ WinnerSet.singleton d.2 := by
    by_contra hn
    push Not at hn
    have hp := (singleton_iff_profile t ht _ _).mp (hD d hd)
    have hq := profile_mono d.2 _ _ (fun g hg =>
      decide_eq_true (hn g (of_decide_eq_true hg))) (Equational.Core.encode t ht) hp
    have he := (singleton_iff_profile t ht (values q) d.2).mpr hq
    have hkr : k = d.2 := by simpa [he] using hk
    exact hdk hkr.symm
  obtain ⟨g, hgd, hgq⟩ := hw
  obtain ⟨s, hs, hsr⟩ := exists_mem_ne_of_ne_singleton d.2 (values q g) hgq
  refine ⟨s, hsr, g, ?_, hs⟩
  intro e he
  simpa only [Finset.mem_singleton.mp he] using hgd


private theorem atomic_positive_sufficient (three : Fin 3 ↪ Role)
    (values : Row → Gen → WinnerSet Role) (D : Finset (Row × Role))
    (p : Option (Row × Role))
    (h : ProfileCondition (fun E o => ∃ g,
      Atomic E (fun i => values i g) ∧ Positive o (fun i => values i g)) D p) :
    ∃ t : Term Role Gen, t.IsCore ∧ Atomic D (fun i => t.eval (values i)) ∧
      Positive p (fun i => t.eval (values i)) := by
  classical
  have hrain : ∀ S, S ⊆ D → Rainbow S → ∃ g, Atomic S (fun i => values i g) := by
    intro S hSD hS
    obtain ⟨g, hg, _⟩ := h.1 S hSD hS
    exact ⟨g,hg⟩
  obtain ⟨t, ht, hprofiles⟩ := exists_least_profile_term three values D hrain
  have hD : Atomic D (fun i => t.eval (values i)) := by
    intro d hd
    apply (hprofiles (values d.1) d.2).mpr
    exact Or.inr ⟨d, hd, rfl, fun _ h => h⟩
  obtain ⟨e, he, hep, heamb, _⟩ := exists_profile_maximum three t ht
  refine ⟨e, he, fun d hd => (hep (values d.1) d.2).mpr (hD d hd), ?_⟩
  cases hp : p with
  | none => trivial
  | some qk =>
    obtain ⟨q,k⟩ := qk
    have hpos : (∃ g, Atomic ∅ (fun i => values i g) ∧
        Positive (some (q,k)) (fun i => values i g)) ∧
        ∀ d ∈ D, d.2 ≠ k → ∃ s, s ≠ d.2 ∧ ∃ g,
          Atomic {d} (fun i => values i g) ∧ Positive (some (q,s)) (fun i => values i g) := by
      simpa only [ProfileCondition, hp] using h.2
    obtain ⟨g, _, hg⟩ := hpos.1
    have hno (r : Role) (hrk : r ≠ k) : t.eval (values q) ≠ WinnerSet.singleton r := by
      intro heq
      rcases (hprofiles (values q) r).mp heq with hall | ⟨d, hd, hdr, hsub⟩
      · have hkr : k = r := by simpa [Positive, hall g] using hg
        exact hrk hkr.symm
      · obtain ⟨s, hsr, g', hgd, hgs⟩ := hpos.2 d hd (hdr ▸ hrk)
        have hval := hsub g' (by simpa only [hdr] using hgd d (Finset.mem_singleton_self _))
        have hsr' : s = r := by simpa [Positive, hval] using hgs
        exact hsr (hsr'.trans hdr.symm)
    change k ∈ (e.eval (values q)).val
    by_cases hamb : (t.eval (values q)).Ambiguous
    · rw [heamb (values q) hamb]
      exact Set.mem_iUnion.mpr ⟨g,hg⟩
    · obtain ⟨r, hr⟩ : ∃ r, t.eval (values q) = WinnerSet.singleton r := by
        simpa only [WinnerSet.Ambiguous, not_forall, not_not] using hamb
      have hrk : r = k := by
        by_contra hn
        exact hno r hn hr
      rw [(hep (values q) r).mpr hr, hrk]
      exact Set.mem_singleton k

/-- Atomic output requirements and one optional possible winner have a direct
rainbow/profile test on the given generators. The generator type may be empty. -/
theorem atomic_positive_iff (three : Fin 3 ↪ Role)
    (values : Row → Gen → WinnerSet Role) (D : Finset (Row × Role))
    (p : Option (Row × Role)) :
    (∃ t : Term Role Gen, t.IsCore ∧ Atomic D (fun i => t.eval (values i)) ∧
      Positive p (fun i => t.eval (values i))) ↔
    ProfileCondition (fun E o => ∃ g,
      Atomic E (fun i => values i g) ∧ Positive o (fun i => values i g)) D p := by
  classical
  constructor
  · rintro ⟨t, ht, hD, hp⟩
    refine ⟨?_, ?_⟩
    · intro S hSD hS
      obtain ⟨g,hg⟩ := atomic_rainbow_necessary t ht values D hD S hSD hS
      exact ⟨g,hg,trivial⟩
    · cases hopt : p with
      | none => trivial
      | some qk =>
        obtain ⟨q,k⟩ := qk
        have hk : k ∈ (t.eval (values q)).val := by simpa [Positive, hopt] using hp
        obtain ⟨hprov,hother⟩ := atomic_positive_necessary t ht values D hD q k hk
        refine ⟨?_, hother⟩
        obtain ⟨g,hg⟩ := hprov
        exact ⟨g, by intro d hd; exact (Finset.notMem_empty _ hd).elim, hg⟩
  · exact atomic_positive_sufficient three values D p

end KFOL.Core.Interpolation
