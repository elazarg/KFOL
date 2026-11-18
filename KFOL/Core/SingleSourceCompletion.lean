module

public import KFOL.Core.ProfileSourceFiber
public import KFOL.Core.SourceReciprocity

/-! # Complete coefficients at one source across all observers

The atom postings of a probe forget its observer. A predicate at one input
is realizable precisely when it is downward closed under inclusion of these
postings. Equal postings consequently give equal answers across observers.
-/

@[expose] public section

namespace KFOL.Core.SingleSourceCompletion

open Sources ProfileSourceFiber
open scoped Classical

universe u v
variable {Role : Type u} {Var : Type v} {j : Var}

/-- The passive input--owner pairs actually posted as atoms on this probe. -/
def postings (q : Observation Role j) : Set ({i : Var // i ≠ j} × Role) :=
  {a | ∃ r, q.2 a.1 = .atom r ∧ r.val = a.2}

/-- A single downward-closure condition includes agreement on equal partial
colorings seen by different observers. -/
def Downward (P : Observation Role j → Prop) : Prop :=
  ∀ p q, postings p ⊆ postings q → P q → P p

theorem supplies_downward (three : Fin 3 ↪ Role) (t : Term Role Var) (ht : t.IsCore) :
    Downward (Supplies three t j) := by
  intro p q inc hq
  by_contra hp
  have hp' := (probe_loss_iff_cofactor_independent three t ht p.1 j p.2).mp hp
  apply (show ¬Supplies three t j q from
    (probe_loss_iff_cofactor_independent three t ht q.1 j q.2).mpr ?_) hq
  intro v w away fixed
  apply hp' v w away
  intro i r hr
  have posted : (i, r.val) ∈ postings p := ⟨r, hr, rfl⟩
  obtain ⟨s, hs, he⟩ := inc posted
  exact (fixed i s hs).trans (congrArg WinnerSet.singleton he)

private theorem postings_subset_of_le {k : Role} {p q : Pattern k j} (h : p ≤ q) :
    postings ⟨k,q⟩ ⊆ postings ⟨k,p⟩ := by
  rintro ⟨i,r⟩ ⟨s, hs, rfl⟩
  change q i = .atom s at hs
  rcases h i with hn | he
  · simp [hs] at hn
  · exact ⟨s, he.trans hs, rfl⟩

/-- Downward closure across all observations is precisely antitonicity in the
postings on each observer facet and agreement on overlaps. In the existing
passive-status order, removing a posting increases a pattern. -/
theorem downward_iff_facets (P : Observation Role j → Prop) :
    Downward P ↔ (∀ k, Monotone (fun p : Pattern k j => P ⟨k,p⟩)) ∧
      ∀ p q, postings p = postings q → (P p ↔ P q) := by
  constructor
  · intro h
    exact ⟨fun k _ _ inc => h _ _ (postings_subset_of_le inc),
      fun p q eq => ⟨h q p eq.ge, h p q eq.le⟩⟩
  · rintro ⟨mono, overlap⟩ p q inc hq
    let restricted (i : {i : Var // i ≠ j}) : Passive q.1 :=
      match q.2 i with
      | .neutral => .neutral
      | .atom r => if (i, r.val) ∈ postings p then .atom r else .neutral
    have le : q.2 ≤ restricted := by
      intro i
      cases he : q.2 i with
      | neutral => exact Or.inl (by simp [restricted, he])
      | atom r =>
        by_cases hr : (i,r.val) ∈ postings p
        · exact Or.inr (by simp [restricted, he, hr])
        · exact Or.inl (by simp [restricted, he, hr])
    have eq : postings ⟨q.1,restricted⟩ = postings p := by
      ext a
      obtain ⟨i,r⟩ := a
      constructor
      · rintro ⟨s, hs, rfl⟩
        change restricted i = .atom s at hs
        cases he : q.2 i with
        | neutral => simp [restricted, he] at hs
        | atom t =>
          by_cases hr : (i,t.val) ∈ postings p
          · have es : t = s := by simpa [restricted, he, hr] using hs
            exact es ▸ hr
          · simp [restricted, he, hr] at hs
      · intro hr
        obtain ⟨s, hs, rfl⟩ := inc hr
        exact ⟨s, by simp [restricted, hs, hr], rfl⟩
    exact (overlap _ _ eq).mp (mono q.1 le hq)

private theorem posted_iff (three : Fin 3 ↪ Role) (q : Observation Role j)
    (i : {i : Var // i ≠ j}) (r : Role) :
    (i,r) ∈ postings q ↔ probe three q.1 j q.2 i.val = WinnerSet.singleton r := by
  rw [probe_other three q.1 j q.2 i.val i.property]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact (representative_atom_iff three q.1 _ s).mpr hs
  · intro h
    have hr : r ≠ q.1 := by
      rintro rfl
      exact representative_omits three q.1 (q.2 i) (h ▸ (Set.mem_singleton q.1))
    exact ⟨⟨r,hr⟩, (representative_atom_iff three q.1 _ ⟨r,hr⟩).mp h, rfl⟩

private theorem literal (three : Fin 3 ↪ Role) (r : Role) (i : {i : Var // i ≠ j})
    (q : Observation Role j) :
    Supplies three (.choice r (.var j) (.var i.val)) j q ↔ (i,r) ∉ postings q := by
  rw [posted_iff three]
  have hi : q.1 ∉ (probe three q.1 j q.2 i.val).val := by simp [i.property]
  simp only [Supplies, Term.eval, probe_source]
  by_cases he : r = q.1
  · subst r
    rw [WinnerSet.mem_choice_owner]
    have hn : probe three q.1 j q.2 i.val ≠ WinnerSet.singleton q.1 :=
      fun eq => hi (eq ▸ (Set.mem_singleton q.1))
    simp [hn]
  · rw [WinnerSet.mem_choice_other r q.1 he]
    simp [Ne.symm he]

private theorem exists_excluding (three : Fin 3 ↪ Role)
    (forbidden : Finset ({i : Var // i ≠ j} × Role)) :
    ∃ t : Term Role Var, t.IsCore ∧
      ∀ q, Supplies three t j q ↔ ∀ a ∈ forbidden, a ∉ postings q := by
  classical
  induction forbidden using Finset.induction_on with
  | empty => exact ⟨.var j, trivial, fun q => by simp [Supplies, Term.eval]⟩
  | insert a F _ ih =>
    obtain ⟨t, ht, hF⟩ := ih
    let lit : Term Role Var := .choice a.2 (.var j) (.var a.1.val)
    refine ⟨substituteAt t j lit, substituteAt_isCore ht (show lit.IsCore from ⟨trivial,trivial⟩) j, fun q => ?_⟩
    have meet := substituteAt_probe three ht lit q.1 j q.2
    change Supplies three (substituteAt t j lit) j q ↔
      Supplies three t j q ∧ Supplies three lit j q at meet
    rw [meet, hF, literal, Finset.forall_mem_insert]
    exact and_comm

private theorem principal [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role) (p : Observation Role j) :
    ∃ t : Term Role Var, t.IsCore ∧ ∀ q, Supplies three t j q ↔ postings q ⊆ postings p := by
  classical
  obtain ⟨t, ht, hits⟩ := exists_excluding three (Finset.univ.filter fun a => a ∉ postings p)
  refine ⟨t, ht, fun q => (hits q).trans ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h a ha => by_contra fun hn => h a hn ha, fun h _ hn ha => hn (h ha)⟩

private theorem exists_union [Fintype Role] [Fintype Var] [Nontrivial Var] (three : Fin 3 ↪ Role)
    (S : Finset (Observation Role j)) :
    ∃ t : Term Role Var, t.IsCore ∧ ∀ q, Supplies three t j q ↔ ∃ p ∈ S, postings q ⊆ postings p := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    obtain ⟨i, hi⟩ := exists_ne j
    exact ⟨.var i, trivial, fun q => by simp [Supplies, Term.eval, hi]⟩
  | insert p S _ ih =>
    obtain ⟨s, hs, hS⟩ := ih
    obtain ⟨t, ht, hp⟩ := principal three p
    refine ⟨Term.unionTerm three t s, ⟨⟨ht,hs⟩,⟨ht,hs⟩⟩, fun q => ?_⟩
    have hu : Supplies three (Term.unionTerm three t s) j q ↔
        Supplies three t j q ∨ Supplies three s j q := by simp [Supplies]
    simp [hu, hp, hS]

/-- All observers of one input can be prescribed in a single actual core word
exactly when the predicate respects inclusion of passive postings. A second
input permits the identically false predicate. -/
theorem exists_iff_downward [Fintype Role] [Fintype Var] [Nontrivial Var] (three : Fin 3 ↪ Role)
    (P : Observation Role j → Prop) :
    (∃ t : Term Role Var, t.IsCore ∧ ∀ q, Supplies three t j q ↔ P q) ↔ Downward P := by
  classical
  constructor
  · rintro ⟨t,ht,hP⟩ p q inc hq
    exact (hP p).mp (supplies_downward three t ht p q inc ((hP q).mpr hq))
  · intro h
    obtain ⟨t, ht, hS⟩ := exists_union three (Finset.univ.filter P)
    refine ⟨t, ht, fun q => (hS q).trans ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨p,hp,inc⟩ => h q p inc hp, fun hq => ⟨q,hq,Set.Subset.rfl⟩⟩

private theorem adjoin_inputs (three : Fin 3 ↪ Role) (t : Term Role Var) (ht : t.IsCore)
    (S : Finset Var) : ∃ s : Term Role Var, s.IsCore ∧ ∀ v k,
      k ∈ (s.eval v).val ↔ k ∈ (t.eval v).val ∨ ∃ i ∈ S, k ∈ (v i).val := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨t, ht, by simp⟩
  | insert i S _ ih =>
    obtain ⟨s, hs, he⟩ := ih
    refine ⟨Term.unionTerm three s (.var i), ⟨⟨hs,trivial⟩,⟨hs,trivial⟩⟩, fun v k => ?_⟩
    simp only [Term.eval_unionTerm, WinnerSet.val_union, Set.mem_union, he, Term.eval,
      Finset.mem_insert, or_and_right, exists_or, exists_eq_left]
    rw [or_assoc, @or_comm (∃ i ∈ S, k ∈ (v i).val) (k ∈ (v i).val)]

/-- Adjoining all passive projections gives the greatest completion. Its value
contains precisely the passive winners together with those supplied by the
distinguished input. -/
theorem exists_greatest [Fintype Role] [Fintype Var] [Nontrivial Var] (three : Fin 3 ↪ Role)
    (P : Observation Role j → Prop) (hP : Downward P) :
    ∃ s : Term Role Var, s.IsCore ∧ (∀ q, Supplies three s j q ↔ P q) ∧
      (∀ v k, k ∈ (s.eval v).val ↔
        (∃ i ≠ j, k ∈ (v i).val) ∨ (k ∈ (v j).val ∧ P ⟨k, pattern k j v⟩)) ∧
      ∀ t : Term Role Var, t.IsCore → (∀ q, Supplies three t j q ↔ P q) →
        ∀ v, (t.eval v).val ⊆ (s.eval v).val := by
  classical
  obtain ⟨t, ht, coeff⟩ := (exists_iff_downward three P).mpr hP
  obtain ⟨s, hs, value⟩ := adjoin_inputs three t ht (Finset.univ.erase j)
  simp only [Finset.mem_erase, Finset.mem_univ, and_true] at value
  have formula (v : Var → WinnerSet Role) (k : Role) :
      k ∈ (s.eval v).val ↔ (∃ i ≠ j, k ∈ (v i).val) ∨ (k ∈ (v j).val ∧ P ⟨k,pattern k j v⟩) := by
    rw [value, membership_iff_source three t ht v k]
    constructor
    · rintro (⟨i, hi, bit⟩ | other)
      · by_cases hij : i = j
        · subst i
          exact Or.inr ⟨hi, (coeff _).mp bit⟩
        · exact Or.inl ⟨i,hij,hi⟩
      · exact Or.inl other
    · rintro (other | ⟨hj, bit⟩)
      · exact Or.inr other
      · exact Or.inl ⟨j,hj,(coeff _).mpr bit⟩
  refine ⟨s, hs, fun q => ?_, formula, ?_⟩
  · simp [Supplies, formula, pattern_probe]
  · intro u hu coeff' v k hk
    obtain ⟨i, hi, bit⟩ := (membership_iff_source three u hu v k).mp hk
    apply (formula v k).mpr
    by_cases he : i = j
    · subst i
      exact Or.inr ⟨hi,(coeff' _).mp bit⟩
    · exact Or.inl ⟨i,he,hi⟩

/-- An intrinsic joint test for one complete source family and all singleton
profiles. All three predicates in the criterion are tests on the given data. -/
theorem exists_with_profiles_iff [Fintype Role] [Fintype Var] [Nontrivial Var]
    (three : Fin 3 ↪ Role) (Φ : Role → (Var → Bool) → Bool) (hΦ : AdmissibleProfiles Φ)
    (P : Observation Role j → Prop) :
    (∃ t : Term Role Var, t.IsCore ∧ HasProfiles Φ t ∧ ∀ q, Supplies three t j q ↔ P q) ↔
      Downward P ∧ (∀ q, Forced three Φ j q → P q) ∧ (∀ q, P q → Permitted three Φ j q) := by
  rw [exists_iff_between three Φ hΦ j P, exists_iff_downward]

end KFOL.Core.SingleSourceCompletion
