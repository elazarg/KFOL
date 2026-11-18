module

public import KFOL.Core.ProfileBudgets.Folds
public import KFOL.Core.SourceProbes
public import KFOL.Algebra.Semilattice

/-! # Extracting a single owned fold from monochromatic negative observations -/

@[expose] public section

namespace KFOL.Core.ProfileBudgets

universe u v w
variable {Role : Type u} [DecidableEq Role] {Var : Type v} [DecidableEq Var] {Row : Type w}
attribute [local instance] Equational.coreStructure

omit [DecidableEq Role] in
private theorem choice_vars (r : Role) (x y : CoreTerm Role Var) :
    (choiceTerm r x y).varFinset = x.varFinset ∪ y.varFinset := by
  simp [choiceTerm, FirstOrder.Language.Term.varFinset, Finset.univ_fin2]

omit [DecidableEq Role] in
private theorem pruning_vars {r : Role} {t s : CoreTerm Role Var} (hp : Prunes r t s) :
    s.varFinset ⊆ t.varFinset := by
  induction hp with
  | var => rfl
  | owned _ _ ihx ihy => simpa only [choice_vars] using Finset.union_subset_union ihx ihy
  | left _ _ ih =>
    rw [choice_vars]
    exact ih.trans Finset.subset_union_left
  | right _ _ ih =>
    rw [choice_vars]
    exact ih.trans Finset.subset_union_right

private theorem fold_indicator {r : Role} {s : CoreTerm Role Var} (hf : OwnedFold r s)
    (i : Var) : profile r (fun j => decide (j = i)) s = true ↔ i ∈ s.varFinset := by
  induction hf with
  | var j => simp [FirstOrder.Language.Term.varFinset, eq_comm]
  | choice _ _ ihx ihy => simp only [profile_choice, ite_true, Bool.or_eq_true, choice_vars,
      Finset.mem_union, ihx, ihy]

/-- Each budget has a single possible allowed absorber. If all ineligible inputs
of a budget are assigned its owner, a safe word has a safe one-owner pruning
using only inputs assigned to that owner. -/
theorem exists_owned_pruning_of_row_owners (b : Row → Budget Role Var)
    (owner : Var → Role) (rowOwner : Row → Role)
    (mono : ∀ z q, q ∈ (b z).allowed → q ≠ rowOwner z → ∀ i, (b z).values i ≠ WinnerSet.singleton q)
    (assigned : ∀ z i, ¬((b z).values i).val ⊆ (b z).allowed → owner i = rowOwner z)
    (t : CoreTerm Role Var) (ht : Satisfies b t) :
    ∃ r s, Prunes r t s ∧ s.varFinset.Nonempty ∧ s.varFinset ⊆ t.varFinset ∧
      (∀ i ∈ s.varFinset, owner i = r) ∧ SafeSupport b r (s.varFinset : Set Var) ∧
      Satisfies b s := by
  let outside (r : Role) (i : Var) := decide (owner i ≠ r)
  have hloss : ∃ r, profile r (outside r) t = false := by
    by_contra! hh
    obtain ⟨i, hi⟩ := profile_common_source id Function.injective_id outside t
      (fun r => Bool.eq_true_of_not_eq_false (hh r))
    simpa [outside] using hi (owner i)
  obtain ⟨r, hr⟩ := hloss
  obtain ⟨s, hp, _, hneg⟩ := exists_pruning_pair r r (fun _ => true) (outside r) t
  obtain ⟨S, hS, hprof, hbound⟩ := hp.ownedFold.support
  have heq : S = s.varFinset := by
    ext i
    have hh := (hprof r (fun j => decide (j = i))).symm.trans (fold_indicator hp.ownedFold i)
    simpa only [ite_true, decide_eq_true_eq, exists_eq_right] using hh
  subst S
  have howner (i) (hi : i ∈ s.varFinset) : owner i = r := by
    by_contra hn
    have hw : profile r (outside r) s = true := by
      rw [hprof, ite_eq_left rfl]
      exact ⟨i, hi, decide_eq_true hn⟩
    rw [hneg hr] at hw
    contradiction
  let restricted (z : {z // rowOwner z = r}) := b z.val
  have ha : SingleAbsorber restricted r := fun z q hq hqr =>
    mono z.val q hq (by simpa only [z.property] using hqr)
  have hs := hp.satisfies ha (fun z => ht z.val)
  have hsafe : SafeSupport b r (s.varFinset : Set Var) := by
    intro z
    by_cases hz : rowOwner z = r
    · exact (hbound _ _).mp (hs ⟨z,hz⟩)
    · left
      intro i hi
      by_contra hn
      exact hz ((assigned z i hn).symm.trans (howner i hi))
  exact ⟨r, s, hp, hS, pruning_vars hp, howner, hsafe, fun z => (hbound _ _).mpr (hsafe z)⟩

end KFOL.Core.ProfileBudgets

namespace KFOL.Core.Sources

open ProfileBudgets
universe u v w
variable {Role : Type u} [DecidableEq Role] {Var : Type v} [DecidableEq Var] {Row : Type w}
attribute [local instance] Equational.coreStructure

private noncomputable def probeBudget (three : Fin 3 ↪ Role) (q : ProbeIndex Role Var) :
    Budget Role Var := ⟨probeAt three q, exclusionBounds q⟩

private theorem exists_monochromatic_support (three : Fin 3 ↪ Role)
    (rows : Row → ProbeIndex Role Var) (owner : Var → Role)
    (mono : ∀ z i q, (rows z).2.2 i = .atom q → q.val = owner (rows z).2.1)
    (t : CoreTerm Role Var)
    (ht : ∀ z, (rows z).1 ∉ (t.realize (probeAt three (rows z))).val) :
    ∃ (r : Role) (S : Finset Var), S.Nonempty ∧ S ⊆ t.varFinset ∧ (∀ i ∈ S, owner i = r) ∧
      SafeSupport (fun z => probeBudget three (rows z)) r (S : Set Var) := by
  let b (z : Row) := probeBudget three (rows z)
  have habs : ∀ z q, q ∈ (b z).allowed → q ≠ owner (rows z).2.1 →
      ∀ i, (b z).values i ≠ WinnerSet.singleton q := by
    intro z q hq hn i he
    change q ≠ (rows z).1 at hq
    change probe three _ _ _ i = _ at he
    by_cases hi : i = (rows z).2.1
    · subst i
      rw [probe_source] at he
      exact hq (WinnerSet.singleton_inj.mp he).symm
    · rw [probe_other three _ _ _ i hi] at he
      exact hn (mono z ⟨i,hi⟩ ⟨q,hq⟩ ((representative_atom_iff three _ _ ⟨q,hq⟩).mp he))
  have assigned : ∀ z i, ¬((b z).values i).val ⊆ (b z).allowed →
      owner i = owner (rows z).2.1 := by
    intro z i hn
    apply congrArg owner
    apply (mem_probe_iff three _ _ _ i).mp
    by_contra hh
    exact hn (fun a ha he => hh (he ▸ ha))
  have safe : Satisfies b t := fun z _ ha he => ht z (he ▸ ha)
  obtain ⟨r, s, _, hS, hsub, own, hs, _⟩ :=
    exists_owned_pruning_of_row_owners b owner (fun z => owner (rows z).2.1) habs assigned t safe
  exact ⟨r, s.varFinset, hS, hsub, own, hs⟩

/-- When all postings on each negative source probe have the designated owner
of its head, every safe core word contains a nonempty, equally safe fold
support in one designated owner class. -/
theorem exists_monochromatic_safe_fold (three : Fin 3 ↪ Role) (rows : Row → ProbeIndex Role Var)
    (owner : Var → Role)
    (mono : ∀ z i q, (rows z).2.2 i = .atom q → q.val = owner (rows z).2.1)
    (t : CoreTerm Role Var)
    (ht : ∀ z, (rows z).1 ∉ (t.realize (probeAt three (rows z))).val) :
    ∃ (r : Role) (S : Finset Var) (hS : S.Nonempty), S ⊆ t.varFinset ∧ (∀ i ∈ S, owner i = r) ∧
      ∀ z, (rows z).1 ∉ (WinnerSet.choiceFold r S hS (probeAt three (rows z))).val := by
  let b (z : Row) := probeBudget three (rows z)
  obtain ⟨r, S, hS, hsub, own, hs⟩ := exists_monochromatic_support three rows owner mono t ht
  refine ⟨r, S, hS, hsub, own, ?_⟩
  intro z
  rcases hs z with all | ⟨hr, i, hi, he⟩
  · let := WinnerSet.choiceSemilattice r
    have hfold : (WinnerSet.choiceFold r S hS (b z).values).val ⊆ (b z).allowed :=
      Finset.sup'_induction hS (b z).values (p := fun x : WinnerSet Role => x.val ⊆ (b z).allowed)
        (fun x hx y hy => (WinnerSet.choice_subset_union r x y).trans (Set.union_subset hx hy)) all
    exact fun hm => (hfold hm) rfl
  · rw [(WinnerSet.choiceFold_eq_owner_iff r _ hS (probeAt three (rows z))).mpr ⟨i,hi,he⟩]
    exact fun hm => hr hm.symm

omit [DecidableEq Role] in
/-- On a set of inputs of the same designated owner, a negative probe is
safe precisely when selecting its head also selects at least one of its posts. -/
private theorem safe_support_iff_posts (three : Fin 3 ↪ Role) (rows : Row → ProbeIndex Role Var)
    (owner : Var → Role)
    (mono : ∀ z i q, (rows z).2.2 i = .atom q → q.val = owner (rows z).2.1)
    (r : Role) (S : Finset Var) (own : ∀ i ∈ S, owner i = r) :
    SafeSupport (fun z => probeBudget three (rows z)) r (S : Set Var) ↔
      ∀ z, (rows z).2.1 ∈ S → ∃ i : {i // i ≠ (rows z).2.1},
        i.val ∈ S ∧ (rows z).2.2 i ≠ .neutral := by
  constructor
  · intro hs z hj
    obtain all | ⟨hr, i, hi, he⟩ := hs z
    · exact False.elim (all _ hj ((mem_probe_iff three _ _ _ _).mpr rfl) rfl)
    · change r ≠ (rows z).1 at hr
      change probe three _ _ _ i = _ at he
      have hne : i ≠ (rows z).2.1 := by
        rintro rfl
        rw [probe_source] at he
        exact hr (WinnerSet.singleton_inj.mp he).symm
      rw [probe_other three _ _ _ i hne] at he
      have hatom := (representative_atom_iff three _ _ ⟨r,hr⟩).mp he
      exact ⟨⟨i,hne⟩,hi,fun hn => by rw [hatom] at hn; contradiction⟩
  · intro posts z
    by_cases hj : (rows z).2.1 ∈ S
    · obtain ⟨i, hi, hp⟩ := posts z hj
      cases he : (rows z).2.2 i with
      | neutral => exact False.elim (hp he)
      | atom q =>
        have hqr : q.val = r := (mono z i q he).trans (own _ hj)
        subst r
        refine Or.inr ⟨q.property, i.val, hi, ?_⟩
        change probe three _ _ _ _ = _
        rw [probe_other three _ _ _ i.val i.property]
        exact (representative_atom_iff three _ _ q).mpr he
    · left
      intro i hi a ha he
      have eq := (mem_probe_iff three _ _ _ i).mp (he ▸ ha)
      exact hj (eq ▸ hi)

/-- A simultaneous negative sample with monochromatic postings per head has
a safe word exactly when it admits a nonempty, one-owner set of inputs that
hits the postings of every row whose head it contains. -/
theorem exists_safe_word_iff_hits_postings (three : Fin 3 ↪ Role) (rows : Row → ProbeIndex Role Var)
    (owner : Var → Role)
    (mono : ∀ z i q, (rows z).2.2 i = .atom q → q.val = owner (rows z).2.1) :
    (∃ t : CoreTerm Role Var, ∀ z, (rows z).1 ∉ (t.realize (probeAt three (rows z))).val) ↔
      ∃ (r : Role) (S : Finset Var), S.Nonempty ∧ (∀ i ∈ S, owner i = r) ∧
        ∀ z, (rows z).2.1 ∈ S → ∃ i : {i // i ≠ (rows z).2.1},
          i.val ∈ S ∧ (rows z).2.2 i ≠ .neutral := by
  constructor
  · rintro ⟨t,ht⟩
    obtain ⟨r,S,hS,_,own,hs⟩ := exists_monochromatic_support three rows owner mono t ht
    exact ⟨r,S,hS,own,(safe_support_iff_posts three rows owner mono r S own).mp hs⟩
  · rintro ⟨r,S,hS,own,posts⟩
    have hs := (safe_support_iff_posts three rows owner mono r S own).mpr posts
    obtain ⟨t,_,ht⟩ := exists_fold_support (Row := Row) r S hS
    exact ⟨t,fun z hm => ht _ hs z hm rfl⟩

/-- With one loss per head, the surviving set condition says that each
selected input has an outgoing posting to another selected input. -/
theorem exists_safe_word_iff_posted_successors (three : Fin 3 ↪ Role)
    (observer owner : Var → Role) (p : ∀ j, Pattern (observer j) j)
    (mono : ∀ j i q, p j i = .atom q → q.val = owner j) :
    (∃ t : CoreTerm Role Var, ∀ j, observer j ∉ (t.realize (probe three (observer j) j (p j))).val) ↔
      ∃ (r : Role) (S : Finset Var), S.Nonempty ∧ (∀ i ∈ S, owner i = r) ∧
        ∀ j ∈ S, ∃ i : {i // i ≠ j}, i.val ∈ S ∧ p j i ≠ .neutral :=
  exists_safe_word_iff_hits_postings three (fun j => ⟨observer j,j,p j⟩) owner mono

end KFOL.Core.Sources
