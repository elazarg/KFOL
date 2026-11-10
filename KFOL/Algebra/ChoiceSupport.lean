module

public import KFOL.Algebra.Semilattice
public import KFOL.Definitions.Core
public import Mathlib.Data.Fintype.EquivFin

/-! # Finite observational support for arbitrary owned-choice families

Only the role carrier is finite. The index family need not be finite or
countable; the support is chosen after the actual winner values are fixed.
-/

@[expose] public section

namespace KFOL.WinnerSet

universe u v
variable {Role : Type u} {Index : Type v}

/-- A non-owner-atom value contains some nonowner winner. -/
theorem exists_mem_ne_of_ne_singleton (owner : Role) (A : WinnerSet Role)
    (hne : A ≠ singleton owner) : ∃ winner ∈ A.val, winner ≠ owner := by
  classical
  by_contra h
  apply hne
  apply eq_singleton_of_subset
  intro winner hw
  change winner = owner
  by_contra hn
  exact h ⟨winner, hw, hn⟩

/-- With no absorbing owner atom, at most one representative per nonowner
role covers the complete union. An owner-containing anchor is reused for one
of its nonowner winners, so it does not cost an additional representative. -/
theorem exists_small_union_support [Fintype Role] [Nonempty Index]
    (owner : Role) (values : Index → WinnerSet Role)
    (hn : ∀ i, values i ≠ singleton owner) :
    ∃ S : Finset Index, S.Nonempty ∧ S.card ≤ Fintype.card Role - 1 ∧
      ∀ winner, (∃ i, winner ∈ (values i).val) ↔ ∃ i ∈ S, winner ∈ (values i).val := by
  classical
  obtain ⟨anchor, ha⟩ : ∃ anchor : Index,
      (∃ i, owner ∈ (values i).val) → owner ∈ (values anchor).val := by
    by_cases he : ∃ i, owner ∈ (values i).val
    · obtain ⟨anchor, ha⟩ := he
      exact ⟨anchor, fun _ => ha⟩
    · exact ⟨Classical.arbitrary Index, fun h => (he h).elim⟩
  obtain ⟨other, ho, hne⟩ := exists_mem_ne_of_ne_singleton owner (values anchor) (hn anchor)
  let D : Finset Role := Finset.univ.filter (fun r => r ≠ owner ∧ ∃ i, r ∈ (values i).val)
  have hD (r : Role) : r ∈ D ↔ r ≠ owner ∧ ∃ i, r ∈ (values i).val := by simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
  have hother : other ∈ D := (hD other).mpr ⟨hne, anchor, ho⟩
  let pick (r : Role) : Index :=
    if r = other then anchor else
      if hr : ∃ i, r ∈ (values i).val then Classical.choose hr else anchor
  have hpick (r : Role) (hr : r ∈ D) : r ∈ (values (pick r)).val := by
    by_cases he : r = other
    · subst r
      simpa only [pick, ite_true] using ho
    · have hex := (hD r).mp hr |>.2
      simp only [pick, he, ite_false, dite_eq_left hex]
      exact Classical.choose_spec hex
  have hanchor : pick other = anchor := by simp only [pick, ite_true]
  let S := D.image pick
  have hS : S.Nonempty := ⟨pick other, Finset.mem_image.mpr ⟨other, hother, rfl⟩⟩
  have hcard : S.card ≤ Fintype.card Role - 1 := calc
    S.card ≤ D.card := Finset.card_image_le
    _ ≤ (Finset.univ.erase owner).card := Finset.card_le_card (by
      intro r hr
      exact Finset.mem_erase.mpr ⟨(hD r).mp hr |>.1, Finset.mem_univ _⟩)
    _ = Fintype.card Role - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  refine ⟨S, hS, hcard, ?_⟩
  intro winner
  constructor
  · intro hw
    by_cases he : winner = owner
    · subst winner
      refine ⟨anchor, ?_, ha hw⟩
      rw [← hanchor]
      exact Finset.mem_image.mpr ⟨other, hother, rfl⟩
    · have hd := (hD winner).mpr ⟨he, hw⟩
      exact ⟨pick winner, Finset.mem_image.mpr ⟨winner, hd, rfl⟩, hpick winner hd⟩
  · rintro ⟨i, _, hi⟩
    exact ⟨i, hi⟩

open Classical in
/-- Owned-choice breadth is at most K-1 for K≥2, even for an arbitrary
nonempty index type. The right side independently specifies absorption or
union of the complete original family. -/
theorem exists_small_choice_support [Fintype Role] [Nontrivial Role] [Nonempty Index]
    (owner : Role) (values : Index → WinnerSet Role) :
    ∃ (S : Finset Index) (hS : S.Nonempty), S.card ≤ Fintype.card Role - 1 ∧
      (choiceFold owner S hS values).val =
        if ∃ i, values i = singleton owner then {owner}
        else {winner | ∃ i, winner ∈ (values i).val} := by
  classical
  by_cases he : ∃ i, values i = singleton owner
  · obtain ⟨i, hi⟩ := he
    refine ⟨{i}, Finset.singleton_nonempty i, ?_, ?_⟩
    · have hc := Fintype.one_lt_card (α := Role)
      simp only [Finset.card_singleton]
      omega
    · have hex : ∃ j, values j = singleton owner := ⟨i, hi⟩
      rw [ite_eq_left hex]
      exact congrArg Subtype.val ((choiceFold_eq_owner_iff owner {i}
        (Finset.singleton_nonempty i) values).mpr ⟨i, Finset.mem_singleton_self _, hi⟩)
  · have hn : ∀ i, values i ≠ singleton owner := fun i hi => he ⟨i, hi⟩
    obtain ⟨S, hS, hc, hcover⟩ := exists_small_union_support owner values hn
    refine ⟨S, hS, hc, ?_⟩
    rw [ite_eq_right he]
    ext winner
    exact (mem_choiceFold_of_no_owner owner S hS values (fun i _ => hn i) winner).trans (hcover winner).symm

/-- The same support is an actual least upper bound in mathlib's
owned-choice semilattice, including for an infinite index type. -/
theorem exists_small_choice_isLUB [Fintype Role] [Nontrivial Role] [Nonempty Index]
    (owner : Role) (values : Index → WinnerSet Role) :
    ∃ (S : Finset Index) (hS : S.Nonempty), S.card ≤ Fintype.card Role - 1 ∧
      @IsLUB (WinnerSet Role) (choiceSemilattice owner).toLE
        (Set.range values) (choiceFold owner S hS values) := by
  classical
  let _ := choiceSemilattice owner
  let _ : LE (WinnerSet Role) := (choiceSemilattice owner).toLE
  obtain ⟨S, hS, hc, hv⟩ := exists_small_choice_support owner values
  refine ⟨S, hS, hc, ?_, ?_⟩
  · rintro A ⟨i, rfl⟩
    apply (choice_le_iff owner _ _).mpr
    by_cases he : ∃ i, values i = singleton owner
    · left
      apply Subtype.ext
      change (choiceFold owner S hS values).val = {owner}
      simpa only [ite_eq_left he] using hv
    · right
      refine ⟨fun hi => he ⟨i, hi⟩, ?_⟩
      intro winner hw
      rw [hv, ite_eq_right he]
      exact ⟨i, hw⟩
  · intro B hB
    exact Finset.sup'_le hS values (fun i _ => hB ⟨i, rfl⟩)

/-- For nonowner singleton operands, the finite fold retains precisely the
listed roles. -/
theorem choiceFold_singletons [DecidableEq Role] (owner : Role) (S : Finset Role)
    (hS : S.Nonempty) (hn : owner ∉ S) :
    (choiceFold owner S hS singleton).val = (S : Set Role) := by
  classical
  ext winner
  rw [mem_choiceFold_of_no_owner owner S hS singleton]
  · simp only [singleton, Set.mem_singleton_iff, Finset.mem_coe]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hw
      exact ⟨winner, hw, rfl⟩
  · intro i hi he
    have heq := singleton_inj.mp he
    exact hn (heq ▸ hi)

/-- The K-1 bound is sharp: reproducing all nonowner singleton winners
requires every one of the K-1 distinct operands. -/
theorem choice_support_sharp [Fintype Role] [DecidableEq Role]
    (owner : Role) (S : Finset Role) (hS : S.Nonempty) (hn : owner ∉ S)
    (he : (choiceFold owner S hS singleton).val = {winner | winner ≠ owner}) :
    S = Finset.univ.erase owner ∧ S.card = Fintype.card Role - 1 := by
  have hv : (S : Set Role) = {winner | winner ≠ owner} := (choiceFold_singletons owner S hS hn).symm.trans he
  have hs : S = Finset.univ.erase owner := by
    ext winner
    change winner ∈ (S : Set Role) ↔ _
    rw [hv]
    simp only [Set.mem_ofPred_eq, Finset.mem_erase, Finset.mem_univ, and_true]
  refine ⟨hs, ?_⟩
  rw [hs, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]

end KFOL.WinnerSet

namespace KFOL.Term

universe u v w
variable {Role : Type u} {Var : Type v}

/-- Finite owned-choice folds have actual core syntax, so compiling the fold
introduces no winner constants or role permutations. -/
theorem exists_core_choice_fold {Index : Type w} (owner : Role) (S : Finset Index)
    (hS : S.Nonempty) (terms : Index → Term Role Var) (hc : ∀ i ∈ S, (terms i).IsCore) :
    ∃ t : Term Role Var, t.IsCore ∧ ∀ v : Var → WinnerSet Role,
      t.eval v = WinnerSet.choiceFold owner S hS (fun i => (terms i).eval v) := by
  let := WinnerSet.choiceSemilattice owner
  have hp : ∃ t : Term Role Var, t.IsCore ∧ ∀ v : Var → WinnerSet Role,
      t.eval v = (S.sup' hS (fun i v => (terms i).eval v)) v :=
    Finset.sup'_induction hS (fun i v => (terms i).eval v)
      (p := fun f : (Var → WinnerSet Role) → WinnerSet Role =>
        ∃ t : Term Role Var, t.IsCore ∧ ∀ v, t.eval v = f v)
      (fun f ⟨s, hs, hscore⟩ g ⟨t, ht, htcore⟩ =>
        ⟨.choice owner s t, ⟨hs, ht⟩, fun v => by
          change WinnerSet.choice owner (s.eval v) (t.eval v) = WinnerSet.choice owner (f v) (g v)
          rw [hscore, htcore]⟩)
      (fun i hi => ⟨terms i, hc i hi, fun _ => rfl⟩)
  obtain ⟨t, ht, he⟩ := hp
  refine ⟨t, ht, fun v => ?_⟩
  exact (he v).trans (Finset.sup'_apply hS _ v)

end KFOL.Term
