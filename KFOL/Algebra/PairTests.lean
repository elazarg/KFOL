module

public import KFOL.Algebra.Basic

/-!
# Singleton-or-pair countervaluations

Port of the status, single-membership and refinement argument in
`lean/FullAlgebra.lean`. Singleton tests determine every choice's status. Within
a fixed status cell evaluation is monotone, and preserving one input membership
suffices to preserve any specified output membership. Shrink inputs to pairs
while retaining that membership.
-/

@[expose] public section

namespace KFOL

universe u v

namespace WinnerSet

variable {Role : Type u}

/-- Values in the same status cell agree on every singleton test. -/
def SameStatus (A B : WinnerSet Role) : Prop :=
  ∀ r, A = singleton r ↔ B = singleton r

theorem SameStatus.choice {A B C D : WinnerSet Role}
    (hAC : SameStatus A C) (hBD : SameStatus B D) (r : Role) :
    SameStatus (choice r A B) (choice r C D) := by
  intro i
  by_cases hri : r = i
  · subst i
    rw [choice_eq_owner_iff, choice_eq_owner_iff]
    exact or_congr (hAC r) (hBD r)
  · rw [choice_eq_other_iff A B r hri, choice_eq_other_iff C D r hri]
    exact and_congr (hAC i) (hBD i)

theorem SameStatus.rename {A B : WinnerSet Role} (h : SameStatus A B)
    (p : Equiv.Perm Role) : SameStatus (rename p A) (rename p B) := by
  intro r
  obtain ⟨s, rfl⟩ := p.surjective r
  rw [rename_eq_singleton_iff, rename_eq_singleton_iff]
  exact h s

/-- Every value can be shrunk to a singleton or pair containing a specified
member, without changing any singleton test. -/
theorem exists_pair_subset (A : WinnerSet Role) (a : Role) (ha : a ∈ A.val) :
    ∃ B : WinnerSet Role, (∃ b c, B.val = {b, c}) ∧ B.val ⊆ A.val ∧
      SameStatus A B ∧ a ∈ B.val := by
  classical
  by_cases hA : A = singleton a
  · refine ⟨A, ⟨a, a, ?_⟩, Set.Subset.rfl, fun _ => Iff.rfl, ha⟩
    simp [hA]
  · have hb : ∃ b ∈ A.val, b ≠ a := by
      apply Classical.byContradiction
      intro h
      apply hA
      apply eq_singleton_of_subset A a
      intro b hb
      apply Classical.byContradiction
      intro hba
      exact h ⟨b, hb, hba⟩
    obtain ⟨b, hb, hba⟩ := hb
    let B : WinnerSet Role := ⟨{a, b}, a, by simp⟩
    have hsub : B.val ⊆ A.val := by
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact ha
      · exact Set.mem_singleton_iff.mp hx ▸ hb
    refine ⟨B, ⟨a, b, rfl⟩, hsub, ?_, by simp [B]⟩
    intro r
    constructor
    · intro h
      exact eq_singleton_of_subset B r (by simpa [h] using hsub)
    · intro h
      have ha' : a = r := by
        have : a ∈ B.val := by simp [B]
        simpa [h] using this
      have hb' : b = r := by
        have : b ∈ B.val := by simp [B]
        simpa [h] using this
      exact False.elim (hba (hb'.trans ha'.symm))

end WinnerSet

namespace Term

variable {Role : Type u} {Var : Type v}

theorem eval_sameStatus (t : Term Role Var) (v w : Var → WinnerSet Role)
    (h : ∀ x, WinnerSet.SameStatus (v x) (w x)) :
    WinnerSet.SameStatus (t.eval v) (t.eval w) := by
  induction t with
  | winner => exact fun _ => Iff.rfl
  | var x => exact h x
  | choice r s t hs ht => exact hs.choice ht r
  | rename p t ht => exact ht.rename p

/-- Evaluation is monotone under shrinking that preserves the status cell. -/
theorem eval_subset_of_sameStatus (t : Term Role Var) (v w : Var → WinnerSet Role)
    (hstatus : ∀ x, WinnerSet.SameStatus (v x) (w x))
    (hsub : ∀ x, (w x).val ⊆ (v x).val) : (t.eval w).val ⊆ (t.eval v).val := by
  classical
  induction t with
  | winner => exact Set.Subset.rfl
  | var x => exact hsub x
  | rename p t ht => exact Set.image_mono ht
  | choice r s t hs ht =>
    have transfer := or_congr ((s.eval_sameStatus v w hstatus) r)
      ((t.eval_sameStatus v w hstatus) r)
    by_cases hc : s.eval v = WinnerSet.singleton r ∨ t.eval v = WinnerSet.singleton r
    · have hc' := transfer.mp hc
      simp only [eval, WinnerSet.choice, ite_eq_left hc, ite_eq_left hc']
      exact Set.Subset.rfl
    · have hc' := fun h => hc (transfer.mpr h)
      simp only [eval, WinnerSet.choice, ite_eq_right hc, ite_eq_right hc', WinnerSet.val_union]
      exact Set.union_subset_union hs ht

private def Pinned (v : Var → WinnerSet Role) : Option (Var × Role) → Prop
  | none => True
  | some (x, a) => a ∈ (v x).val

/-- One input membership (or no input membership for a constant source)
preserves a chosen output member throughout its status cell. -/
private theorem one_pin (t : Term Role Var) (v : Var → WinnerSet Role)
    (k : Role) (hk : k ∈ (t.eval v).val) :
    ∃ pin : Option (Var × Role), Pinned v pin ∧
      ∀ w, (∀ x, WinnerSet.SameStatus (v x) (w x)) →
        Pinned w pin → k ∈ (t.eval w).val := by
  classical
  induction t generalizing k with
  | winner r => exact ⟨none, True.intro, fun _ _ _ => hk⟩
  | var x => exact ⟨some (x, k), hk, fun _ _ h => h⟩
  | rename p t ht =>
    obtain ⟨a, ha, he⟩ := hk
    obtain ⟨pin, hpin, preserve⟩ := ht a ha
    exact ⟨pin, hpin, fun w hstatus hpinned =>
      ⟨a, preserve w hstatus hpinned, he⟩⟩
  | choice r s t hs ht =>
    have transfer : ∀ w, (∀ x, WinnerSet.SameStatus (v x) (w x)) →
        (s.eval v = WinnerSet.singleton r ∨ t.eval v = WinnerSet.singleton r ↔
         s.eval w = WinnerSet.singleton r ∨ t.eval w = WinnerSet.singleton r) := by
      intro w hstatus
      exact or_congr ((s.eval_sameStatus v w hstatus) r)
        ((t.eval_sameStatus v w hstatus) r)
    by_cases hc : s.eval v = WinnerSet.singleton r ∨ t.eval v = WinnerSet.singleton r
    · have hkr : k = r := by simpa [eval, WinnerSet.choice, hc] using hk
      refine ⟨none, True.intro, ?_⟩
      intro w hstatus _
      have hc' := (transfer w hstatus).mp hc
      simp [eval, WinnerSet.choice, hc', hkr]
    · have hmem : k ∈ (s.eval v).val ∨ k ∈ (t.eval v).val := by
        simpa only [eval, WinnerSet.choice, ite_eq_right hc, WinnerSet.val_union,
          Set.mem_union] using hk
      rcases hmem with hmem | hmem
      · obtain ⟨pin, hpin, preserve⟩ := hs k hmem
        refine ⟨pin, hpin, ?_⟩
        intro w hstatus hpinned
        have hc' := fun h => hc ((transfer w hstatus).mpr h)
        simp only [eval, WinnerSet.choice, ite_eq_right hc', WinnerSet.val_union]
        exact Or.inl (preserve w hstatus hpinned)
      · obtain ⟨pin, hpin, preserve⟩ := ht k hmem
        refine ⟨pin, hpin, ?_⟩
        intro w hstatus hpinned
        have hc' := fun h => hc ((transfer w hstatus).mpr h)
        simp only [eval, WinnerSet.choice, ite_eq_right hc', WinnerSet.val_union]
        exact Or.inr (preserve w hstatus hpinned)

private theorem pair_valuation (v : Var → WinnerSet Role) (pin : Option (Var × Role))
    (hpin : Pinned v pin) :
    ∃ w : Var → WinnerSet Role,
      (∀ x, (∃ a b, (w x).val = {a, b}) ∧ (w x).val ⊆ (v x).val ∧
        WinnerSet.SameStatus (v x) (w x)) ∧ Pinned w pin := by
  classical
  let base : Var → Role := fun x => (v x).property.choose
  have hbase : ∀ x, base x ∈ (v x).val := fun x => (v x).property.choose_spec
  have make : ∀ a : Var → Role, (∀ x, a x ∈ (v x).val) →
      ∃ w : Var → WinnerSet Role,
        (∀ x, (∃ b c, (w x).val = {b, c}) ∧ (w x).val ⊆ (v x).val ∧
          WinnerSet.SameStatus (v x) (w x)) ∧ ∀ x, a x ∈ (w x).val := by
    intro a ha
    have hx := fun x => WinnerSet.exists_pair_subset (v x) (a x) (ha x)
    exact ⟨fun x => (hx x).choose,
      fun x => ⟨(hx x).choose_spec.1, (hx x).choose_spec.2.1,
        (hx x).choose_spec.2.2.1⟩, fun x => (hx x).choose_spec.2.2.2⟩
  cases pin with
  | none =>
    obtain ⟨w, hw, _⟩ := make base hbase
    exact ⟨w, hw, True.intro⟩
  | some xa =>
    obtain ⟨x₀, a₀⟩ := xa
    let a := fun x => if x = x₀ then a₀ else base x
    have ha : ∀ x, a x ∈ (v x).val := by
      intro x
      by_cases hx : x = x₀
      · subst x
        simpa [a, Pinned] using hpin
      · simpa [a, hx] using hbase x
    obtain ⟨w, hw, hwa⟩ := make a ha
    exact ⟨w, hw, by simpa [Pinned, a] using hwa x₀⟩

/-- A failed membership test has a singleton-or-pair countervaluation preserving
the specified distinguishing role and the direction of the failure. -/
theorem exists_pair_membership_countervaluation (s t : Term Role Var)
    (v : Var → WinnerSet Role) (k : Role)
    (hs : k ∈ (s.eval v).val) (ht : k ∉ (t.eval v).val) :
    ∃ w : Var → WinnerSet Role, (∀ x, ∃ a b, (w x).val = {a, b}) ∧
      k ∈ (s.eval w).val ∧ k ∉ (t.eval w).val := by
  obtain ⟨pin, hpin, preserve⟩ := s.one_pin v k hs
  obtain ⟨w, hw, hpinned⟩ := pair_valuation v pin hpin
  have hstatus := fun x => (hw x).2.2
  have hsub := fun x => (hw x).2.1
  exact ⟨w, fun x => (hw x).1, preserve w hstatus hpinned,
    fun h => ht (t.eval_subset_of_sameStatus v w hstatus hsub h)⟩

/-- Every failed equation fails when each variable has one or two winners. -/
theorem exists_pair_countervaluation (s t : Term Role Var)
    (failure : ∃ v : Var → WinnerSet Role, s.eval v ≠ t.eval v) :
    ∃ w : Var → WinnerSet Role, (∀ x, ∃ a b, (w x).val = {a, b}) ∧
      s.eval w ≠ t.eval w := by
  classical
  obtain ⟨v, hv⟩ := failure
  have hval : (s.eval v).val ≠ (t.eval v).val := fun h => hv (Subtype.ext h)
  obtain ⟨k, hk⟩ := Classical.not_forall.mp (fun h => hval (Set.ext h))
  by_cases hs : k ∈ (s.eval v).val
  · have ht : k ∉ (t.eval v).val := fun ht => hk ⟨fun _ => ht, fun _ => hs⟩
    obtain ⟨w, hw, hsw, htw⟩ := s.exists_pair_membership_countervaluation t v k hs ht
    exact ⟨w, hw, fun he => htw (he ▸ hsw)⟩
  · have ht : k ∈ (t.eval v).val := by
      by_contra ht
      exact hk ⟨fun h => False.elim (hs h), fun h => False.elim (ht h)⟩
    obtain ⟨w, hw, htw, hsw⟩ := t.exists_pair_membership_countervaluation s v k ht hs
    exact ⟨w, hw, fun he => hsw (he.symm ▸ htw)⟩

end Term

end KFOL
