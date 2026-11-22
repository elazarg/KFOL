module

public import KFOL.Core.ProfileSynthesis
public import KFOL.Algebra.ViewOrders.Monotone
import KFOL.Algebra.Monotone

/-! # Pruning a positive singleton profile and realizing a unanimous singleton face -/

@[expose] public section

namespace KFOL.Core

universe u v w
variable {Role : Type u} [DecidableEq Role] {Var : Type v}
attribute [local instance] Equational.coreStructure

/-- A restriction on the owner labels of a core word, independent of its evaluation. -/
def OwnersIn (P : Role → Prop) : Equational.Term (Equational.CoreSymbol Role) Var → Prop
  | .var _ => True
  | .func (.choice r) args => P r ∧ OwnersIn P (args 0) ∧ OwnersIn P (args 1)

/-- At an owner absent from the gates, a word's profile is the conjunction over
precisely its occurring variables. -/
theorem profile_iff_forall_mem_varFinset_of_ownersIn [DecidableEq Var] (a : Role)
    (g : Equational.Term (Equational.CoreSymbol Role) Var) (foreign : OwnersIn (· ≠ a) g)
    (B : Var → Bool) : profile a B g = true ↔ ∀ x ∈ g.varFinset, B x = true := by
  induction g using induction_choice with
  | var x => simp [FirstOrder.Language.Term.varFinset]
  | choice r s t ihs iht =>
    obtain ⟨hr, hs, ht⟩ := foreign
    rw [profile_choice, ite_eq_right hr, Bool.and_eq_true, ihs hs, iht ht]
    simp [choiceTerm, FirstOrder.Language.Term.varFinset, Finset.univ_fin2, or_imp, forall_and]

/-- The profile only sees flags at inputs occurring in the word. -/
theorem profile_congr_on_varFinset [DecidableEq Var] (a : Role)
    (g : Equational.Term (Equational.CoreSymbol Role) Var) (B C : Var → Bool)
    (agree : ∀ x ∈ g.varFinset, B x = C x) : profile a B g = profile a C g := by
  induction g using induction_choice with
  | var x => exact agree x (by simp [FirstOrder.Language.Term.varFinset])
  | choice r s t ihs iht =>
    simp [choiceTerm, FirstOrder.Language.Term.varFinset, Finset.univ_fin2,
      or_imp, forall_and] at agree
    rw [profile_choice, profile_choice, ihs agree.1, iht agree.2]

/-- A proper-support word at an owned root has a coatom support and a
unanimous root-owner profile when the parent profile has no two-hole win. -/
theorem proper_child_unanimous_of_no_two_hole_win [DecidableEq Var] (a : Role)
    (s t : Equational.Term (Equational.CoreSymbol Role) Var) {i : Var}
    (missing : i ∉ s.varFinset)
    (parent : ∀ (B : Var → Bool) (x y : Var), x ≠ y → B x = false → B y = false →
      profile a B (choiceTerm a s t) = false) :
    (∀ x, x ∈ s.varFinset ↔ x ≠ i) ∧
      ∀ B : Var → Bool, profile a B s = true ↔ ∀ x ∈ s.varFinset, B x = true := by
  have full (g : Equational.Term (Equational.CoreSymbol Role) Var) :
      profile a (fun _ => true) g = true := by
    induction g using induction_choice with
    | var x => rfl
    | choice r u v ihu ihv => simp [profile_choice, ihu, ihv]
  have onlyFull (B : Var → Bool) (win : profile a B s = true) :
      ∀ x, x ≠ i → B x = true := by
    intro x different
    by_contra notTrue
    let C : Var → Bool := fun y => if y = i then false else B y
    have eq := profile_congr_on_varFinset a s B C (by
      intro y member
      have ne : y ≠ i := fun h => missing (h ▸ member)
      simp [C, ne])
    have winC : profile a C s = true := eq ▸ win
    have falseX : B x = false := Bool.eq_false_iff.mpr notTrue
    have h := parent C x i different (by simp [C, different, falseX]) (by simp [C])
    simp [profile_choice, winC] at h
  constructor
  · intro x
    refine ⟨fun member eq => missing (eq ▸ member), fun different => ?_⟩
    have win : profile a (fun y => decide (y ∈ s.varFinset)) s = true := by
      rw [profile_congr_on_varFinset a s _ (fun _ => true)
        (by intro y member; simp [member])]
      exact full s
    simpa using onlyFull _ win x different
  · intro B
    refine ⟨fun win x member => onlyFull B win x (fun eq => missing (eq ▸ member)), ?_⟩
    intro all
    rw [profile_congr_on_varFinset a s B (fun _ => true) all]
    exact full s

/-- Retention of a foreign winner on rows with two designated ambiguous
inputs excludes any singleton-profile win with two missing flags. -/
theorem no_two_hole_win_of_retention (a k : Role) (foreign : k ≠ a)
    (menu : WinnerSet Role) (notAtom : menu ≠ WinnerSet.singleton a)
    (g : Equational.Term (Equational.CoreSymbol Role) Var)
    (retain : ∀ (v : Var → WinnerSet Role) (x y : Var),
      x ≠ y → v x = menu → v y = menu → k ∈ (g.realize v).val) :
    ∀ (B : Var → Bool) (x y : Var), x ≠ y → B x = false → B y = false →
      profile a B g = false := by
  classical
  intro B x y different hx hy
  let v : Var → WinnerSet Role := fun z => if B z then WinnerSet.singleton a else menu
  have seen : (fun z => decide (v z = WinnerSet.singleton a)) = B := by
    funext z
    cases h : B z <;> simp [v, h, notAtom]
  by_contra fail
  have win : profile a B g = true := by cases h : profile a B g <;> simp_all
  have atom : g.realize v = WinnerSet.singleton a := by
    rw [winnerSet_eq_singleton_iff_profile, seen]
    exact win
  have mark := retain v x y different (by simp [v, hx]) (by simp [v, hy])
  simp [atom, WinnerSet.singleton, foreign] at mark

/-- A positive owner profile on a coalition gives a term using only that coalition,
without gates of that owner, below the original in that owner's view at every valuation. -/
theorem exists_view_below_of_profile (a : Role) (A : Var → Bool)
    (t : Equational.Term (Equational.CoreSymbol Role) Var) (positive : profile a A t = true) :
    ∃ u : Equational.Term (Equational.CoreSymbol Role) {x // A x = true},
      OwnersIn (· ≠ a) u ∧ ∀ v : Var → WinnerSet Role, PlayerView.Below a
        (WinnerSet.view a (u.realize (fun x => v x.val))) (WinnerSet.view a (t.realize v)) := by
  induction t using induction_choice with
  | var x =>
    refine ⟨.var ⟨x, positive⟩, trivial, fun _ => (WinnerSet.view_below_iff _ _ _).mpr ?_⟩
    exact ⟨id, fun _ _ => id⟩
  | choice r s t ihs iht =>
    by_cases same : r = a
    · subst r
      simp only [profile_choice, ite_true, Bool.or_eq_true] at positive
      rcases positive with hs | ht
      · obtain ⟨u, gu, hu⟩ := ihs hs
        exact ⟨u, gu, fun v => WinnerSet.view_below_choice_self a (Or.inl (hu v))⟩
      · obtain ⟨u, gu, hu⟩ := iht ht
        exact ⟨u, gu, fun v => WinnerSet.view_below_choice_self a (Or.inr (hu v))⟩
    · simp only [profile_choice, ite_eq_right same, Bool.and_eq_true] at positive
      obtain ⟨u, gu, hu⟩ := ihs positive.1
      obtain ⟨w, gw, hw⟩ := iht positive.2
      exact ⟨choiceTerm r u w, ⟨same, gu, gw⟩, fun v => WinnerSet.view_choice_mono a r (hu v) (hw v)⟩

/-- The same restricted term preserves every omission of the owner on an arbitrary
family of rows, including the marked probes for source coefficients. -/
theorem exists_omitting_of_profile {Row : Type w} (a : Role) (A : Var → Bool)
    (t : Equational.Term (Equational.CoreSymbol Role) Var) (positive : profile a A t = true)
    (rows : Row → Var → WinnerSet Role) (omitted : ∀ j, a ∉ (t.realize (rows j)).val) :
    ∃ u : Equational.Term (Equational.CoreSymbol Role) {x // A x = true},
      ∀ j, a ∉ (u.realize (fun x => rows j x.val)).val := by
  obtain ⟨u, _, hu⟩ := exists_view_below_of_profile a A t positive
  exact ⟨u, fun j wins => omitted j (((WinnerSet.view_below_iff _ _ _).mp (hu (rows j))).1 wins)⟩

/-- Keep every branch which can pass the owner test on the selected inputs.
On valuations with no other atom of that owner, deleting the other branches
preserves the owner test and gives a pointwise smaller word. -/
theorem exists_below_preserving_profile (a : Role) (A : Var → Bool)
    (t : Equational.Term (Equational.CoreSymbol Role) Var) (positive : profile a A t = true) :
    ∃ u : Equational.Term (Equational.CoreSymbol Role) {x // A x = true},
      ∀ v : Var → WinnerSet Role, (∀ x, v x = WinnerSet.singleton a → A x = true) →
        (u.realize (fun x => v x.val)).val ⊆ (t.realize v).val ∧
          (u.realize (fun x => v x.val) = WinnerSet.singleton a ↔ t.realize v = WinnerSet.singleton a) := by
  classical
  have cannotAbsorb (s : Equational.Term (Equational.CoreSymbol Role) Var)
      (failed : profile a A s ≠ true) (v : Var → WinnerSet Role)
      (inside : ∀ x, v x = WinnerSet.singleton a → A x = true) :
      s.realize v ≠ WinnerSet.singleton a := by
    intro atom
    apply failed
    exact profile_mono a _ A (by simpa only [decide_eq_true_eq] using inside) s
      ((winnerSet_eq_singleton_iff_profile s a v).mp atom)
  induction t using induction_choice with
  | var x => exact ⟨.var ⟨x, positive⟩, fun _ _ => ⟨Set.Subset.rfl, Iff.rfl⟩⟩
  | choice r s t ihs iht =>
    by_cases keepS : profile a A s = true <;> by_cases keepT : profile a A t = true
    · obtain ⟨u, hu⟩ := ihs keepS
      obtain ⟨w, hw⟩ := iht keepT
      refine ⟨choiceTerm r u w, fun v inside => ?_⟩
      obtain ⟨subU, atomU⟩ := hu v inside
      obtain ⟨subW, atomW⟩ := hw v inside
      change (WinnerSet.choice r _ _).val ⊆ (WinnerSet.choice r _ _).val ∧
        (WinnerSet.choice r _ _ = WinnerSet.singleton a ↔ WinnerSet.choice r _ _ = WinnerSet.singleton a)
      refine ⟨WinnerSet.choice_mono r subU subW, ?_⟩
      by_cases own : r = a
      · subst r
        exact (WinnerSet.choice_eq_owner_iff _ _ _).trans
          ((or_congr atomU atomW).trans (WinnerSet.choice_eq_owner_iff _ _ _).symm)
      · exact (WinnerSet.choice_eq_other_iff _ _ _ own).trans
          ((and_congr atomU atomW).trans (WinnerSet.choice_eq_other_iff _ _ _ own).symm)
    · have own : r = a := by
        by_contra ne
        exact keepT ((by simpa only [profile_choice, ite_eq_right ne, Bool.and_eq_true] using positive :
          profile a A s = true ∧ profile a A t = true).2)
      subst r
      obtain ⟨u, hu⟩ := ihs keepS
      refine ⟨u, fun v inside => ?_⟩
      obtain ⟨sub, atom⟩ := hu v inside
      have no := cannotAbsorb t keepT v inside
      refine ⟨sub.trans (WinnerSet.subset_choice_of_right_ne _ _ _ no), ?_⟩
      exact atom.trans ((or_iff_left no).symm.trans (WinnerSet.choice_eq_owner_iff _ _ _).symm)
    · have own : r = a := by
        by_contra ne
        exact keepS ((by simpa only [profile_choice, ite_eq_right ne, Bool.and_eq_true] using positive :
          profile a A s = true ∧ profile a A t = true).1)
      subst r
      obtain ⟨u, hu⟩ := iht keepT
      refine ⟨u, fun v inside => ?_⟩
      obtain ⟨sub, atom⟩ := hu v inside
      have no := cannotAbsorb s keepS v inside
      change _ ⊆ (WinnerSet.choice a (s.realize v) (t.realize v)).val ∧
        (_ = WinnerSet.singleton a ↔ WinnerSet.choice a (s.realize v) (t.realize v) = WinnerSet.singleton a)
      rw [WinnerSet.choice_comm (s.realize v) (t.realize v) a]
      refine ⟨sub.trans (WinnerSet.subset_choice_of_right_ne _ _ _ no), ?_⟩
      exact atom.trans ((or_iff_left no).symm.trans (WinnerSet.choice_eq_owner_iff _ _ _).symm)
    · by_cases own : r = a <;> simp [profile_choice, own, keepS, keepT] at positive

open Classical in
/-- Attaching a pointwise contained word with unanimous owner profile realizes the
baseline except on the face where every selected input is the owner's singleton. -/
theorem realize_choice_of_unanimous_profile {W : Type w} (a : Role) (ι : W → Var)
    (C : Equational.Term (Equational.CoreSymbol Role) Var)
    (g : Equational.Term (Equational.CoreSymbol Role) W)
    (bounded : ∀ v : Var → WinnerSet Role, (g.realize (v ∘ ι)).val ⊆ (C.realize v).val)
    (unanimous : ∀ B : W → Bool, profile a B g = true ↔ ∀ x, B x = true)
    (v : Var → WinnerSet Role) :
    (choiceTerm a C (g.relabel ι)).realize v =
      if ∀ x, v (ι x) = WinnerSet.singleton a then WinnerSet.singleton a else C.realize v := by
  change WinnerSet.choice a (C.realize v) ((g.relabel ι).realize v) = _
  rw [FirstOrder.Language.Term.realize_relabel]
  have atom : g.realize (v ∘ ι) = WinnerSet.singleton a ↔
      ∀ x, v (ι x) = WinnerSet.singleton a := by
    rw [winnerSet_eq_singleton_iff_profile, unanimous]
    simp only [Function.comp_apply, decide_eq_true_eq]
  by_cases face : ∀ x, v (ι x) = WinnerSet.singleton a
  · rw [ite_eq_left face]
    exact (WinnerSet.choice_eq_owner_iff _ _ _).mpr (Or.inr (atom.mpr face))
  · rw [ite_eq_right face]
    by_cases base : C.realize v = WinnerSet.singleton a
    · rw [base]
      exact (WinnerSet.choice_eq_owner_iff _ _ _).mpr (Or.inl rfl)
    · rw [WinnerSet.choice, ite_eq_right (not_or.mpr ⟨base, fun h => face (atom.mp h)⟩)]
      exact Subtype.ext (Set.union_eq_left.mpr (bounded v))

end KFOL.Core
