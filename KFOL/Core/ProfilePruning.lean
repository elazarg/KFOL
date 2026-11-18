module

public import KFOL.Core.ProfileSynthesis
public import KFOL.Algebra.ViewOrders.Monotone

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
