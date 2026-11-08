module

public import KFOL.Algebra.Idempotent
public import KFOL.Definitions.Views
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Order.Setoid.Basic

/-! # Exact player views and the intrinsic subdirect representation -/

@[expose] public section

namespace KFOL

universe u v

namespace WinnerSet

variable {Role : Type u}

theorem mem_choice_owner (r : Role) (A B : WinnerSet Role) :
    r ∈ (choice r A B).val ↔ r ∈ A.val ∨ r ∈ B.val := by
  classical
  by_cases h : A = singleton r ∨ B = singleton r
  · have hm : r ∈ A.val ∨ r ∈ B.val :=
      h.elim (fun he => Or.inl (by simp [he])) (fun he => Or.inr (by simp [he]))
    simp [choice, h, hm]
  · simp only [choice, ite_eq_right h, val_union, Set.mem_union]

theorem mem_choice_other (r k : Role) (hrk : r ≠ k) (A B : WinnerSet Role) :
    k ∈ (choice r A B).val ↔
      (k ∈ A.val ∨ k ∈ B.val) ∧ A ≠ singleton r ∧ B ≠ singleton r := by
  classical
  by_cases h : A = singleton r ∨ B = singleton r
  · have hn : ¬(A ≠ singleton r ∧ B ≠ singleton r) :=
      fun hh => h.elim hh.1 hh.2
    simp [choice, h, Ne.symm hrk, hn]
  · have ha : A ≠ singleton r := fun he => h (Or.inl he)
    have hb : B ≠ singleton r := fun he => h (Or.inr he)
    simp [choice, ha, hb]

theorem SameView.choice {k : Role} {A B C D : WinnerSet Role}
    (hAC : SameView k A C) (hBD : SameView k B D) (r : Role) :
    SameView k (choice r A B) (choice r C D) := by
  constructor
  · by_cases hr : r = k
    · subst r
      rw [mem_choice_owner, mem_choice_owner]
      exact or_congr hAC.1 hBD.1
    · rw [mem_choice_other r k hr, mem_choice_other r k hr]
      exact and_congr (or_congr hAC.1 hBD.1)
        (and_congr (not_congr (hAC.2 r hr)) (not_congr (hBD.2 r hr)))
  · intro i hi
    by_cases hr : r = i
    · subst r
      rw [choice_eq_owner_iff, choice_eq_owner_iff]
      exact or_congr (hAC.2 i hi) (hBD.2 i hi)
    · rw [choice_eq_other_iff _ _ _ hr, choice_eq_other_iff _ _ _ hr]
      exact and_congr (hAC.2 i hi) (hBD.2 i hi)

@[simp] theorem view_eq_possible_iff (k : Role) (A : WinnerSet Role) :
    view k A = .possible ↔ k ∈ A.val := by
  classical
  unfold view
  split_ifs <;> simp_all

@[simp] theorem view_eq_other_iff (k : Role) (A : WinnerSet Role)
    (r : {r : Role // r ≠ k}) : view k A = .other r ↔ A = singleton r.val := by
  classical
  constructor
  · intro he
    by_cases hk : k ∈ A.val
    · simp [view, hk] at he
    · by_cases h : ∃ r, A = singleton r
      · simp only [view, dite_eq_right hk, dite_eq_left h] at he
        have hr := PlayerView.other.inj he
        exact h.choose_spec.trans (congrArg singleton (congrArg Subtype.val hr))
      · simp [view, hk, h] at he
  · rintro rfl
    have hk : k ∉ (singleton r.val).val := fun h => r.property h.symm
    have hw : ∃ s, singleton r.val = singleton s := ⟨r.val, rfl⟩
    simp only [view, dite_eq_right hk, dite_eq_left hw]
    congr 1
    apply Subtype.ext
    exact (singleton_inj.mp hw.choose_spec).symm

@[simp] theorem view_eq_impossible_iff (k : Role) (A : WinnerSet Role) :
    view k A = .impossible ↔ k ∉ A.val ∧ ∀ r, A ≠ singleton r := by
  classical
  unfold view
  split_ifs <;> simp_all

/-- The concrete view has exactly the independently specified observation kernel. -/
theorem view_eq_view_iff (k : Role) (A B : WinnerSet Role) :
    view k A = view k B ↔ SameView k A B := by
  constructor
  · intro h
    constructor
    · exact (view_eq_possible_iff k A).symm.trans
        ((congrArg (fun q => q = PlayerView.possible) h).to_iff.trans
          (view_eq_possible_iff k B))
    · intro r hr
      rw [← view_eq_other_iff k A ⟨r, hr⟩, ← view_eq_other_iff k B ⟨r, hr⟩, h]
  · intro h
    cases hA : view k A with
    | possible =>
      exact ((view_eq_possible_iff k B).mpr (h.1.mp
        ((view_eq_possible_iff k A).mp hA))).symm
    | other r =>
      exact ((view_eq_other_iff k B r).mpr
        ((h.2 r.val r.property).mp ((view_eq_other_iff k A r).mp hA))).symm
    | impossible =>
      obtain ⟨hk, ha⟩ := (view_eq_impossible_iff k A).mp hA
      symm
      apply (view_eq_impossible_iff k B).mpr
      refine ⟨fun hb => hk (h.1.mpr hb), ?_⟩
      intro r he
      by_cases hr : r = k
      · exact hk (h.1.mpr (by simp [he, hr]))
      · exact ha r ((h.2 r hr).mpr he)

end WinnerSet

namespace Term

variable {Role : Type u} {Var : Type v}

theorem IsCore.isPublic {t : Term Role Var} (ht : t.IsCore) : t.IsPublic := by
  induction t with
  | winner => exact False.elim ht
  | var => trivial
  | choice r s t hs ht' => exact ⟨hs ht.1, ht' ht.2⟩
  | rename => exact False.elim ht

/-- Congruence preservation for the public reduct, including winner constants. -/
theorem IsPublic.eval_sameView {t : Term Role Var} (ht : t.IsPublic) (k : Role)
    (v w : Var → WinnerSet Role) (h : ∀ x, WinnerSet.SameView k (v x) (w x)) :
    WinnerSet.SameView k (t.eval v) (t.eval w) := by
  induction t with
  | winner => exact ⟨Iff.rfl, fun _ _ => Iff.rfl⟩
  | var x => exact h x
  | choice r s t hs ht' => exact (hs ht.1).choice (ht' ht.2) r
  | rename => exact False.elim ht

/-- Public terms are closed under substitution of public expressions. -/
theorem IsPublic.subst {t : Term Role Var} (ht : t.IsPublic)
    {Var' : Type*} (replacement : Var → Term Role Var')
    (hr : ∀ x, (replacement x).IsPublic) : (t.subst replacement).IsPublic := by
  induction t with
  | winner => trivial
  | var x => exact hr x
  | choice r s t hs ht' => exact ⟨hs ht.1, ht' ht.2⟩
  | rename => exact False.elim ht

/-- Contextual equivalence in the public signature is exactly equality of views. -/
theorem contextual_iff_sameView (k : Role) (A B : WinnerSet Role) :
    (∀ t : Term Role Unit, t.IsPublic →
      (k ∈ (t.eval (fun _ => A)).val ↔ k ∈ (t.eval (fun _ => B)).val)) ↔
    WinnerSet.SameView k A B := by
  classical
  constructor
  · intro h
    refine ⟨h (.var ()) trivial, ?_⟩
    intro i hi
    have hc := h (.choice i (.var ()) (.winner k)) ⟨trivial, trivial⟩
    have hk : WinnerSet.singleton k ≠ WinnerSet.singleton i := by
      simpa using Ne.symm hi
    change k ∈ (WinnerSet.choice i A (WinnerSet.singleton k)).val ↔
      k ∈ (WinnerSet.choice i B (WinnerSet.singleton k)).val at hc
    rw [WinnerSet.mem_choice_other i k hi, WinnerSet.mem_choice_other i k hi] at hc
    have hn : A ≠ WinnerSet.singleton i ↔ B ≠ WinnerSet.singleton i :=
      ⟨fun ha => (hc.mp ⟨Or.inr rfl, ha, hk⟩).2.1,
        fun hb => (hc.mpr ⟨Or.inr rfl, hb, hk⟩).2.1⟩
    exact not_iff_not.mp hn
  · intro h t ht
    exact (ht.eval_sameView k (fun _ => A) (fun _ => B) (fun _ => h)).1

/-- Full unary polynomial contexts may use any finite list of arbitrary
winner-set parameters, besides their one varying input (`none`). -/
theorem polynomial_contextual_iff_sameView (k : Role) (A B : WinnerSet Role) :
    (∀ (n : ℕ) (t : Term Role (Option (Fin n))), t.IsPublic →
      ∀ parameters : Fin n → WinnerSet Role,
      (k ∈ (t.eval (fun x => x.elim A parameters)).val ↔
        k ∈ (t.eval (fun x => x.elim B parameters)).val)) ↔
    WinnerSet.SameView k A B := by
  constructor
  · intro h
    apply (contextual_iff_sameView k A B).mp
    intro t ht
    let replacement : Unit → Term Role (Option (Fin 0)) := fun _ => .var none
    have hp := h 0 (t.subst replacement) (ht.subst replacement (fun _ => trivial)) Fin.elim0
    simpa only [eval_subst, replacement, eval, Option.elim_none] using hp
  · intro h n t ht parameters
    apply (ht.eval_sameView k _ _ ?_).1
    intro x
    cases x with
    | none => exact h
    | some j => exact ⟨Iff.rfl, fun _ _ => Iff.rfl⟩

/-- Idempotent full-language operations inherit the public congruences. -/
theorem eval_sameView_of_idempotent (three : Fin 3 ↪ Role) (t : Term Role Var)
    (hd : ∀ A : WinnerSet Role, t.eval (fun _ => A) = A) (k : Role)
    (v w : Var → WinnerSet Role) (h : ∀ x, WinnerSet.SameView k (v x) (w x)) :
    WinnerSet.SameView k (t.eval v) (t.eval w) := by
  obtain ⟨hc, he, _⟩ := t.idempotent_extraction three hd
  rw [← he v, ← he w]
  exact hc.isPublic.eval_sameView k v w h


end Term

namespace PlayerView

variable {Role : Type u}

/-- Two distinguished states and one state for each other role. -/
def equivOption (k : Role) : PlayerView k ≃ Option (Option {r : Role // r ≠ k}) where
  toFun
    | .possible => none
    | .impossible => some none
    | .other r => some (some r)
  invFun
    | none => .possible
    | some none => .impossible
    | some (some r) => .other r
  left_inv q := by cases q <;> rfl
  right_inv q := by rcases q with _ | (_ | _) <;> rfl

/-- Count the concrete states by a bijection, independently of their realization. -/
theorem card (k : Role) [Fintype Role] :
    Nat.card (PlayerView k) = Fintype.card Role + 1 := by
  classical
  rw [Nat.card_congr (equivOption k), Nat.card_eq_fintype_card,
    Fintype.card_option, Fintype.card_option,
    Fintype.card_subtype_compl (fun r : Role => r = k), Fintype.card_subtype_eq]
  have hpos : 0 < Fintype.card Role := Fintype.card_pos_iff.mpr ⟨k⟩
  omega

/-- Canonical representatives realize every view. -/
@[simp] theorem view_representative (three : Fin 3 ↪ Role) (k : Role) (q : PlayerView k) :
    WinnerSet.view k (representative three k q) = q := by
  cases q with
  | possible => exact (WinnerSet.view_eq_possible_iff _ _).mpr rfl
  | other r => exact (WinnerSet.view_eq_other_iff _ _ r).mpr rfl
  | impossible =>
    apply (WinnerSet.view_eq_impossible_iff _ _).mpr
    obtain ⟨a, hak, _⟩ := exists_role_outside_pair three k k
    obtain ⟨b, hba, hbk⟩ := exists_role_outside_pair three a k
    exact ⟨fun h => h rfl, WinnerSet.ambiguous_of_two_mem _ a b hba.symm hak hbk⟩

end PlayerView

namespace Term

variable {Role : Type u} {Var : Type v}

/-- The operation induced on a view agrees with observing full evaluation. -/
theorem view_eval_of_idempotent (three : Fin 3 ↪ Role) (t : Term Role Var)
    (hd : ∀ A : WinnerSet Role, t.eval (fun _ => A) = A) (k : Role)
    (v : Var → WinnerSet Role) :
    WinnerSet.view k (t.eval v) =
      PlayerView.eval three k t (fun x => WinnerSet.view k (v x)) := by
  apply (WinnerSet.view_eq_view_iff k _ _).mpr
  apply t.eval_sameView_of_idempotent three hd k
  intro x
  exact (WinnerSet.view_eq_view_iff k _ _).mp
    (PlayerView.view_representative three k _).symm

/-- The same quotient construction applies to all public reduct terms. -/
theorem IsPublic.view_eval {t : Term Role Var} (ht : t.IsPublic)
    (three : Fin 3 ↪ Role) (k : Role) (v : Var → WinnerSet Role) :
    WinnerSet.view k (t.eval v) =
      PlayerView.eval three k t (fun x => WinnerSet.view k (v x)) := by
  apply (WinnerSet.view_eq_view_iff k _ _).mpr
  apply ht.eval_sameView k
  intro x
  exact (WinnerSet.view_eq_view_iff k _ _).mp
    (PlayerView.view_representative three k _).symm

end Term

namespace WinnerSet

variable {Role : Type u}

theorem view_surjective (three : Fin 3 ↪ Role) (k : Role) : Function.Surjective (view k) :=
  fun q => ⟨PlayerView.representative three k q, PlayerView.view_representative three k q⟩

/-- Count nonempty winner sets, rather than their syntactic representations. -/
theorem card_winnerSet [Fintype Role] :
    Nat.card (WinnerSet Role) = 2 ^ Fintype.card Role - 1 := by
  classical
  let e : WinnerSet Role ≃ {S : Set Role // S ≠ ∅} :=
    { toFun := fun A => ⟨A.val, A.property.ne_empty⟩
      invFun := fun A => ⟨A.val, Set.nonempty_iff_ne_empty.mpr A.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl (fun S : Set Role => S = ∅),
    Fintype.card_set, Fintype.card_subtype_eq]

/-- The contextual quotient has exactly the concrete view states. -/
noncomputable def quotientViewEquiv (three : Fin 3 ↪ Role) (k : Role) :
    Quotient (Setoid.ker (view k)) ≃ PlayerView k :=
  Setoid.quotientKerEquivOfSurjective (view k) (view_surjective three k)

theorem card_quotient_view [Fintype Role] (three : Fin 3 ↪ Role) (k : Role) :
    Nat.card (Quotient (Setoid.ker (view k))) = Fintype.card Role + 1 := by
  rw [Nat.card_congr (quotientViewEquiv three k), PlayerView.card]

/-- All player coordinates together recover the original winner set. -/
theorem views_injective : Function.Injective (fun A : WinnerSet Role => fun k => view k A) := by
  intro A B h
  apply Subtype.ext
  ext k
  exact ((view_eq_view_iff k A B).mp (congrFun h k)).1

/-- Omitting any one coordinate identifies two different winner sets. -/
theorem views_irredundant (three : Fin 3 ↪ Role) (k : Role) :
    ∃ A B : WinnerSet Role, A ≠ B ∧
      (∀ j, j ≠ k → view j A = view j B) ∧ view k A ≠ view k B := by
  let A := PlayerView.representative three k .impossible
  let B : WinnerSet Role := ⟨Set.univ, k, trivial⟩
  have hA : view k A = .impossible := PlayerView.view_representative three k _
  have hB : view k B = .possible := (view_eq_possible_iff _ _).mpr trivial
  have hne : view k A ≠ view k B := by rw [hA, hB]; intro h; cases h
  refine ⟨A, B, fun h => hne (congrArg (view k) h), ?_, hne⟩
  intro j hj
  have hAj : view j A = .possible := (view_eq_possible_iff _ _).mpr hj
  have hBj : view j B = .possible := (view_eq_possible_iff _ _).mpr trivial
  exact hAj.trans hBj.symm

end WinnerSet
end KFOL
