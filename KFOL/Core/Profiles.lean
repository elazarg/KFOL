module

public import KFOL.Core.Native

/-! # Uniform Boolean profiles and their common source -/

@[expose] public section

namespace KFOL.Core

universe u v w

variable {Role : Type u} [DecidableEq Role] {Var : Type v}

omit [DecidableEq Role] in
@[elab_as_elim] theorem induction_choice
    {P : Equational.Term (Equational.CoreSymbol Role) Var → Prop}
    (var : ∀ x, P (.var x))
    (choice : ∀ r s t, P s → P t → P (choiceTerm r s t))
    (t : Equational.Term (Equational.CoreSymbol Role) Var) : P t := by
  induction t with
  | var x => exact var x
  | @func n f args ih =>
    cases f with
    | choice r =>
      have he : FirstOrder.Language.Term.func (Equational.CoreSymbol.choice r) args =
          choiceTerm r (args 0) (args 1) := by
        congr 1
        funext i
        have hi : i = 0 ∨ i = 1 := by omega
        rcases hi with rfl | rfl <;> rfl
      rw [he]
      exact choice r _ _ (ih 0) (ih 1)

@[simp] theorem profile_var (i : Role) (v : Var → Bool) (x : Var) :
    profile i v (.var x) = v x := rfl

@[simp] theorem profile_choice (i r : Role) (v : Var → Bool)
    (s t : Equational.Term (Equational.CoreSymbol Role) Var) :
    profile i v (choiceTerm r s t) =
      if r = i then profile i v s || profile i v t else profile i v s && profile i v t := rfl

/-- Profiles are monotone Boolean functions, uniformly at arbitrary arity. -/
theorem profile_mono (i : Role) (v w : Var → Bool)
    (hvw : ∀ x, v x = true → w x = true)
    (t : Equational.Term (Equational.CoreSymbol Role) Var) :
    profile i v t = true → profile i w t = true := by
  induction t using induction_choice with
  | var x => exact hvw x
  | choice r s t hs ht =>
    by_cases hri : r = i
    · simp only [profile_choice, ite_eq_left hri, Bool.or_eq_true]
      exact fun h => h.imp hs ht
    · simp only [profile_choice, ite_eq_right hri, Bool.and_eq_true]
      exact fun h => ⟨hs h.1, ht h.2⟩

/-- Distinct owners' positive profiles have a shared actual variable leaf.
No finiteness or nonemptiness assumption on the family of owners is needed. -/
theorem profile_common_source {Index : Type w} (owners : Index → Role)
    (hinj : Function.Injective owners) (v : Index → Var → Bool)
    (t : Equational.Term (Equational.CoreSymbol Role) Var)
    (h : ∀ i, profile (owners i) (v i) t = true) :
    ∃ x : Var, ∀ i, v i x = true := by
  classical
  induction t using induction_choice with
  | var x => exact ⟨x, h⟩
  | choice r s t hs ht =>
    by_cases hr : ∃ i, owners i = r
    · obtain ⟨i, hi⟩ := hr
      have hor : profile (owners i) (v i) s = true ∨ profile (owners i) (v i) t = true := by
        simpa only [profile_choice, hi, ite_true, Bool.or_eq_true] using h i
      have hother (j : Index) (hji : j ≠ i) :
          profile (owners j) (v j) s = true ∧ profile (owners j) (v j) t = true := by
        have hrj : r ≠ owners j := by
          intro he
          exact hji (hinj (hi.trans he)).symm
        simpa only [profile_choice, ite_eq_right hrj, Bool.and_eq_true] using h j
      rcases hor with hi | hi
      · apply hs
        intro j
        by_cases hji : j = i
        · simpa only [hji] using hi
        · exact (hother j hji).1
      · apply ht
        intro j
        by_cases hji : j = i
        · simpa only [hji] using hi
        · exact (hother j hji).2
    · apply hs
      intro j
      have hrj : r ≠ owners j := fun he => hr ⟨j, he.symm⟩
      have hj : profile (owners j) (v j) s = true ∧ profile (owners j) (v j) t = true := by
        simpa only [profile_choice, ite_eq_right hrj, Bool.and_eq_true] using h j
      exact hj.1

attribute [local instance] Native.structureOf

/-- Profiles compute the exact atomic outputs in native algebras. -/
theorem realize_eq_atom_iff_profile (t : Equational.Term (Equational.CoreSymbol Role) Var)
    (i : Role) (v : Var → Native Role) :
    t.realize v = .atom i ↔ profile i (fun x => decide (v x = .atom i)) t = true := by
  induction t using induction_choice with
  | var x => simp
  | choice r s t hs ht =>
    change Native.choice r (s.realize v) (t.realize v) = .atom i ↔ _
    by_cases hri : r = i
    · subst r
      simp only [Native.choice_eq_atom_owner, profile_choice, ite_true, Bool.or_eq_true, hs, ht]
    · simp only [Native.choice_eq_atom_other r i hri, profile_choice, ite_eq_right hri,
        Bool.and_eq_true, hs, ht]

end KFOL.Core
