module

public import KFOL.Core.Locality
public import KFOL.Core.Profiles

/-! # Owner exhaustion and the uniform K+1-variable lower bound -/

@[expose] public section

namespace KFOL.Core

universe u v

variable {Role : Type u} [DecidableEq Role] {Var : Type v}

attribute [local instance] Native.structureOf Equational.coreStructure

omit [DecidableEq Role] in
@[simp] theorem realize_choice_winner (r : Role)
    (s t : Equational.Term (Equational.CoreSymbol Role) Var) (v : Var → WinnerSet Role) :
    (choiceTerm r s t).realize v = WinnerSet.choice r (s.realize v) (t.realize v) := rfl

@[simp] theorem realize_choice_native (r : Role)
    (s t : Equational.Term (Equational.CoreSymbol Role) Var) (v : Var → Native Role) :
    (choiceTerm r s t).realize v = Native.choice r (s.realize v) (t.realize v) := rfl

omit [DecidableEq Role] in
theorem realize_union_winner (three : Fin 3 ↪ Role)
    (s t : Equational.Term (Equational.CoreSymbol Role) Var) (v : Var → WinnerSet Role) :
    (unionTerm three s t).realize v = (s.realize v).union (t.realize v) := by
  unfold unionTerm
  simp only [realize_choice_winner]
  exact WinnerSet.three_owner_union _ _ _ _ _ (three.injective.ne (by decide))
    (three.injective.ne (by decide)) (three.injective.ne (by decide))

theorem realize_union_native (three : Fin 3 ↪ Role)
    (s t : Equational.Term (Equational.CoreSymbol Role) Var) (v : Var → Native Role) :
    (unionTerm three s t).realize v = Native.join (s.realize v) (t.realize v) := by
  unfold unionTerm
  simp only [realize_choice_native]
  exact Native.three_choice_join _ _ _ (three.injective.ne (by decide))
    (three.injective.ne (by decide)) (three.injective.ne (by decide)) _ _

omit [DecidableEq Role] in
theorem mem_exhaustionRight (three : Fin 3 ↪ Role) (roles : List Role)
    (v : Option Role → WinnerSet Role) (r : Role) (hr : r ∈ roles) :
    r ∈ (v none).val → r ∈ ((exhaustionRight three roles).realize v).val := by
  induction roles with
  | nil => simp at hr
  | cons k roles ih =>
    change r ∈ (v none).val → r ∈ ((unionTerm three
      (choiceTerm k (.var none) (.var (some k))) (exhaustionRight three roles)).realize v).val
    rw [realize_union_winner]
    intro hv
    rcases List.mem_cons.mp hr with rfl | hr
    · exact Or.inl ((WinnerSet.mem_choice_owner r _ _).mpr (Or.inl hv))
    · exact Or.inr (ih hr hv)

omit [DecidableEq Role] in
/-- Owner exhaustion is valid for arbitrary nonempty winner-set inputs. -/
theorem exhaustion_valid [Fintype Role] (three : Fin 3 ↪ Role) :
    (exhaustionIdentity three).Holds (WinnerSet Role) := by
  unfold Equational.Identity.Holds exhaustionIdentity
  intro v
  simp only [FirstOrder.Language.Term.realize_relabel]
  rw [realize_union_winner]
  apply Subtype.ext
  ext r
  constructor
  · rintro (hr | hr)
    · exact mem_exhaustionRight three Finset.univ.toList _ r (by simp) hr
    · exact hr
  · exact Or.inr

private def nativeValuation : Option Role → Native Role
  | none => .upper
  | some r => .atom r

private theorem native_summand (r : Role) :
    (choiceTerm r (.var none) (.var (some r))).realize (nativeValuation (Role := Role)) =
      Native.atom r := by
  change Native.choice r .upper (.atom r) = .atom r
  simp [Native.choice]

private theorem native_right_spec (three : Fin 3 ↪ Role) (roles : List Role) :
    (exhaustionRight three roles).realize (nativeValuation (Role := Role)) ≠ .upper ∧
      ∀ i, (exhaustionRight three roles).realize (nativeValuation (Role := Role)) = .atom i ↔
        three 0 = i ∧ ∀ r ∈ roles, r = i := by
  induction roles with
  | nil =>
    have he : exhaustionRight three [] =
        choiceTerm (three 0) (.var none) (.var (some (three 0))) := rfl
    rw [he, native_summand]
    simp
  | cons r roles ih =>
    have he : exhaustionRight three (r :: roles) = unionTerm three
        (choiceTerm r (.var none) (.var (some r))) (exhaustionRight three roles) := rfl
    rw [he, realize_union_native, native_summand]
    constructor
    · simp [ih.1]
    · intro i
      rw [Native.join_eq_atom, ih.2]
      simp only [Native.atom.injEq, List.mem_cons, forall_eq_or_imp]
      tauto

private theorem native_right_lower [Fintype Role] (three : Fin 3 ↪ Role) :
    (exhaustionRight three Finset.univ.toList).realize (nativeValuation (Role := Role)) =
      Native.lower := by
  have hs := native_right_spec three Finset.univ.toList
  apply Native.ext_atoms_upper
  · intro i
    simp only [reduceCtorEq, iff_false]
    intro hi
    obtain ⟨h0, hall⟩ := (hs.2 i).mp hi
    exact three.injective.ne (show (0 : Fin 3) ≠ 1 by decide) (h0.trans (hall (three 1) (by simp)).symm)
  · simp [hs.1]

/-- The same explicit core equation fails in the native K+2-element algebra. -/
theorem exhaustion_not_valid [Fintype Role] (three : Fin 3 ↪ Role) :
    ¬(exhaustionIdentity three).Holds (Native Role) := by
  intro h
  let v : Fin (Fintype.card (Option Role)) → Native Role :=
    nativeValuation ∘ (Fintype.equivFin (Option Role)).symm
  have he := h v
  simp only [exhaustionIdentity, FirstOrder.Language.Term.realize_relabel] at he
  have hv : v ∘ Fintype.equivFin (Option Role) = nativeValuation := by
    funext x
    simp only [v, Function.comp_apply, Equiv.symm_apply_apply]
  rw [hv, realize_union_native, native_right_lower] at he
  change Native.join .upper .lower = .lower at he
  simp [Native.join] at he

theorem native_not_inVariety [Fintype Role] (three : Fin 3 ↪ Role) :
    ¬Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) (Native Role) :=
  fun h => exhaustion_not_valid three (h.2 _ (exhaustion_valid three))

/-- The separating equation uses exactly K+1 actual variables after its
derived union has been fully expanded into owned-choice syntax. -/
theorem exhaustion_variableCount [Fintype Role] (three : Fin 3 ↪ Role) :
    (exhaustionIdentity three).variableCount = Fintype.card Role + 1 := by
  have hc := Finset.card_le_univ (exhaustionIdentity three).support
  rw [Fintype.card_fin] at hc
  change (exhaustionIdentity three).variableCount ≤ (exhaustionIdentity three).arity at hc
  change (exhaustionIdentity three).variableCount ≤ Fintype.card (Option Role) at hc
  rw [Fintype.card_option] at hc
  have hn : ¬(exhaustionIdentity three).variableCount ≤ Fintype.card Role := by
    intro hsmall
    exact exhaustion_not_valid three (Native.holds_of_variableCount_le three _ hsmall
      (exhaustion_valid three))
  omega

/-- No set of identities using at most K actual variables, even an infinite
one, is a basis for the K-owner core. -/
theorem no_basis_with_role_bound [Fintype Role] (three : Fin 3 ↪ Role)
    (T : Equational.Theory (Equational.CoreSymbol Role))
    (hT : Equational.HasVariableBound T (Fintype.card Role)) :
    ¬Equational.IsBasis (WinnerSet Role) T := by
  intro hb
  have hm : Equational.Models T (Native Role) := by
    intro e he
    exact Native.holds_of_variableCount_le three e (hT e he) (hb.models e he)
  have : Nonempty (Native Role) := ⟨.lower⟩
  exact native_not_inVariety three (hb.inVariety hm)

/-- Every basis therefore contains an equation with at least K+1 actual
variables, rather than merely a presentation of that declared arity. -/
theorem exists_large_identity_of_basis [Fintype Role] (three : Fin 3 ↪ Role)
    (T : Equational.Theory (Equational.CoreSymbol Role))
    (hT : Equational.IsBasis (WinnerSet Role) T) :
    ∃ e ∈ T, Fintype.card Role + 1 ≤ e.variableCount := by
  classical
  by_contra hn
  push Not at hn
  apply no_basis_with_role_bound three T _ hT
  intro e he
  have hh := hn e he
  omega

end KFOL.Core
