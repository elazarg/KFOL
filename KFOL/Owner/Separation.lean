module

public import KFOL.Owner.Guards

/-! # Explicit three-role, two-winner countervaluations for failed coverage -/

@[expose] public section

namespace KFOL.Owner

universe u v

private theorem not_ambiguous_singleton {Role : Type u} (r : Role) :
    ¬(WinnerSet.singleton r).Ambiguous := fun h => h r rfl

private theorem pair_ambiguous {Role : Type u} (a b : Role) :
    ((WinnerSet.singleton a).union (WinnerSet.singleton b)).Ambiguous ↔ a ≠ b := by
  constructor
  · intro h he
    subst b
    have hu : (WinnerSet.singleton a).union (WinnerSet.singleton a) = WinnerSet.singleton a := by
      apply Subtype.ext
      exact Set.union_self _
    exact h a hu
  · intro hab
    exact WinnerSet.ambiguous_of_two_mem _ a b hab (Or.inl rfl) (Or.inr rfl)

private theorem pair_eq_singleton {Role : Type u} (a b r : Role) :
    (WinnerSet.singleton a).union (WinnerSet.singleton b) = WinnerSet.singleton r ↔ a = r ∧ b = r := by
  rw [WinnerSet.union_eq_singleton_iff]
  simp only [WinnerSet.singleton_inj]

theorem minimalVal_ambiguous {Role : Type u} {Var : Type v} [DecidableEq Var]
    (observer other background : Role) (hko : observer ≠ other) (hob : other ≠ background)
    (g : Guard Var) (j : Var) :
    (minimalVal observer other background g j).Ambiguous ↔ j ∈ g.many := by
  by_cases hs : j = g.source <;> by_cases hm : j ∈ g.many <;> by_cases hn : j ∈ g.outside <;>
    simp_all [minimalVal, pair_ambiguous, not_ambiguous_singleton]

theorem minimalVal_outside {Role : Type u} {Var : Type v} [DecidableEq Var]
    (observer other background : Role) (hko : observer ≠ other) (hob : other ≠ background)
    (g : Guard Var) (j : Var) :
    minimalVal observer other background g j ≠ WinnerSet.singleton other ↔
      j ∈ g.many ∨ j ∈ g.outside ∨ j = g.source := by
  have hbo : background ≠ other := Ne.symm hob
  by_cases hs : j = g.source <;> by_cases hm : j ∈ g.many <;> by_cases hn : j ∈ g.outside <;>
    simp_all [minimalVal, pair_eq_singleton, WinnerSet.singleton_inj]

theorem minimalVal_marker {Role : Type u} {Var : Type v} [DecidableEq Var]
    (observer other background : Role) (hko : observer ≠ other) (hkb : observer ≠ background)
    (g : Guard Var) (j : Var) :
    observer ∈ (minimalVal observer other background g j).val ↔ j = g.source := by
  have hok : other ≠ observer := hko.symm
  have hbk : background ≠ observer := hkb.symm
  by_cases hs : j = g.source <;> by_cases hm : j ∈ g.many <;> by_cases hn : j ∈ g.outside <;>
    simp_all [minimalVal, WinnerSet.val_singleton, WinnerSet.val_union]

/-- Every countervaluation input is a union of two (possibly equal) atoms
chosen from the same three named roles. -/
theorem minimalVal_pair {Role : Type u} {Var : Type v} [DecidableEq Var]
    (observer other background : Role) (g : Guard Var) (j : Var) :
    ∃ a ∈ ({observer, other, background} : Set Role), ∃ b ∈ ({observer, other, background} : Set Role),
      minimalVal observer other background g j =
        (WinnerSet.singleton a).union (WinnerSet.singleton b) := by
  have hunion (a : Role) : (WinnerSet.singleton a).union (WinnerSet.singleton a) = WinnerSet.singleton a := by
    apply Subtype.ext
    exact Set.union_self _
  by_cases hs : j = g.source
  · subst j
    by_cases hm : g.source ∈ g.many
    · exact ⟨observer, by simp, other, by simp, by simp [minimalVal, hm]⟩
    · exact ⟨observer, by simp, observer, by simp, by simp only [minimalVal, ite_true, ite_eq_right hm, hunion]⟩
  · by_cases hm : j ∈ g.many
    · exact ⟨other, by simp, background, by simp, by simp [minimalVal, hs, hm]⟩
    · by_cases hn : j ∈ g.outside
      · exact ⟨background, by simp, background, by simp, by simp only [minimalVal, ite_eq_right hs, ite_eq_right hm, hn, ite_true, hunion]⟩
      · exact ⟨other, by simp, other, by simp, by simp only [minimalVal, ite_eq_right hs, ite_eq_right hm, hn, ite_false, hunion]⟩

theorem eval_minimalVal {Role : Type u} {Var : Type v} [DecidableEq Var]
    (observer other background : Role)
    (hko : observer ≠ other) (hkb : observer ≠ background) (hob : other ≠ background)
    (g : Guard Var) (guards : List (Guard Var)) :
    Eval guards (fun j => (minimalVal observer other background g j).Ambiguous)
      (fun j => minimalVal observer other background g j ≠ WinnerSet.singleton other)
      (fun j => observer ∈ (minimalVal observer other background g j).val) ↔
      ∃ h ∈ guards, h.Dominates g := by
  simp only [Eval, Guard.Holds, minimalVal_ambiguous observer other background hko hob,
    minimalVal_outside observer other background hko hob,
    minimalVal_marker observer other background hko hkb]
  constructor
  · rintro ⟨h, hh, hm, hn, hs⟩
    exact ⟨h, hh, hs, hm, hn⟩
  · rintro ⟨h, hh, hs, hm, hn⟩
    exact ⟨h, hh, hm, hn, hs⟩

/-- Pairwise coverage is exactly universal implication on winner-set inputs. -/
theorem covers_iff {Role : Type u} {Var : Type v} [DecidableEq Var]
    (observer other background : Role)
    (hko : observer ≠ other) (hkb : observer ≠ background) (hob : other ≠ background)
    (left right : List (Guard Var)) :
    Covers left right ↔ ∀ v : Var → WinnerSet Role,
      Eval left (fun j => (v j).Ambiguous) (fun j => v j ≠ WinnerSet.singleton other)
        (fun j => observer ∈ (v j).val) →
      Eval right (fun j => (v j).Ambiguous) (fun j => v j ≠ WinnerSet.singleton other)
        (fun j => observer ∈ (v j).val) := by
  constructor
  · intro h v
    apply covers_sound left right h
    · intro j hm he
      exact hm other he
    · intro j hj he
      rw [he] at hj
      exact hko hj
  · intro himp g hg
    let v := minimalVal observer other background g
    have hleft : Eval left (fun j => (v j).Ambiguous) (fun j => v j ≠ WinnerSet.singleton other)
        (fun j => observer ∈ (v j).val) := by
      apply (eval_minimalVal observer other background hko hkb hob g left).mpr
      exact ⟨g, hg, rfl, (fun _ h => h), fun j h => Or.inr (Or.inl h)⟩
    have hright := himp v hleft
    exact (eval_minimalVal observer other background hko hkb hob g right).mp hright

/-- A failed coverage test supplies the concrete minimal valuation of a
failed left guard; every input uses at most two of the named three roles. -/
theorem countervaluation_of_not_covers {Role : Type u} {Var : Type v} [DecidableEq Var]
    (observer other background : Role)
    (hko : observer ≠ other) (hkb : observer ≠ background) (hob : other ≠ background)
    (left right : List (Guard Var)) (h : ¬Covers left right) :
    ∃ g ∈ left,
      Eval left (fun j => (minimalVal observer other background g j).Ambiguous)
        (fun j => minimalVal observer other background g j ≠ WinnerSet.singleton other)
        (fun j => observer ∈ (minimalVal observer other background g j).val) ∧
      ¬Eval right (fun j => (minimalVal observer other background g j).Ambiguous)
        (fun j => minimalVal observer other background g j ≠ WinnerSet.singleton other)
        (fun j => observer ∈ (minimalVal observer other background g j).val) := by
  classical
  have hn : ¬∀ g ∈ left, ∃ q ∈ right, q.Dominates g := h
  push Not at hn
  obtain ⟨g, hg, hn⟩ := hn
  refine ⟨g, hg, ?_, ?_⟩
  · apply (eval_minimalVal observer other background hko hkb hob g left).mpr
    exact ⟨g, hg, rfl, (fun _ h => h), fun j h => Or.inr (Or.inl h)⟩
  · intro he
    obtain ⟨q, hq, hdom⟩ := (eval_minimalVal observer other background hko hkb hob g right).mp he
    exact hn q hq hdom

end KFOL.Owner
