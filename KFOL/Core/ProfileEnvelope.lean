module

public import KFOL.Core.ProfileSynthesis
public import KFOL.Core.TernaryInterpolation
public import KFOL.Algebra.SemilatticeTrace
public import KFOL.Algebra.Atomic.CoreSupport
public import KFOL.Reset.Public

/-! # The greatest operation with prescribed singleton profiles

Resetting a profile witness against the union of all inputs retains its atomic
outputs and fills every ambiguous output with all available winners. This is
the maximum among all provenance-preserving operations with those profiles.
-/

@[expose] public section

namespace KFOL.Core

universe u v
variable {Role : Type u} {Var : Type v}

private def unionInputs (three : Fin 3 ↪ Role) (xs : List Var) (base : Var) : Term Role Var :=
  xs.foldr (fun j t => Term.unionTerm three (.var j) t) (.var base)

private theorem unionInputs_core (three : Fin 3 ↪ Role) (xs : List Var) (base : Var) :
    (unionInputs three xs base).IsCore := by
  induction xs with
  | nil => trivial
  | cons j xs ih => exact ⟨⟨trivial, ih⟩, ⟨trivial, ih⟩⟩

private theorem unionInputs_mem (three : Fin 3 ↪ Role) (xs : List Var) (base : Var)
    (v : Var → WinnerSet Role) (r : Role) :
    r ∈ ((unionInputs three xs base).eval v).val ↔
      r ∈ (v base).val ∨ ∃ j ∈ xs, r ∈ (v j).val := by
  induction xs with
  | nil => simp [unionInputs, Term.eval]
  | cons j xs ih =>
    change r ∈ ((Term.unionTerm three (.var j) (unionInputs three xs base)).eval v).val ↔ _
    rw [Term.eval_unionTerm]
    simp only [WinnerSet.val_union, Set.mem_union, Term.eval, ih,
      List.mem_cons, exists_eq_or_imp]
    tauto

/-- In the principal ideal below a core operation, completion of an attained
profile is right adjoint to taking singleton outputs, ordered by reverse
inclusion. The competing bounded operation can be arbitrary. -/
theorem relative_profile_maximum [Fintype Role] (three : Fin 3 ↪ Role)
    (bound t : Term Role Var) (hb : bound.IsCore) (ht : t.IsCore)
    (hle : ∀ v, (t.eval v).val ⊆ (bound.eval v).val) :
    ∃ e : Term Role Var, e.IsCore ∧
      (∀ v r, e.eval v = WinnerSet.singleton r ↔ t.eval v = WinnerSet.singleton r) ∧
      (∀ v, (t.eval v).Ambiguous → e.eval v = bound.eval v) ∧
      ∀ f : (Var → WinnerSet Role) → WinnerSet Role,
        (∀ v, (f v).val ⊆ (bound.eval v).val) →
          ((∀ v, (f v).val ⊆ (e.eval v).val) ↔
           ∀ v r, t.eval v = WinnerSet.singleton r → f v = WinnerSet.singleton r) := by
  classical
  let e := Reset.Term.resetTerm three Finset.univ.toList bound t
  have he (v : Var → WinnerSet Role) : e.eval v = (bound.eval v).reset (t.eval v) :=
    Reset.Term.eval_resetTerm three Finset.univ.toList (by simp) bound t v
  have ha (v : Var → WinnerSet Role) (h : (t.eval v).Ambiguous) : e.eval v = bound.eval v := by
    rw [he, WinnerSet.reset_of_ambiguous _ _ h]
    apply Subtype.ext
    exact Set.union_eq_left.mpr (hle v)
  have hs (v : Var → WinnerSet Role) (r : Role) :
      e.eval v = WinnerSet.singleton r ↔ t.eval v = WinnerSet.singleton r := by
    rw [he, WinnerSet.reset_eq_singleton]
  refine ⟨e, Reset.Term.isCore_resetTerm three _ _ _ hb ht, hs, ha, ?_⟩
  intro f hf
  constructor
  · intro h v r hr
    apply WinnerSet.eq_singleton_of_subset _ r
    simpa only [(hs v r).mpr hr, WinnerSet.val_singleton] using h v
  · intro h v
    by_cases hv : (t.eval v).Ambiguous
    · rw [ha v hv]
      exact hf v
    · obtain ⟨r, hr⟩ : ∃ r, t.eval v = WinnerSet.singleton r := by
        simpa only [WinnerSet.Ambiguous, not_forall, not_not] using hv
      rw [h v r hr, (hs v r).mpr hr]

/-- Every realizable singleton-profile family has a greatest provenance-
preserving completion, itself a core operation. All ambiguous outputs of the
completion are the union of all inputs. -/
theorem exists_profile_maximum [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (t : Term Role Var) (ht : t.IsCore) :
    ∃ e : Term Role Var, e.IsCore ∧
      (∀ v r, e.eval v = WinnerSet.singleton r ↔ t.eval v = WinnerSet.singleton r) ∧
      (∀ v, (t.eval v).Ambiguous → (e.eval v).val = ⋃ j, (v j).val) ∧
      ∀ f : (Var → WinnerSet Role) → WinnerSet Role,
        (∀ v, (f v).val ⊆ ⋃ j, (v j).val) →
        (∀ v r, f v = WinnerSet.singleton r ↔ t.eval v = WinnerSet.singleton r) →
        ∀ v, (f v).val ⊆ (e.eval v).val := by
  classical
  obtain ⟨base, _⟩ := ht.vars_nonempty
  let U := unionInputs three Finset.univ.toList base
  have hU (v : Var → WinnerSet Role) : (U.eval v).val = ⋃ j, (v j).val := by
    ext r
    change r ∈ ((unionInputs three Finset.univ.toList base).eval v).val ↔ _
    rw [unionInputs_mem]
    simp only [Finset.mem_toList, Finset.mem_univ, true_and, Set.mem_iUnion]
    exact ⟨fun h => h.elim (fun h => ⟨base, h⟩) id, fun h => Or.inr h⟩
  have htU (v : Var → WinnerSet Role) : (t.eval v).val ⊆ ⋃ j, (v j).val :=
    ht.eval_subset_of_support v _ (fun j _ r hr => Set.mem_iUnion.mpr ⟨j, hr⟩)
  obtain ⟨e, he, hs, ha, hmax⟩ := relative_profile_maximum three U t
    (unionInputs_core three _ _) ht (fun v => hU v ▸ htU v)
  refine ⟨e, he, hs, fun v hv => ha v hv ▸ hU v, ?_⟩
  intro f hf hprofile
  exact (hmax f (fun v => hU v ▸ hf v)).mpr fun v r => (hprofile v r).mpr

/-- Core operations in a fixed profile class need not be order-convex among
all operations in that class, even under all ternary relational tests. -/
theorem profile_fiber_nonconvex [Fintype Role] (three : Fin 3 ↪ Role) :
    ∃ s t : Term Role (Fin 3), s.IsCore ∧ t.IsCore ∧
      (∀ v r, s.eval v = WinnerSet.singleton r ↔ t.eval v = WinnerSet.singleton r) ∧
      (∀ v r, threewiseCounterexample three v = WinnerSet.singleton r ↔
        t.eval v = WinnerSet.singleton r) ∧
      (∀ v, (s.eval v).val ⊆ (threewiseCounterexample three v).val ∧
        (threewiseCounterexample three v).val ⊆ (t.eval v).val) ∧
      ¬∃ u : Term Role (Fin 3), u.IsCore ∧ ∀ v, u.eval v = threewiseCounterexample three v := by
  obtain ⟨s, hs, hlow, hsp⟩ := Threewise.counterexample_lower three
  obtain ⟨t, ht, htp, _, hmax⟩ := exists_profile_maximum three s hs
  have hprov (v : Fin 3 → WinnerSet Role) :
      (threewiseCounterexample three v).val ⊆ ⋃ j, (v j).val := by
    classical
    obtain ⟨u, hu, he⟩ := Threewise.counterexample_interpolable three (fun _ => v)
    rw [← he 0]
    exact hu.eval_subset_of_support v _ (fun j _ r hr => Set.mem_iUnion.mpr ⟨j, hr⟩)
  exact ⟨s, t, hs, ht, fun v r => (htp v r).symm,
    fun v r => (hsp v r).symm.trans (htp v r).symm,
    fun v => ⟨hlow v, hmax _ hprov (fun v r => (hsp v r).symm) v⟩,
    Threewise.counterexample_not_term three⟩

end KFOL.Core
