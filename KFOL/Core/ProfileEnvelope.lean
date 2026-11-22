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

private theorem eval_suppress_of_no_trigger (roles : List Role)
    (bound t : Term Role Var) (v : Var → WinnerSet Role)
    (hle : (t.eval v).val ⊆ (bound.eval v).val)
    (h : ∀ r ∈ roles, t.eval v ≠ WinnerSet.singleton r) :
    (Term.suppress roles bound t).eval v = bound.eval v := by
  classical
  induction roles with
  | nil => rfl
  | cons r rest ih =>
    have ht := h r (List.mem_cons_self ..)
    have hb : bound.eval v ≠ WinnerSet.singleton r := by
      intro he
      exact ht (WinnerSet.eq_singleton_of_subset _ r (by simpa [he] using hle))
    simp only [Term.suppress, Term.eval, ih (fun s hs => h s (List.mem_cons_of_mem _ hs)),
      WinnerSet.choice, ht, hb, or_self, ite_false]
    exact Subtype.ext (Set.union_eq_left.mpr hle)

/-- Partial singleton profiles mask a core upper envelope only at the listed
owners. Any bounded operation that respects their winning tests is below the
mask, and the mask has exactly the witness's singleton tests at those owners. -/
theorem relative_partial_profile_maximum (roles : List Role)
    (bound t : Term Role Var) (hb : bound.IsCore) (ht : t.IsCore)
    (hle : ∀ v, (t.eval v).val ⊆ (bound.eval v).val) :
    ∃ e : Term Role Var, e.IsCore ∧
      (∀ v r, r ∈ roles → (e.eval v = WinnerSet.singleton r ↔
                            t.eval v = WinnerSet.singleton r)) ∧
      (∀ v, (∀ r ∈ roles, t.eval v ≠ WinnerSet.singleton r) → e.eval v = bound.eval v) ∧
      ∀ f : (Var → WinnerSet Role) → WinnerSet Role,
        (∀ v, (f v).val ⊆ (bound.eval v).val) →
        ((∀ v, (f v).val ⊆ (e.eval v).val) ↔
          ∀ v r, r ∈ roles → t.eval v = WinnerSet.singleton r → f v = WinnerSet.singleton r) := by
  classical
  let e := Term.suppress roles bound t
  have heCore : e.IsCore := by
    dsimp [e]
    induction roles with
    | nil => exact hb
    | cons r rest ih => exact ⟨ih, ht⟩
  have heAtom (v) (r) (hr : r ∈ roles) (h : t.eval v = WinnerSet.singleton r) :
      e.eval v = WinnerSet.singleton r :=
    Term.eval_suppress_atom roles bound t v r hr h
  have heOther (v) (h : ∀ r ∈ roles, t.eval v ≠ WinnerSet.singleton r) :
      e.eval v = bound.eval v :=
    eval_suppress_of_no_trigger roles bound t v (hle v) h
  refine ⟨e, heCore, ?_, heOther, ?_⟩
  · intro v r hr
    refine ⟨?_, heAtom v r hr⟩
    intro h
    by_cases hex : ∃ s ∈ roles, t.eval v = WinnerSet.singleton s
    · obtain ⟨s, hs, hts⟩ := hex
      exact hts.trans ((heAtom v s hs hts).symm.trans h)
    · have hv : ∀ s ∈ roles, t.eval v ≠ WinnerSet.singleton s :=
        fun s hs ht' => hex ⟨s, hs, ht'⟩
      have hbound : bound.eval v = WinnerSet.singleton r := (heOther v hv).symm.trans h
      exact WinnerSet.eq_singleton_of_subset _ r (by simpa [hbound] using hle v)
  · intro f hf
    constructor
    · intro h v r hr htr
      exact WinnerSet.eq_singleton_of_subset _ r (by simpa [heAtom v r hr htr] using h v)
    · intro h v
      by_cases hex : ∃ r ∈ roles, t.eval v = WinnerSet.singleton r
      · obtain ⟨r, hr, htr⟩ := hex
        rw [heAtom v r hr htr, h v r hr htr]
      · rw [heOther v (fun r hr htr => hex ⟨r, hr, htr⟩)]
        exact hf v

/-- A greatest witness for positive singleton demands agrees with the
unrestricted envelope wherever no listed owner is forced to be a singleton. -/
theorem positive_profile_envelope (roles : List Role) (bound t : Term Role Var)
    (demand : (Var → WinnerSet Role) → Role → Prop)
    (hroles : ∀ v r, demand v r → r ∈ roles)
    (hb : bound.IsCore) (ht : t.IsCore)
    (hle : ∀ v, (t.eval v).val ⊆ (bound.eval v).val)
    (hpass : ∀ v r, demand v r → t.eval v = WinnerSet.singleton r)
    (hgreatest : ∀ w : Term Role Var, w.IsCore →
      (∀ v, (w.eval v).val ⊆ (bound.eval v).val) →
      (∀ v r, demand v r → w.eval v = WinnerSet.singleton r) →
      ∀ v, (w.eval v).val ⊆ (t.eval v).val) :
    (∀ v r, t.eval v = WinnerSet.singleton r ↔
      ∀ w : Term Role Var, w.IsCore →
        (∀ u, (w.eval u).val ⊆ (bound.eval u).val) →
        (∀ u s, demand u s → w.eval u = WinnerSet.singleton s) →
        w.eval v = WinnerSet.singleton r) ∧
    ∀ v, (∀ r ∈ roles, t.eval v ≠ WinnerSet.singleton r) → t.eval v = bound.eval v := by
  obtain ⟨e, he, hprofiles, hother, hmaximum⟩ :=
    relative_partial_profile_maximum roles bound t hb ht hle
  have hmask_le (v) : (e.eval v).val ⊆ (bound.eval v).val := by
    by_cases hex : ∃ r ∈ roles, t.eval v = WinnerSet.singleton r
    · obtain ⟨r, hr, htr⟩ := hex
      rw [(hprofiles v r hr).mpr htr, ← htr]
      exact hle v
    · rw [hother v (fun r hr htr => hex ⟨r, hr, htr⟩)]
  have hmask_pass (v) (r) (hd : demand v r) : e.eval v = WinnerSet.singleton r :=
    (hprofiles v r (hroles v r hd)).mpr (hpass v r hd)
  have hmask_eq (v) : e.eval v = t.eval v :=
    Subtype.ext (Set.Subset.antisymm (hgreatest e he hmask_le hmask_pass v)
      (((hmaximum t.eval hle).mpr (fun _ _ _ h => h)) v))
  refine ⟨?_, fun v h => (hmask_eq v).symm.trans (hother v h)⟩
  intro v r
  constructor
  · intro h w hw hwle hwpass
    exact WinnerSet.eq_singleton_of_subset _ r (by simpa [h] using hgreatest w hw hwle hwpass v)
  · exact fun h => h t ht hle hpass

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
