module

public import KFOL.Algebra.SemilatticeTrace
public import KFOL.Definitions.Views
public import KFOL.Reset.Public

/-! # Removing a neutral source from core terms

A temporary source can carry a ghost which no original owner can absorb on its
own. Its ordinary residue is again a core term. The public statement reads the
residue through the canonical complement sections, without extending the public
signature or adding a winner constant.
-/

@[expose] public section

namespace KFOL.Core

universe u v
variable {Role : Type u} {Var : Type v}

private structure Trace (Role : Type u) where
  marked : Bool
  ordinary : Set Role

private noncomputable def traceChoice (r : Role) (x y : Trace Role) : Trace Role :=
  if (x.marked = false ∧ x.ordinary = {r}) ∨
      (y.marked = false ∧ y.ordinary = {r}) then
    ⟨false, {r}⟩
  else ⟨x.marked || y.marked, x.ordinary ∪ y.ordinary⟩

private noncomputable def trace (v : Var → WinnerSet Role) :
    Term Role (Option Var) → Trace Role
  | .winner r => ⟨false, {r}⟩
  | .var none => ⟨true, ∅⟩
  | .var (some j) => ⟨false, (v j).val⟩
  | .choice r s t => traceChoice r (trace v s) (trace v t)
  | .rename p t => ⟨(trace v t).marked, p '' (trace v t).ordinary⟩

private structure Compares (z : Trace Role) (A B : WinnerSet Role) : Prop where
  constant : z.marked = false → B.val = z.ordinary
  lower : z.marked = true → A.val ⊆ B.val
  upper : B.val ⊆ A.val ∪ z.ordinary
  ambiguous : A.Ambiguous →
    B.val = if z.marked then A.val ∪ z.ordinary else z.ordinary

private theorem compares_choice (r : Role) (x y : Trace Role)
    (A B C : WinnerSet Role) (hx : Compares x A B) (hy : Compares y A C) :
    Compares (traceChoice r x y) A (WinnerSet.choice r B C) := by
  classical
  by_cases habs : (x.marked = false ∧ x.ordinary = {r}) ∨
      (y.marked = false ∧ y.ordinary = {r})
  · have he : WinnerSet.choice r B C = WinnerSet.singleton r := by
      apply (WinnerSet.choice_eq_owner_iff _ _ _).mpr
      rcases habs with h | h
      · exact Or.inl (Subtype.ext ((hx.constant h.1).trans h.2))
      · exact Or.inr (Subtype.ext ((hy.constant h.1).trans h.2))
    rw [he]
    simp only [traceChoice, ite_eq_left habs]
    refine ⟨fun _ => rfl, ?_, Set.subset_union_right, fun _ => rfl⟩
    simp
  · have hBx : x.marked = false → B ≠ WinnerSet.singleton r := by
      intro hm he
      apply habs
      exact Or.inl ⟨hm, (hx.constant hm).symm.trans (congrArg Subtype.val he)⟩
    have hCy : y.marked = false → C ≠ WinnerSet.singleton r := by
      intro hm he
      apply habs
      exact Or.inr ⟨hm, (hy.constant hm).symm.trans (congrArg Subtype.val he)⟩
    by_cases hreal : B = WinnerSet.singleton r ∨ C = WinnerSet.singleton r
    · have hm : (traceChoice r x y).marked = true := by
        simp only [traceChoice, ite_eq_right habs]
        rcases hreal with h | h
        · have : x.marked = true := Bool.eq_true_of_not_eq_false (fun hf => hBx hf h)
          simp [this]
        · have : y.marked = true := Bool.eq_true_of_not_eq_false (fun hf => hCy hf h)
          simp [this]
      have hA : A = WinnerSet.singleton r := by
        apply WinnerSet.eq_singleton_of_subset
        rcases hreal with h | h
        · have ht : x.marked = true := Bool.eq_true_of_not_eq_false (fun hf => hBx hf h)
          simpa only [h, WinnerSet.val_singleton] using hx.lower ht
        · have ht : y.marked = true := Bool.eq_true_of_not_eq_false (fun hf => hCy hf h)
          simpa only [h, WinnerSet.val_singleton] using hy.lower ht
      have he : WinnerSet.choice r B C = WinnerSet.singleton r :=
        (WinnerSet.choice_eq_owner_iff _ _ _).mpr hreal
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [hm]
      · intro _; rw [he, hA]
      · rw [he, hA]; exact Set.subset_union_left
      · intro ha; exact (ha r hA).elim
    · have he : (WinnerSet.choice r B C).val = B.val ∪ C.val := by
        simp only [WinnerSet.choice, ite_eq_right hreal, WinnerSet.val_union]
      have ht : traceChoice r x y = ⟨x.marked || y.marked, x.ordinary ∪ y.ordinary⟩ :=
        ite_eq_right habs
      rw [ht]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro hm
        have hxf : x.marked = false := by simpa using (Bool.or_eq_false_iff.mp hm).1
        have hyf : y.marked = false := by simpa using (Bool.or_eq_false_iff.mp hm).2
        rw [he, hx.constant hxf, hy.constant hyf]
      · intro hm
        rcases Bool.or_eq_true_iff.mp hm with hm | hm
        · exact (hx.lower hm).trans (he ▸ Set.subset_union_left)
        · exact (hy.lower hm).trans (he ▸ Set.subset_union_right)
      · rw [he]
        intro k hk
        rcases hk with hk | hk
        · rcases hx.upper hk with hk | hk
          · exact Or.inl hk
          · exact Or.inr (Or.inl hk)
        · rcases hy.upper hk with hk | hk
          · exact Or.inl hk
          · exact Or.inr (Or.inr hk)
      · intro ha
        rw [he, hx.ambiguous ha, hy.ambiguous ha]
        cases hxm : x.marked <;> cases hym : y.marked <;>
          simp [Set.union_left_comm, Set.union_comm]

private theorem trace_compares (t : Term Role (Option Var)) (ht : t.IsCore)
    (v : Var → WinnerSet Role) (A : WinnerSet Role) :
    Compares (trace v t) A (t.eval (fun j => j.elim A v)) := by
  induction t with
  | winner => exact ht.elim
  | rename => exact ht.elim
  | var j =>
    cases j with
    | none =>
      refine ⟨by simp [trace], fun _ => Set.Subset.rfl, ?_, ?_⟩
      · simp [Term.eval, trace]
      · intro _; simp [Term.eval, trace]
    | some j =>
      refine ⟨fun _ => rfl, by simp [trace], Set.subset_union_right, fun _ => rfl⟩
  | choice r s t ihs iht =>
    exact compares_choice r _ _ _ _ _ (ihs ht.1) (iht ht.2)

private theorem trace_nonempty (t : Term Role (Option Var)) (ht : t.IsCore)
    (v : Var → WinnerSet Role) (A : WinnerSet Role) :
    (trace v t).marked = true ∨ (trace v t).ordinary.Nonempty := by
  by_cases hm : (trace v t).marked = false
  · right
    rw [← (trace_compares t ht v A).constant hm]
    exact (t.eval (fun j => j.elim A v)).property
  · exact Or.inl (Bool.eq_true_of_not_eq_false hm)

private def replace (t : Term Role (Option Var)) (g : Term Role Var) : Term Role Var :=
  t.subst (fun j => j.elim g Term.var)

private def eliminate (three : Fin 3 ↪ Role) :
    Term Role (Option Var) → Option (Term Role Var)
  | .winner _ | .rename _ _ => none
  | .var none => none
  | .var (some j) => some (.var j)
  | .choice r s t => match eliminate three s, eliminate three t with
    | none, z => z
    | z, none => z
    | some g, some h => some (.choice r
        (Term.unionTerm three g (replace s h))
        (Term.unionTerm three h (replace t g)))

private theorem replace_core (t : Term Role (Option Var)) (ht : t.IsCore)
    (g : Term Role Var) (hg : g.IsCore) : (replace t g).IsCore := by
  classical
  unfold replace
  apply ht.subst
  intro j _
  cases j <;> simp [Option.elim, hg, Term.IsCore]

private theorem eliminate_core (three : Fin 3 ↪ Role)
    (t : Term Role (Option Var)) (ht : t.IsCore) :
    ∀ g, eliminate three t = some g → g.IsCore := by
  induction t with
  | winner => exact ht.elim
  | rename => exact ht.elim
  | var j => cases j <;> simp [eliminate, Term.IsCore]
  | choice r s t ihs iht =>
    cases hs : eliminate three s with
    | none =>
      cases ht' : eliminate three t with
      | none => simp [eliminate, hs, ht']
      | some h =>
        intro g he
        have : h = g := by simpa [eliminate, hs, ht'] using he
        subst g
        exact iht ht.2 h ht'
    | some g =>
      cases ht' : eliminate three t with
      | none =>
        intro h he
        have : g = h := by simpa [eliminate, hs, ht'] using he
        subst h
        exact ihs ht.1 g hs
      | some h =>
        intro z he
        have hz : Term.choice r (Term.unionTerm three g (replace s h))
            (Term.unionTerm three h (replace t g)) = z := by
          simpa [eliminate, hs, ht'] using he
        subst z
        have hg := ihs ht.1 g hs
        have hh := iht ht.2 h ht'
        simp [Term.IsCore, Term.unionTerm, hg, hh,
          replace_core s ht.1 h hh, replace_core t ht.2 g hg]

private theorem val_eq_singleton (A : WinnerSet Role) (r : Role) :
    A.val = {r} ↔ A = WinnerSet.singleton r :=
  ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

private theorem choice_union_right (r : Role) (A B : WinnerSet Role) :
    WinnerSet.choice r A (A.union B) =
      if A = WinnerSet.singleton r then A else A.union B := by
  classical
  by_cases ha : A = WinnerSet.singleton r
  · simp [WinnerSet.choice, ha]
  · have hu : A.union B ≠ WinnerSet.singleton r :=
      fun h => ha ((WinnerSet.union_eq_singleton_iff A B r).mp h).1
    rw [WinnerSet.choice, ite_eq_right (not_or.mpr ⟨ha, hu⟩), ite_eq_right ha]
    apply Subtype.ext
    ext k
    simp only [WinnerSet.val_union, Set.mem_union]
    tauto

private theorem choice_union_left (r : Role) (A B : WinnerSet Role) :
    WinnerSet.choice r (A.union B) B =
      if B = WinnerSet.singleton r then B else A.union B := by
  rw [WinnerSet.choice_comm, WinnerSet.union_comm A B, choice_union_right]

private theorem traceChoice_ordinary (r : Role) (x y : Trace Role)
    (g h : WinnerSet Role) (hg : x.ordinary = g.val) (hh : y.ordinary = h.val) :
    (traceChoice r x y).ordinary =
      (WinnerSet.choice r (if x.marked then g.union h else g)
        (if y.marked then g.union h else h)).val := by
  classical
  cases hx : x.marked <;> cases hy : y.marked
  · by_cases hab : g = WinnerSet.singleton r ∨ h = WinnerSet.singleton r <;>
      simp [traceChoice, hx, hy, hg, hh, val_eq_singleton, WinnerSet.choice, hab]
  · by_cases hab : g = WinnerSet.singleton r <;>
      simp [traceChoice, hx, hy, hg, hh, val_eq_singleton, choice_union_right, hab]
  · by_cases hab : h = WinnerSet.singleton r <;>
      simp [traceChoice, hx, hy, hg, hh, val_eq_singleton, choice_union_left, hab]
  · simp [traceChoice, hx, hy, hg, hh, WinnerSet.choice_self]

private theorem compares_union (z : Trace Role) (A B C : WinnerSet Role)
    (hc : C.val = z.ordinary) (h : Compares z A B) :
    C.union B = if z.marked then C.union A else C := by
  cases hm : z.marked
  · apply Subtype.ext
    simp only [Bool.false_eq_true, ite_false, WinnerSet.val_union]
    rw [h.constant hm, ← hc, Set.union_self]
  · apply Subtype.ext
    change C.val ∪ B.val = C.val ∪ A.val
    ext k
    constructor
    · rintro (hk | hk)
      · exact Or.inl hk
      · rcases h.upper hk with hk | hk
        · exact Or.inr hk
        · exact Or.inl (hc ▸ hk)
    · rintro (hk | hk)
      · exact Or.inl hk
      · exact Or.inr (h.lower hm hk)

private theorem residual_choice (r : Role) (x y : Trace Role)
    (g h U V : WinnerSet Role) (hg : x.ordinary = g.val) (hh : y.ordinary = h.val)
    (hU : Compares x h U) (hV : Compares y g V) :
    (traceChoice r x y).ordinary =
      (WinnerSet.choice r (g.union U) (h.union V)).val := by
  rw [compares_union x h U g hg.symm hU, compares_union y g V h hh.symm hV]
  rw [WinnerSet.union_comm h g]
  exact traceChoice_ordinary r x y g h hg hh

private theorem traceChoice_zero_left (r : Role) (y : Trace Role) :
    (traceChoice r ⟨true, ∅⟩ y).ordinary = y.ordinary := by
  classical
  by_cases h : y.marked = false ∧ y.ordinary = {r}
  · simp [traceChoice, h]
  · simp [traceChoice, h]

private theorem traceChoice_zero_right (r : Role) (x : Trace Role) :
    (traceChoice r x ⟨true, ∅⟩).ordinary = x.ordinary := by
  classical
  by_cases h : x.marked = false ∧ x.ordinary = {r}
  · simp [traceChoice, h]
  · simp [traceChoice, h]

private theorem eval_replace (t : Term Role (Option Var)) (g : Term Role Var)
    (v : Var → WinnerSet Role) :
    (replace t g).eval v = t.eval (fun j => j.elim (g.eval v) v) := by
  rw [replace, Term.eval_subst]
  congr 1
  funext j
  cases j <;> rfl

private theorem eliminate_sound (three : Fin 3 ↪ Role)
    (t : Term Role (Option Var)) (ht : t.IsCore) (v : Var → WinnerSet Role) :
    (trace v t).ordinary =
      (eliminate three t).elim ∅ (fun g => (g.eval v).val) := by
  classical
  induction t with
  | winner => exact ht.elim
  | rename => exact ht.elim
  | var j => cases j <;> rfl
  | choice r s t ihs iht =>
    cases hs : eliminate three s with
    | none =>
      have hse : (trace v s).ordinary = ∅ := by simpa only [hs, Option.elim_none] using ihs ht.1
      have hsm : (trace v s).marked = true := by
        rcases trace_nonempty s ht.1 v (WinnerSet.singleton (three 0)) with h | h
        · exact h
        · simp only [hse, Set.not_nonempty_empty] at h
      have hsz : trace v s = ⟨true, ∅⟩ := by
        cases he : trace v s with
        | mk m C => simp_all
      simp only [trace, hsz, traceChoice_zero_left, eliminate, hs]
      exact iht ht.2
    | some g =>
      cases hh : eliminate three t with
      | none =>
        have hte : (trace v t).ordinary = ∅ := by simpa only [hh, Option.elim_none] using iht ht.2
        have htm : (trace v t).marked = true := by
          rcases trace_nonempty t ht.2 v (WinnerSet.singleton (three 0)) with h | h
          · exact h
          · simp only [hte, Set.not_nonempty_empty] at h
        have htz : trace v t = ⟨true, ∅⟩ := by
          cases he : trace v t with
          | mk m C => simp_all
        simp only [trace, htz, traceChoice_zero_right, eliminate, hs, hh, Option.elim_some]
        simpa only [hs, Option.elim_some] using ihs ht.1
      | some h =>
        have hsg : (trace v s).ordinary = (g.eval v).val := by
          simpa only [hs, Option.elim_some] using ihs ht.1
        have hth : (trace v t).ordinary = (h.eval v).val := by
          simpa only [hh, Option.elim_some] using iht ht.2
        simp only [trace, eliminate, hs, hh, Option.elim_some,
          Term.eval, Term.eval_unionTerm]
        apply residual_choice r _ _ _ _ _ _ hsg hth
        · rw [eval_replace]
          exact trace_compares s ht.1 v (h.eval v)
        · rw [eval_replace]
          exact trace_compares t ht.2 v (g.eval v)

private theorem complement_ambiguous (three : Fin 3 ↪ Role) (k : Role) :
    (PlayerView.representative three k .impossible).Ambiguous := by
  intro r he
  obtain ⟨q, hqk, hqr⟩ := exists_role_outside_pair three k r
  have hq : q ∈ (PlayerView.representative three k .impossible).val := hqk
  rw [he] at hq
  exact hqr hq

private theorem section_trace (three : Fin 3 ↪ Role)
    (t : Term Role (Option Var)) (ht : t.IsCore)
    (v : Var → WinnerSet Role) (k : Role) :
    k ∈ (t.eval (fun j => j.elim (PlayerView.representative three k .impossible) v)).val ↔
      k ∈ (trace v t).ordinary := by
  rw [(trace_compares t ht v _).ambiguous (complement_ambiguous three k)]
  cases hm : (trace v t).marked <;>
    simp [PlayerView.representative]

/-- Deleting a temporary source leaves either zero or a genuine core operation.
Its ordinary membership bits are read by setting the temporary input to the
complement of the observed owner. No term over an extended role carrier is
needed in this interface. -/
theorem exists_optional_core_residual (three : Fin 3 ↪ Role)
    (t : Term Role (Option Var)) (ht : t.IsCore) :
    ∃ g : Option (Term Role Var), (∀ s, g = some s → s.IsCore) ∧
      ∀ (v : Var → WinnerSet Role) (k : Role),
        (∃ s, g = some s ∧ k ∈ (s.eval v).val) ↔
          k ∈ (t.eval (fun j =>
            j.elim (PlayerView.representative three k .impossible) v)).val := by
  refine ⟨eliminate three t, eliminate_core three t ht, ?_⟩
  intro v k
  rw [section_trace three t ht, eliminate_sound three t ht]
  cases eliminate three t <;> simp

/-- The zero case and the core-residual case form an exhaustive alternative. -/
theorem core_residual_alternative (three : Fin 3 ↪ Role)
    (t : Term Role (Option Var)) (ht : t.IsCore) :
    (∀ (v : Var → WinnerSet Role) (k : Role),
      k ∉ (t.eval (fun j =>
        j.elim (PlayerView.representative three k .impossible) v)).val) ∨
    ∃ g : Term Role Var, g.IsCore ∧ ∀ (v : Var → WinnerSet Role) (k : Role),
      k ∈ (g.eval v).val ↔ k ∈ (t.eval (fun j =>
        j.elim (PlayerView.representative three k .impossible) v)).val := by
  obtain ⟨g, hg, he⟩ := exists_optional_core_residual three t ht
  cases g with
  | none => left; simpa using he
  | some g => exact Or.inr ⟨g, hg g rfl, by simpa using he⟩

private theorem eliminate_some_of_mem [DecidableEq Var] (three : Fin 3 ↪ Role)
    (t : Term Role (Option Var)) (ht : t.IsCore) (j : Var)
    (hj : some j ∈ t.vars) : ∃ g, eliminate three t = some g := by
  induction t with
  | winner => exact ht.elim
  | rename => exact ht.elim
  | var i =>
    have hi : some j = i := Finset.mem_singleton.mp hj
    subst i
    exact ⟨.var j, rfl⟩
  | choice r s t ihs iht =>
    rcases Finset.mem_union.mp hj with hj | hj
    · obtain ⟨g, hg⟩ := ihs ht.1 hj
      cases hh : eliminate three t <;> simp [eliminate, hg, hh]
    · obtain ⟨h, hh⟩ := iht ht.2 hj
      cases hg : eliminate three s <;> simp [eliminate, hg, hh]

/-- If an ordinary variable occurs, the residual is nonempty and is represented
by a core term on the remaining variables. -/
theorem exists_core_residual [DecidableEq Var] (three : Fin 3 ↪ Role)
    (t : Term Role (Option Var)) (ht : t.IsCore)
    (hused : ∃ j, some j ∈ t.vars) :
    ∃ g : Term Role Var, g.IsCore ∧ ∀ (v : Var → WinnerSet Role) (k : Role),
      k ∈ (g.eval v).val ↔ k ∈ (t.eval (fun j =>
        j.elim (PlayerView.representative three k .impossible) v)).val := by
  obtain ⟨j, hj⟩ := hused
  obtain ⟨g, hg⟩ := eliminate_some_of_mem three t ht j hj
  refine ⟨g, eliminate_core three t ht g hg, ?_⟩
  intro v k
  rw [section_trace three t ht, eliminate_sound three t ht, hg]
  rfl

private theorem marked_of_projection (three : Fin 3 ↪ Role)
    (t : Term Role (Option Var)) (ht : t.IsCore) (v : Var → WinnerSet Role)
    (hp : ∀ r, t.eval (fun j => j.elim (WinnerSet.singleton r) v) = WinnerSet.singleton r) :
    (trace v t).marked = true := by
  apply Bool.eq_true_of_not_eq_false
  intro hm
  have h0 := (trace_compares t ht v (WinnerSet.singleton (three 0))).constant hm
  have h1 := (trace_compares t ht v (WinnerSet.singleton (three 1))).constant hm
  rw [hp] at h0 h1
  have he : WinnerSet.singleton (three 0) = WinnerSet.singleton (three 1) :=
    Subtype.ext (h0.trans h1.symm)
  exact (three.injective.ne (by decide : (0 : Fin 3) ≠ 1))
    (WinnerSet.singleton_inj.mp he)

/-- The full projection-profile fiber consists precisely of the distinguished
projection and resets of lower-arity core operations. -/
theorem projection_fiber_iff (three : Fin 3 ↪ Role)
    (t : Term Role (Option Var)) (ht : t.IsCore) :
    (∀ (v : Var → WinnerSet Role) (A : WinnerSet Role) (r : Role),
      t.eval (fun j => j.elim A v) = WinnerSet.singleton r ↔
        A = WinnerSet.singleton r) ↔
    ((∀ (v : Var → WinnerSet Role) (A : WinnerSet Role),
        t.eval (fun j => j.elim A v) = A) ∨
      ∃ g : Term Role Var, g.IsCore ∧
        ∀ (v : Var → WinnerSet Role) (A : WinnerSet Role),
          t.eval (fun j => j.elim A v) = (g.eval v).reset A) := by
  classical
  constructor
  · intro hp
    cases hg : eliminate three t with
    | none =>
      left
      intro v A
      have hm := marked_of_projection three t ht v
        (fun r => (hp v (WinnerSet.singleton r) r).mpr rfl)
      have he : (trace v t).ordinary = ∅ := by
        simpa only [hg, Option.elim_none] using eliminate_sound three t ht v
      apply Subtype.ext
      apply Set.Subset.antisymm
      · simpa only [he, Set.union_empty] using (trace_compares t ht v A).upper
      · exact (trace_compares t ht v A).lower hm
    | some g =>
      right
      refine ⟨g, eliminate_core three t ht g hg, ?_⟩
      intro v A
      by_cases ha : A.Ambiguous
      · have hm := marked_of_projection three t ht v
          (fun r => (hp v (WinnerSet.singleton r) r).mpr rfl)
        have he : (trace v t).ordinary = (g.eval v).val := by
          simpa only [hg, Option.elim_some] using eliminate_sound three t ht v
        rw [WinnerSet.reset_of_ambiguous _ _ ha]
        apply Subtype.ext
        rw [(trace_compares t ht v A).ambiguous ha]
        simp [hm, he, WinnerSet.val_union, Set.union_comm]
      · obtain ⟨r, hr⟩ := not_forall.mp ha
        have he : A = WinnerSet.singleton r := not_not.mp hr
        rw [(hp v A r).mpr he, he, WinnerSet.reset_singleton]
  · rintro (h | ⟨g, _, h⟩) v A r
    · rw [h]
    · rw [h, WinnerSet.reset_eq_singleton]

/-- A complement section recovers every ordinary bit of the left reset input. -/
theorem mem_reset_complement (three : Fin 3 ↪ Role) (G : WinnerSet Role) (k : Role) :
    k ∈ (G.reset (PlayerView.representative three k .impossible)).val ↔ k ∈ G.val := by
  have hk : k ∉ (PlayerView.representative three k .impossible).val :=
    fun h => h rfl
  rw [WinnerSet.mem_reset]
  simp only [hk, complement_ambiguous three k, false_or, true_and]

/-- Distinct residual winner sets give distinct reset contexts. -/
theorem reset_left_injective (three : Fin 3 ↪ Role) (G H : WinnerSet Role)
    (he : ∀ A : WinnerSet Role, G.reset A = H.reset A) : G = H := by
  apply Subtype.ext
  ext k
  rw [← mem_reset_complement three G k, ← mem_reset_complement three H k, he]

/-- Every nonempty residual is separated from the distinguished projection. -/
theorem exists_reset_ne_right (three : Fin 3 ↪ Role) (G : WinnerSet Role) :
    ∃ A : WinnerSet Role, G.reset A ≠ A := by
  obtain ⟨k, hk⟩ := G.property
  refine ⟨PlayerView.representative three k .impossible, ?_⟩
  intro he
  have hm := (mem_reset_complement three G k).mpr hk
  rw [he] at hm
  exact hm rfl

/-- Lower-arity residual operations in the nonzero projection fiber are unique
as functions, independently of the chosen core syntax. -/
theorem reset_lift_injective (three : Fin 3 ↪ Role)
    (g h : (Var → WinnerSet Role) → WinnerSet Role)
    (he : ∀ (v : Var → WinnerSet Role) (A : WinnerSet Role),
      (g v).reset A = (h v).reset A) : g = h := by
  funext v
  exact reset_left_injective three (g v) (h v) (he v)

/-- A nonempty residual operation never gives the distinguished projection. -/
theorem reset_lift_ne_projection (three : Fin 3 ↪ Role)
    (g : (Var → WinnerSet Role) → WinnerSet Role) :
    ¬∀ (v : Var → WinnerSet Role) (A : WinnerSet Role), (g v).reset A = A := by
  intro he
  let v : Var → WinnerSet Role := fun _ => WinnerSet.singleton (three 0)
  obtain ⟨A, hA⟩ := exists_reset_ne_right three (g v)
  exact hA (he v A)

/-- On a finite owner carrier, every lower-arity core operation has a core
reset lift in the projection-profile fiber. Finiteness is used only to list
all owners in the native compilation of reset. -/
theorem exists_core_reset_lift [Fintype Role] (three : Fin 3 ↪ Role)
    (g : Term Role Var) (hg : g.IsCore) :
    ∃ t : Term Role (Option Var), t.IsCore ∧
      ∀ (v : Var → WinnerSet Role) (A : WinnerSet Role),
        t.eval (fun j => j.elim A v) = (g.eval v).reset A := by
  classical
  let s : Term Role (Option Var) := g.subst (fun j => .var (some j))
  have hs : s.IsCore := hg.subst _ (by intro j _; trivial)
  refine ⟨Reset.Term.resetTerm three Finset.univ.toList s (.var none),
    Reset.Term.isCore_resetTerm three _ s (.var none) hs trivial, ?_⟩
  intro v A
  rw [Reset.Term.eval_resetTerm three _ (by simp)]
  simp only [s, Term.eval_subst, Term.eval, Option.elim_some, Option.elim_none]

/-- Every owned choice restricts to pointwise union on the common
projection-profile fiber. -/
theorem projection_fiber_choice_union
    (s t : Term Role (Option Var))
    (hs : ∀ (v : Var → WinnerSet Role) (A : WinnerSet Role) (r : Role),
      s.eval (fun j => j.elim A v) = WinnerSet.singleton r ↔ A = WinnerSet.singleton r)
    (ht : ∀ (v : Var → WinnerSet Role) (A : WinnerSet Role) (r : Role),
      t.eval (fun j => j.elim A v) = WinnerSet.singleton r ↔ A = WinnerSet.singleton r)
    (v : Var → WinnerSet Role) (A : WinnerSet Role) (r : Role) :
    WinnerSet.choice r (s.eval (fun j => j.elim A v)) (t.eval (fun j => j.elim A v)) =
      (s.eval (fun j => j.elim A v)).union (t.eval (fun j => j.elim A v)) := by
  classical
  by_cases ha : A.Ambiguous
  · have hn : ¬(s.eval (fun j => j.elim A v) = WinnerSet.singleton r ∨
        t.eval (fun j => j.elim A v) = WinnerSet.singleton r) := by
      rintro (he | he)
      · exact ha r ((hs v A r).mp he)
      · exact ha r ((ht v A r).mp he)
    exact ite_eq_right hn
  · obtain ⟨q, hq⟩ := not_forall.mp ha
    have hA : A = WinnerSet.singleton q := not_not.mp hq
    rw [(hs v A q).mpr hA, (ht v A q).mpr hA,
      WinnerSet.choice_self, WinnerSet.union_self]

end KFOL.Core
