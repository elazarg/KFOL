module

public import KFOL.Owner.SynthesisSoundness

/-! Whole-table executable checking and constructive synthesis soundness. -/

@[expose] public section

namespace KFOL.Owner

universe u v

namespace Term

variable {Role : Type u} {Var : Type v}

/-- Reset is union on two terms with the same independently defined root. -/
theorem eval_step_same_root (s t : Term Role Var) (hr : s.root = t.root)
    (v : Var → WinnerSet Role) : (step s t).eval v = (s.eval v).union (t.eval v) := by
  classical
  rw [eval_step]
  by_cases ht : (t.eval v).Ambiguous
  · exact WinnerSet.reset_of_ambiguous _ _ ht
  · unfold WinnerSet.Ambiguous at ht
    push Not at ht
    obtain ⟨r, htr⟩ := ht
    have hsr := (s.eq_singleton_iff v r).mpr (hr ▸ (t.eq_singleton_iff v r).mp htr)
    rw [hsr, htr, WinnerSet.union_self]
    exact WinnerSet.reset_self _

@[simp] theorem root_joinPaths (r : Var) (ts : List (Term Role Var)) :
    (joinPaths r ts).root = r := by
  induction ts with
  | nil => rfl
  | cons t ts ih => exact ih

theorem owners_joinPaths (a : Role) (r : Var) (ts : List (Term Role Var))
    (hs : ∀ t ∈ ts, t.OwnersIn (fun x => x = a)) : (joinPaths r ts).OwnersIn (fun x => x = a) := by
  induction ts with
  | nil => trivial
  | cons t ts ih => exact ⟨hs t (List.mem_cons_self ..), ih (fun t ht => hs t (List.mem_cons_of_mem _ ht))⟩

theorem size_joinPaths_le (r : Var) (ts : List (Term Role Var)) (bound : ℕ)
    (hs : ∀ t ∈ ts, t.size ≤ bound) :
    (joinPaths r ts).size ≤ 1 + ts.length * (bound + 1) := by
  induction ts with
  | nil => simp [joinPaths]
  | cons t ts ih =>
    have ht := hs t (List.mem_cons_self ..)
    have hh := ih (fun t ht => hs t (List.mem_cons_of_mem _ ht))
    simp only [joinPaths, size_step, List.length_cons]
    rw [Nat.add_mul]
    omega

theorem mem_joinPaths (r : Var) (ts : List (Term Role Var))
    (hr : ∀ t ∈ ts, t.root = r) (v : Var → WinnerSet Role) (k : Role) :
    k ∈ ((joinPaths r ts).eval v).val ↔ k ∈ (v r).val ∨ ∃ t ∈ ts, k ∈ (t.eval v).val := by
  induction ts with
  | nil => simp [joinPaths]
  | cons t ts ih =>
    rw [show joinPaths r (t :: ts) = step t (joinPaths r ts) from rfl,
      eval_step_same_root t _ ((hr t (List.mem_cons_self ..)).trans (root_joinPaths ..).symm)]
    simp only [WinnerSet.val_union, Set.mem_union,
      ih (fun t ht => hr t (List.mem_cons_of_mem _ ht)), List.mem_cons]
    aesop

end Term

namespace GuardTable

variable {Var : Type v} [DecidableEq Var]

@[simp] theorem mem_guards (T : GuardTable Var) (j : Var) (g : GuardPair Var) :
    g ∈ T.guards j ↔ (j, g) ∈ T.entries := by
  simp only [guards, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨p, ⟨hp, hj⟩, hg⟩
    cases p
    cases hj
    cases hg
    exact hp
  · intro h
    exact ⟨(j, g), ⟨h, rfl⟩, rfl⟩

theorem canonicalB_iff (T : GuardTable Var) : T.canonicalB = true ↔ T.Canonical := by
  simp only [canonicalB, decide_eq_true_eq, Canonical]
  constructor
  · rintro ⟨hn, hr, hs⟩
    refine ⟨hn, hr, ?_⟩
    intro j hj
    constructor
    · intro g hg
      exact (hs (j, g) ((T.mem_guards j g).mp hg) hj).1
    · intro g hg h hh hm ho
      exact (hs (j, g) ((T.mem_guards j g).mp hg) hj).2 (j, h)
        ((T.mem_guards j h).mp hh) rfl hm ho
  · rintro ⟨hn, hr, hs⟩
    refine ⟨hn, hr, ?_⟩
    intro p hp hj
    refine ⟨(hs p.1 hj).1 p.2 ((T.mem_guards ..).mpr hp), ?_⟩
    intro q hq he hm ho
    have hqq : q.2 ∈ T.guards p.1 := by
      rw [← he]
      exact (T.mem_guards ..).mpr hq
    exact (hs p.1 hj).2 p.2 ((T.mem_guards ..).mpr hp) q.2 hqq hm ho

theorem check_iff (T : GuardTable Var) (positions : List Var) :
    T.check positions = true ↔ T.Canonical ∧ T.Listed positions ∧
      ∀ p ∈ T.entries, T.accepts positions p.1 p.2 = true := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  rw [T.canonicalB_iff]
  tauto

private theorem mapM_some_iff {α : Type*} {β : Type*} (f : α → Option β)
    (xs : List α) (ys : List β) : xs.mapM f = some ys ↔ List.Forall₂ (fun x y => f x = some y) xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp
  | cons x xs ih =>
    cases hx : f x with
    | none => cases ys <;> simp [List.mapM_cons, hx]
    | some y =>
      cases hy : xs.mapM f with
      | none =>
        have hn : ∀ zs, ¬List.Forall₂ (fun x y => f x = some y) xs zs := by
          intro zs hz
          have hsome := (ih zs).mpr hz
          rw [hy] at hsome
          cases hsome
        cases ys <;> simp [List.mapM_cons, hx, hy, hn]
      | some zs =>
        have hrel := (ih zs).mp hy
        cases ys with
        | nil => simp [List.mapM_cons, hx, hy]
        | cons y' ys =>
          simp only [List.mapM_cons, hx, hy, pure, Option.some.injEq, List.forall₂_cons]
          constructor
          · rintro ⟨rfl, rfl⟩
            exact ⟨rfl, hrel⟩
          · rintro ⟨he, hh⟩
            have heys := Option.some.inj (hy.symm.trans ((ih ys).mpr hh))
            exact congrArg some (congrArg₂ List.cons he heys)

private theorem forall₂_left {α : Type*} {β : Type*} {R : α → β → Prop}
    {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys) :
    ∀ x ∈ xs, ∃ y ∈ ys, R x y := by
  induction h with
  | nil => simp
  | @cons x y xs ys hxy hrest ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ⟨y, List.mem_cons_self .., hxy⟩
    · obtain ⟨y', hy', hzy⟩ := ih z hz
      exact ⟨y', List.mem_cons_of_mem _ hy', hzy⟩

private theorem forall₂_right {α : Type*} {β : Type*} {R : α → β → Prop}
    {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys) :
    ∀ y ∈ ys, ∃ x ∈ xs, R x y := by
  induction h with
  | nil => simp
  | @cons x y xs ys hxy hrest ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ⟨x, List.mem_cons_self .., hxy⟩
    · obtain ⟨x', hx', hxz⟩ := ih z hz
      exact ⟨x', List.mem_cons_of_mem _ hx', hxz⟩

/-- Exact totality of the actual synthesizer on the checker's accepted inputs. -/
theorem synthesize_isSome {Role : Type u} (T : GuardTable Var) (a : Role) (positions : List Var) :
    (T.synthesize a positions).isSome = true ↔ T.check positions = true := by
  unfold synthesize
  split
  next hc =>
    simp only [Option.isSome_map, hc, iff_true]
    obtain ⟨_, hlisted, ha⟩ := (T.check_iff positions).mp hc
    have hex : ∀ xs : List (Var × GuardPair Var), (∀ p ∈ xs, p ∈ T.entries) →
        ∃ ys, xs.mapM (fun p => T.guardPath a positions p.1 p.2) = some ys := by
      intro xs
      induction xs with
      | nil => intro _; exact ⟨[], rfl⟩
      | cons p ps ih =>
        intro hmem
        obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp
          ((T.guardPath_isSome a positions p.1 p.2 (hlisted.2 p (hmem p (List.mem_cons_self ..)))).mpr
            (ha p (hmem p (List.mem_cons_self ..))))
        obtain ⟨ts, hts⟩ := ih (fun q hq => hmem q (List.mem_cons_of_mem _ hq))
        exact ⟨t :: ts, by simp [List.mapM_cons, ht, hts]⟩
    exact Option.isSome_iff_exists.mpr (hex T.entries (fun _ h => h))
  next hc => simp [hc]

/-- Accepted tables produce the specified semantic algebra term, with the
explicit O(nM) bound on expanded syntax. This is sufficiency; necessity of
acceptance for every realization is a separate theorem. -/
theorem synthesize_spec {Role : Type u} (T : GuardTable Var) (a : Role) (positions : List Var)
    {t : Term Role Var} (ht : T.synthesize a positions = some t) :
    T.Realizes a t ∧ t.size ≤ 1 + T.entries.length * (10 * positions.length + 7) := by
  unfold synthesize at ht
  split at ht
  next hc =>
    obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp ht
    have hrel := (mapM_some_iff _ _ _).mp hts
    obtain ⟨hcan, hlisted, _⟩ := (T.check_iff positions).mp hc
    have hpath : ∀ p ∈ T.entries, ∀ s, T.guardPath a positions p.1 p.2 = some s →
        s.root = T.root ∧ s.OwnersIn (fun x => x = a) ∧ s.size ≤ 10 * positions.length + 6 := by
      intro p hp s hs
      have hcover := hlisted.2 p hp
      have hshape : p.1 ≠ T.root → T.root ∈ p.2.many := fun hj =>
        ((hcan.2.2 p.1 hj).1 p.2 ((T.mem_guards ..).mpr hp)).1
      -- Root, owners and sizes do not require choosing a non-owner observer.
      unfold guardPath at hs
      split at hs
      next hj =>
        cases Option.some.inj hs
        exact ⟨rfl, trivial, by simp only [Term.size_var]; omega⟩
      next hj =>
        obtain ⟨fill, hfill, rfl⟩ := Option.map_eq_some_iff.mp hs
        have hflen := T.run_frames_length_le positions p.1 p.2 (hshape hj) hcover (2 * positions.length)
        have hfillowners : fill.OwnersIn (fun x => x = a) := by
          unfold finishTerm at hfill
          split at hfill
          · cases Option.some.inj hfill
            exact ⟨trivial, trivial⟩
          · obtain ⟨z, _, rfl⟩ := Option.map_eq_some_iff.mp hfill
            exact ⟨rfl, trivial, trivial, trivial⟩
        have hfillsize : fill.size ≤ 4 := by
          unfold finishTerm at hfill
          split at hfill
          · cases Option.some.inj hfill
            simp only [Term.size_step, Term.size_var]
            omega
          · obtain ⟨z, _, rfl⟩ := Option.map_eq_some_iff.mp hfill
            simp only [Term.size_guarded, Term.size_var]
            omega
        refine ⟨rfl, Term.owners_pathTerm a T.root _ fill hfillowners, ?_⟩
        rw [Term.size_pathTerm]
        omega
    have hall : ∀ s ∈ ts, s.root = T.root ∧ s.OwnersIn (fun x => x = a) ∧
        s.size ≤ 10 * positions.length + 6 := by
      intro s hs
      obtain ⟨p, hp, hps⟩ := forall₂_right hrel s hs
      exact hpath p hp s hps
    refine ⟨⟨Term.root_joinPaths .., Term.owners_joinPaths a T.root ts (fun s hs => (hall s hs).2.1), ?_⟩, ?_⟩
    · intro k hka v
      rw [Term.mem_joinPaths T.root ts (fun s hs => (hall s hs).1) v k]
      constructor
      · rintro (hv | ⟨s, hs, hv⟩)
        · refine ⟨T.root, ⟨∅, ∅⟩, ?_, ?_, ?_, hv⟩
          · rw [hcan.2.1]; exact Finset.mem_singleton_self _
          · intro i hi; exact False.elim (Finset.notMem_empty i hi)
          · intro i hi; exact False.elim (Finset.notMem_empty i hi)
        · obtain ⟨p, hp, hps⟩ := forall₂_right hrel s hs
          exact (T.guardPath_spec a k hka hcan.2.1 positions p.1 p.2
            (fun hj => ((hcan.2.2 p.1 hj).1 p.2 ((T.mem_guards ..).mpr hp)).1)
            (hlisted.2 p hp) hps).2.2.2.1 v hv
      · rintro ⟨j, g, hg, hm, hn, hv⟩
        have hp := (T.mem_guards j g).mp hg
        obtain ⟨s, hs, hps⟩ := forall₂_left hrel (j, g) hp
        right
        refine ⟨s, hs, ?_⟩
        exact (T.guardPath_spec a k hka hcan.2.1 positions j g
          (fun hj => ((hcan.2.2 j hj).1 g hg).1) (hlisted.2 (j, g) hp) hps).2.2.2.2
          v (fun i hi => hm hi) (fun i hi => hn hi) hv
    · have hsize := Term.size_joinPaths_le T.root ts (10 * positions.length + 6)
        (fun s hs => (hall s hs).2.2)
      rw [← hrel.length_eq] at hsize
      exact hsize
  next hc => cases ht

end GuardTable
end KFOL.Owner
