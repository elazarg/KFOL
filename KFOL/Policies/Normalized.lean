module

public import KFOL.Policies.Guards
public import KFOL.Policies.Lattice
public import KFOL.Policies.Patterns

/-! The normalized native guard compiler. A full passing collision introduces
ambiguity at one input; the second child's root contribution supplies its
lost marker case. No new guard records or duplicated subtrees are introduced. -/

@[expose] public section

namespace KFOL.Policies

universe u v w

@[simp] theorem mem_labelsAt {Label : Type w} {Var : Type v} [DecidableEq Var]
    (g : Guard Label Var) (i : Var) (d : Label) : d ∈ g.labelsAt i ↔ (d, i) ∈ g.passes := by
  simp only [Guard.labelsAt, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨hp, hi⟩, hd⟩
    cases hi
    cases hd
    exact hp
  · intro h
    exact ⟨(d, i), ⟨h, rfl⟩, rfl⟩

@[simp] theorem blockingAt_addMany {Role : Type u} {Label : Type w} {Var : Type v}
    [DecidableEq Role] [DecidableEq Var] (D : Label → Finset Role) (g : Guard Label Var) (i j : Var) :
    (g.addMany j).blockingAt D i = g.blockingAt D i := rfl

@[simp] theorem blockingAt_addPass_same {Role : Type u} {Label : Type w} {Var : Type v}
    [DecidableEq Role] [DecidableEq Var] (D : Label → Finset Role) (g : Guard Label Var) (d : Label) (i : Var) :
    (g.addPass d i).blockingAt D i = D d ∪ g.blockingAt D i := by
  simp [Guard.blockingAt, Guard.labelsAt, Guard.addPass, blockingUnion]

@[simp] theorem blockingAt_addPass_ne {Role : Type u} {Label : Type w} {Var : Type v}
    [DecidableEq Role] [DecidableEq Var] (D : Label → Finset Role) (g : Guard Label Var) (d : Label) (i j : Var) (hij : i ≠ j) :
    (g.addPass d i).blockingAt D j = g.blockingAt D j := by
  simp [Guard.blockingAt, Guard.labelsAt, Guard.addPass, hij]

@[simp] theorem blockingAt_normalizeAt {Role : Type u} {Label : Type w} {Var : Type v}
    [DecidableEq Role] [DecidableEq Var] (D : Label → Finset Role) (top : Finset Role) (g : Guard Label Var) (i j : Var) :
    (g.normalizeAt D top j).blockingAt D i = g.blockingAt D i := by
  unfold Guard.normalizeAt
  split <;> rfl

@[simp] theorem normalizeAt_source {Role : Type u} {Label : Type w} {Var : Type v}
    [DecidableEq Role] [DecidableEq Var] (D : Label → Finset Role) (top : Finset Role) (g : Guard Label Var) (i : Var) :
    (g.normalizeAt D top i).source = g.source := by
  unfold Guard.normalizeAt
  split <;> rfl

/-- The compiled metadata preserves canonicality at every previously proper input. -/
theorem normalized_addMany {Role : Type u} {Label : Type w} {Var : Type v}
    [DecidableEq Role] [DecidableEq Var] (D : Label → Finset Role) (top : Finset Role) (g : Guard Label Var)
    (hg : g.Normalized D top) (i : Var) : (g.addMany i).Normalized D top := by
  intro j hjs hjm
  exact hg j hjs (fun hj => hjm (List.mem_cons_of_mem _ hj))

theorem normalized_normalize_addPass {Role : Type u} {Label : Type w} {Var : Type v}
    [DecidableEq Role] [DecidableEq Var] (D : Label → Finset Role) (top : Finset Role) (g : Guard Label Var)
    (hg : g.Normalized D top) (d : Label) (i : Var) :
    ((g.addPass d i).normalizeAt D top i).Normalized D top := by
  intro j hjs hjm
  by_cases hfull : (g.addPass d i).blockingAt D i = top
  · have he : (g.addPass d i).normalizeAt D top i = (g.addPass d i).addMany i := by
      simp only [Guard.normalizeAt, hfull, ite_true]
    rw [he] at hjs hjm ⊢
    have hji : j ≠ i := fun heq => hjm (heq ▸ List.mem_cons_self ..)
    rw [blockingAt_addMany, blockingAt_addPass_ne D g d i j (Ne.symm hji)]
    exact hg j hjs (fun hj => hjm (List.mem_cons_of_mem _ hj))
  · have he : (g.addPass d i).normalizeAt D top i = g.addPass d i := by
      simp only [Guard.normalizeAt, hfull, ite_false]
    rw [he] at hjs hjm ⊢
    by_cases hji : j = i
    · simpa only [hji] using hfull
    · rw [blockingAt_addPass_ne D g d i j (Ne.symm hji)]
      exact hg j hjs hjm

namespace Term

variable {Role : Type u} {Label : Type w} {Var : Type v} [DecidableEq Role] [DecidableEq Var]

@[simp] theorem normalGuards_var (D : Label → Finset Role) (top : Finset Role) (j : Var) :
    normalGuards D top (.var j : Term Label Var) = [⟨j, [], []⟩] := rfl
@[simp] theorem normalGuards_step (D : Label → Finset Role) (top : Finset Role) (s t : Term Label Var) :
    (step s t).normalGuards D top = t.normalGuards D top ++
      (s.normalGuards D top).map (Guard.addMany t.root) := rfl
@[simp] theorem normalGuards_selective (D : Label → Finset Role) (top : Finset Role) (d : Label) (x y z : Term Label Var) :
    (selective d x y z).normalGuards D top = x.normalGuards D top ++
      (y.normalGuards D top ++ ((z.normalGuards D top).map (Guard.addPass d y.root)).map
        (Guard.normalizeAt D top y.root)).map (Guard.addMany x.root) := rfl

theorem normalGuards_root (D : Label → Finset Role) (top : Finset Role) (t : Term Label Var) :
    (⟨t.root, [], []⟩ : Guard Label Var) ∈ t.normalGuards D top := by
  induction t using induction_policy with
  | var => exact List.mem_singleton_self _
  | step s t _ ht => exact List.mem_append_left _ ht
  | selective d x y z hx _ _ => exact List.mem_append_left _ hx

theorem normalGuards_length (D : Label → Finset Role) (top : Finset Role) (t : Term Label Var) :
    (t.normalGuards D top).length = t.leafCount := by
  induction t using induction_policy with
  | var => rfl
  | step s t hs ht =>
    simp only [normalGuards_step, List.length_append, List.length_map, hs, ht]
    change t.leafCount + s.leafCount = s.leafCount + t.leafCount
    omega
  | selective d x y z hx hy hz =>
    simp only [normalGuards_selective, List.length_append, List.length_map, hx, hy, hz]
    change x.leafCount + (y.leafCount + z.leafCount) = x.leafCount + y.leafCount + z.leafCount
    omega

theorem normalGuards_normalized (D : Label → Finset Role) (top : Finset Role) (htop : top.Nonempty)
    (t : Term Label Var) : ∀ g ∈ t.normalGuards D top, g.Normalized D top := by
  induction t using induction_policy with
  | var j =>
    intro g hg
    cases List.mem_singleton.mp hg
    intro i _ _
    change ∅ ≠ top
    exact Ne.symm (Finset.nonempty_iff_ne_empty.mp htop)
  | step s t hs ht =>
    intro g hg
    rw [normalGuards_step] at hg
    rcases List.mem_append.mp hg with hg | hg
    · exact ht g hg
    · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
      exact normalized_addMany D top h (hs h hh) t.root
  | selective d x y z hx hy hz =>
    intro out hOut
    rw [normalGuards_selective] at hOut
    rcases List.mem_append.mp hOut with hFirst | hMapped
    · exact hx out hFirst
    · obtain ⟨middle, hMiddle, rfl⟩ := List.mem_map.mp hMapped
      apply normalized_addMany D top middle ?_ x.root
      rcases List.mem_append.mp hMiddle with hSecond | hNormalized
      · exact hy middle hSecond
      · obtain ⟨passed, hPassed, rfl⟩ := List.mem_map.mp hNormalized
        obtain ⟨before, hBefore, rfl⟩ := List.mem_map.mp hPassed
        exact normalized_normalize_addPass D top before (hz before hBefore) d y.root

end Term

/-- A conjunction of passing labels is exactly the union of their blockers. -/
theorem policyPasses_blockingUnion {Role : Type u} {Label : Type w} [DecidableEq Role]
    (D : Label → Finset Role) (labels : List Label) (k : Role) (Y : WinnerSet Role) :
    WinnerSet.PolicyPasses (blockingUnion D labels : Set Role) k Y ↔
      ∀ d ∈ labels, WinnerSet.PolicyPasses (D d : Set Role) k Y := by
  induction labels with
  | nil => simp only [blockingUnion, Finset.coe_empty, WinnerSet.policyPasses_empty, List.not_mem_nil, false_implies, implies_true]
  | cons d rest ih =>
    simp only [blockingUnion, Finset.coe_union, WinnerSet.policyPasses_union, ih, List.mem_cons, forall_eq_or_imp]

theorem Guard.passingAt_of_holds {Role : Type u} {Label : Type w} {Var : Type v}
    [DecidableEq Role] [DecidableEq Var] (D : Label → Finset Role) (k : Role) (v : Var → WinnerSet Role)
    (g : Guard Label Var) (hg : g.Holds (fun i => (v i).Ambiguous)
      (fun d i => WinnerSet.PolicyPasses (D d : Set Role) k (v i)) (fun i => k ∈ (v i).val)) (i : Var) :
    WinnerSet.PolicyPasses (g.blockingAt D i : Set Role) k (v i) := by
  apply (policyPasses_blockingUnion D (g.labelsAt i) k (v i)).mpr
  intro d hd
  exact hg.2.1 (d, i) ((mem_labelsAt g i d).mp hd)

/-- Full passing tests force ambiguity or membership at their input. -/
theorem normalizeAt_holds {Role : Type u} {Label : Type w} {Var : Type v}
    [DecidableEq Role] [DecidableEq Var] (D : Label → Finset Role) (top : Finset Role)
    (k : Role) (hTop : (top : Set Role) ∪ {k} = Set.univ) (v : Var → WinnerSet Role)
    (g : Guard Label Var) (i : Var) :
    ((g.normalizeAt D top i).Holds (fun j => (v j).Ambiguous)
      (fun d j => WinnerSet.PolicyPasses (D d : Set Role) k (v j)) (fun j => k ∈ (v j).val) →
      g.Holds (fun j => (v j).Ambiguous) (fun d j => WinnerSet.PolicyPasses (D d : Set Role) k (v j)) (fun j => k ∈ (v j).val)) ∧
    (g.Holds (fun j => (v j).Ambiguous) (fun d j => WinnerSet.PolicyPasses (D d : Set Role) k (v j)) (fun j => k ∈ (v j).val) →
      (g.normalizeAt D top i).Holds (fun j => (v j).Ambiguous)
        (fun d j => WinnerSet.PolicyPasses (D d : Set Role) k (v j)) (fun j => k ∈ (v j).val) ∨ k ∈ (v i).val) := by
  by_cases hfull : g.blockingAt D i = top
  · have he : g.normalizeAt D top i = g.addMany i := by simp only [Guard.normalizeAt, hfull, ite_true]
    rw [he]
    constructor
    · rintro ⟨hm, hn, hv⟩
      exact ⟨fun j hj => hm j (List.mem_cons_of_mem _ hj), hn, hv⟩
    · intro hg
      have hp := g.passingAt_of_holds D k v hg i
      rw [hfull, WinnerSet.policyPasses_observer_cover (top : Set Role) k (v i) hTop] at hp
      rcases hp with hm | hv
      · left
        refine ⟨?_, hg.2.1, hg.2.2⟩
        intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact hm
        · exact hg.1 j hj
      · exact Or.inr hv
  · have he : g.normalizeAt D top i = g := by simp only [Guard.normalizeAt, hfull, ite_false]
    rw [he]
    exact ⟨id, Or.inl⟩

theorem eval_normalizeAt {Role : Type u} {Label : Type w} {Var : Type v}
    [DecidableEq Role] [DecidableEq Var] (D : Label → Finset Role) (top : Finset Role)
    (k : Role) (hTop : (top : Set Role) ∪ {k} = Set.univ) (v : Var → WinnerSet Role)
    (guards : List (Guard Label Var)) (i : Var) :
    (Eval (guards.map (Guard.normalizeAt D top i)) (fun j => (v j).Ambiguous)
      (fun d j => WinnerSet.PolicyPasses (D d : Set Role) k (v j)) (fun j => k ∈ (v j).val) →
      Eval guards (fun j => (v j).Ambiguous) (fun d j => WinnerSet.PolicyPasses (D d : Set Role) k (v j)) (fun j => k ∈ (v j).val)) ∧
    (Eval guards (fun j => (v j).Ambiguous) (fun d j => WinnerSet.PolicyPasses (D d : Set Role) k (v j)) (fun j => k ∈ (v j).val) →
      Eval (guards.map (Guard.normalizeAt D top i)) (fun j => (v j).Ambiguous)
        (fun d j => WinnerSet.PolicyPasses (D d : Set Role) k (v j)) (fun j => k ∈ (v j).val) ∨ k ∈ (v i).val) := by
  constructor
  · rintro ⟨h, hh, hholds⟩
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hh
    exact ⟨g, hg, (normalizeAt_holds D top k hTop v g i).1 hholds⟩
  · rintro ⟨g, hg, hholds⟩
    rcases (normalizeAt_holds D top k hTop v g i).2 hholds with hn | hi
    · exact Or.inl ⟨g.normalizeAt D top i, List.mem_map.mpr ⟨g, hg, rfl⟩, hn⟩
    · exact Or.inr hi

namespace Term

variable {Role : Type u} {Label : Type w} {Var : Type v} [DecidableEq Role] [DecidableEq Var]

/-- Exact observer semantics of the normalized native compiler, including
full-union collisions. The argument retains the second child's root guard. -/
theorem normal_guard_semantics (D : Label → Finset Role) (top : Finset Role)
    (k : Role) (hTop : (top : Set Role) ∪ {k} = Set.univ) (t : Term Label Var) (v : Var → WinnerSet Role) :
    k ∈ (t.eval (fun d => (D d : Set Role)) v).val ↔ Eval (t.normalGuards D top)
      (fun j => (v j).Ambiguous) (fun d j => WinnerSet.PolicyPasses (D d : Set Role) k (v j))
      (fun j => k ∈ (v j).val) := by
  induction t using induction_policy with
  | var j => simp [eval_var, normalGuards_var, Eval, Guard.Holds]
  | step s t hs ht =>
    simp only [eval_step, normalGuards_step, WinnerSet.mem_reset, eval_append, eval_many,
      hs, ht, ambiguous_iff]
  | selective d x y z hx hy hz =>
    let M : Var → Prop := fun j => (v j).Ambiguous
    let N : Label → Var → Prop := fun e j => WinnerSet.PolicyPasses (D e : Set Role) k (v j)
    let V : Var → Prop := fun j => k ∈ (v j).val
    have hyRoot : V y.root → Eval (y.normalGuards D top) M N V := by
      intro hv
      exact ⟨⟨y.root, [], []⟩, y.normalGuards_root D top, (fun _ hi => False.elim (List.not_mem_nil hi)),
        (fun _ hi => False.elim (List.not_mem_nil hi)), hv⟩
    have hn := eval_normalizeAt D top k hTop v ((z.normalGuards D top).map (Guard.addPass d y.root)) y.root
    have hparts :
        (Eval (y.normalGuards D top) M N V ∨
          Eval (((z.normalGuards D top).map (Guard.addPass d y.root)).map (Guard.normalizeAt D top y.root)) M N V) ↔
        (Eval (y.normalGuards D top) M N V ∨ (N d y.root ∧ Eval (z.normalGuards D top) M N V)) := by
      constructor
      · rintro (hy | hz)
        · exact Or.inl hy
        · exact Or.inr ((eval_pass d y.root _ M N V).mp (hn.1 hz))
      · rintro (hy | hz)
        · exact Or.inl hy
        · rcases hn.2 ((eval_pass d y.root _ M N V).mpr hz) with hnz | hroot
          · exact Or.inr hnz
          · exact Or.inl (hyRoot hroot)
    simp only [eval_selective, normalGuards_selective, WinnerSet.mem_policyReset, eval_append, eval_many,
      hx, hy, hz, ambiguous_iff, policyPasses_iff]
    exact or_congr Iff.rfl (and_congr Iff.rfl hparts.symm)

omit [DecidableEq Var] in
/-- Stripping the observed atom changes no possible-win observation. -/
theorem observation_erase (D : Label → Finset Role) (k : Role) (t : Term Label Var) (v : Var → WinnerSet Role) :
    k ∈ (t.eval (fun d => (D d : Set Role)) v).val ↔
      k ∈ (t.eval (fun d => ((D d).erase k : Set Role)) v).val := by
  rw [guard_semantics, guard_semantics]
  simp only [Finset.coe_erase, WinnerSet.policyPasses_diff_observer]

end Term

end KFOL.Policies
