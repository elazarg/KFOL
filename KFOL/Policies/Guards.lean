module

public import KFOL.Policies.Basic
public import KFOL.Owner.Guards

/-! One positive guard per original leaf for arbitrary policy families. -/

@[expose] public section

namespace KFOL.Policies

universe u v w

theorem eval_append {Label : Type w} {Var : Type v} (first second : List (Guard Label Var))
    (M : Var → Prop) (N : Label → Var → Prop) (V : Var → Prop) :
    Eval (first ++ second) M N V ↔ Eval first M N V ∨ Eval second M N V := by
  simp [Eval, List.mem_append, or_and_right, exists_or]

theorem eval_many {Label : Type w} {Var : Type v} (j : Var) (guards : List (Guard Label Var))
    (M : Var → Prop) (N : Label → Var → Prop) (V : Var → Prop) :
    Eval (guards.map (Guard.addMany j)) M N V ↔ M j ∧ Eval guards M N V := by
  constructor
  · rintro ⟨g, hg, hm, hn, hv⟩
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hg
    exact ⟨hm j (List.mem_cons_self ..), s, hs,
      (fun i hi => hm i (List.mem_cons_of_mem _ hi)), hn, hv⟩
  · rintro ⟨hj, g, hg, hm, hn, hv⟩
    refine ⟨g.addMany j, List.mem_map.mpr ⟨g, hg, rfl⟩, ?_, hn, hv⟩
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact hj
    · exact hm i hi

theorem eval_pass {Label : Type w} {Var : Type v} (d : Label) (j : Var) (guards : List (Guard Label Var))
    (M : Var → Prop) (N : Label → Var → Prop) (V : Var → Prop) :
    Eval (guards.map (Guard.addPass d j)) M N V ↔ N d j ∧ Eval guards M N V := by
  constructor
  · rintro ⟨g, hg, hm, hn, hv⟩
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hg
    exact ⟨hn (d, j) (List.mem_cons_self ..), s, hs, hm,
      (fun p hp => hn p (List.mem_cons_of_mem _ hp)), hv⟩
  · rintro ⟨hj, g, hg, hm, hn, hv⟩
    refine ⟨g.addPass d j, List.mem_map.mpr ⟨g, hg, rfl⟩, hm, ?_, hv⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hj
    · exact hn p hp

namespace Term

variable {Role : Type u} {Label : Type w} {Var : Type v}

@[simp] theorem guards_var (j : Var) : guards (.var j : Term Label Var) = [⟨j, [], []⟩] := rfl
@[simp] theorem guards_step (s t : Term Label Var) :
    (step s t).guards = t.guards ++ s.guards.map (Guard.addMany t.root) := rfl
@[simp] theorem guards_selective (d : Label) (x y z : Term Label Var) :
    (selective d x y z).guards = x.guards ++
      (y.guards ++ z.guards.map (Guard.addPass d y.root)).map (Guard.addMany x.root) := rfl

/-- Exact native semantics, retaining policy labels and original variable
occurrences. There is no finiteness, chain or observer restriction here. -/
theorem guard_semantics (D : Label → Set Role) (t : Term Label Var) (k : Role) (v : Var → WinnerSet Role) :
    k ∈ (t.eval D v).val ↔ Eval t.guards
      (fun j => (v j).Ambiguous) (fun d j => WinnerSet.PolicyPasses (D d) k (v j))
      (fun j => k ∈ (v j).val) := by
  induction t using induction_policy with
  | var j => simp [eval_var, guards_var, Eval, Guard.Holds]
  | step s t hs ht =>
    simp only [eval_step, guards_step, WinnerSet.mem_reset, eval_append, eval_many,
      hs, ht, ambiguous_iff]
  | selective d x y z hx hy hz =>
    simp only [eval_selective, guards_selective, WinnerSet.mem_policyReset, eval_append, eval_many,
      eval_pass, hx, hy, hz, ambiguous_iff, policyPasses_iff]

/-- A root occurrence is always available without tests. -/
theorem root_guard_mem (t : Term Label Var) : (⟨t.root, [], []⟩ : Guard Label Var) ∈ t.guards := by
  induction t using induction_policy with
  | var => exact List.mem_singleton_self _
  | step s t _ ht => exact List.mem_append_left _ ht
  | selective d x y z hx _ _ => exact List.mem_append_left _ hx

theorem guards_length (t : Term Label Var) : t.guards.length = t.leafCount := by
  induction t using induction_policy with
  | var => rfl
  | step s t hs ht =>
    simp only [guards_step, List.length_append, List.length_map, hs, ht]
    change t.leafCount + s.leafCount = s.leafCount + t.leafCount
    omega
  | selective d x y z hx hy hz =>
    simp only [guards_selective, List.length_append, List.length_map, hx, hy, hz]
    change x.leafCount + (y.leafCount + z.leafCount) = x.leafCount + y.leafCount + z.leafCount
    omega

end Term

theorem Guard.holds_toSingle {Label : Type w} {Var : Type v} (g : Guard Label Var)
    (M N V : Var → Prop) : g.toSingle.Holds M N V ↔ g.Holds M (fun _ j => N j) V := by
  constructor
  · rintro ⟨hm, hn, hv⟩
    exact ⟨hm, (fun p hp => hn p.2 (List.mem_map.mpr ⟨p, hp, rfl⟩)), hv⟩
  · rintro ⟨hm, hn, hv⟩
    refine ⟨hm, ?_, hv⟩
    intro j hj
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hj
    exact hn p hp

theorem eval_toSingle {Label : Type w} {Var : Type v} (guards : List (Guard Label Var))
    (M N V : Var → Prop) : Owner.Eval (guards.map Guard.toSingle) M N V ↔ Eval guards M (fun _ j => N j) V := by
  constructor
  · rintro ⟨g, hg, hholds⟩
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hg
    exact ⟨s, hs, (s.holds_toSingle M N V).mp hholds⟩
  · rintro ⟨g, hg, hholds⟩
    exact ⟨g.toSingle, List.mem_map.mpr ⟨g, hg, rfl⟩, (g.holds_toSingle M N V).mpr hholds⟩

namespace Term

variable {Role : Type u} {Label : Type w} {Var : Type v}

/-- A fixed single policy uses the same unlabelled guards for every observer. -/
theorem single_guard_semantics (D : Set Role) (t : Term Label Var) (k : Role) (v : Var → WinnerSet Role) :
    k ∈ (t.eval (fun _ => D) v).val ↔ Owner.Eval t.singleGuards
      (fun j => (v j).Ambiguous) (fun j => WinnerSet.PolicyPasses D k (v j)) (fun j => k ∈ (v j).val) := by
  rw [singleGuards, eval_toSingle]
  exact t.guard_semantics (fun _ => D) k v

theorem singleGuards_length (t : Term Label Var) : t.singleGuards.length = t.leafCount := by
  rw [singleGuards, List.length_map, guards_length]

end Term
end KFOL.Policies
