module

public import KFOL.Owner.Basic

/-! # Exact guard semantics and pairwise coverage -/

@[expose] public section

namespace KFOL.Owner

universe u v

theorem eval_append {Var : Type*} (first second : List (Guard Var)) (M N V : Var → Prop) :
    Eval (first ++ second) M N V ↔ Eval first M N V ∨ Eval second M N V := by
  simp [Eval, List.mem_append, or_and_right, exists_or]

theorem eval_many {Var : Type*} (j : Var) (guards : List (Guard Var)) (M N V : Var → Prop) :
    Eval (guards.map (Guard.addMany j)) M N V ↔ M j ∧ Eval guards M N V := by
  constructor
  · rintro ⟨g, hg, hm, hn, hv⟩
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hg
    exact ⟨hm j (by simp [Guard.addMany]), s, hs,
      (fun i hi => hm i (by simp [Guard.addMany, hi])), hn, hv⟩
  · rintro ⟨hj, g, hg, hm, hn, hv⟩
    refine ⟨g.addMany j, List.mem_map.mpr ⟨g, hg, rfl⟩, ?_, hn, hv⟩
    intro i hi
    rcases List.mem_cons.mp hi with hi | hi
    · exact hi ▸ hj
    · exact hm i hi

theorem eval_outside {Var : Type*} (j : Var) (guards : List (Guard Var)) (M N V : Var → Prop) :
    Eval (guards.map (Guard.addOutside j)) M N V ↔ N j ∧ Eval guards M N V := by
  constructor
  · rintro ⟨g, hg, hm, hn, hv⟩
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hg
    exact ⟨hn j (by simp [Guard.addOutside]), s, hs, hm,
      (fun i hi => hn i (by simp [Guard.addOutside, hi])), hv⟩
  · rintro ⟨hj, g, hg, hm, hn, hv⟩
    refine ⟨g.addOutside j, List.mem_map.mpr ⟨g, hg, rfl⟩, hm, ?_, hv⟩
    intro i hi
    rcases List.mem_cons.mp hi with hi | hi
    · exact hi ▸ hj
    · exact hn i hi

@[simp] theorem Term.guards_var {Role : Type u} {Var : Type v} [DecidableEq Role]
    (observer : Role) (j : Var) : guards observer (.var j) = [⟨j, [], []⟩] := rfl

@[simp] theorem Term.guards_step {Role : Type u} {Var : Type v} [DecidableEq Role]
    (observer : Role) (s t : Term Role Var) :
    (step s t).guards observer = t.guards observer ++
      (s.guards observer).map (Guard.addMany t.root) := rfl

@[simp] theorem Term.guards_guarded {Role : Type u} {Var : Type v} [DecidableEq Role]
    (observer r : Role) (x y z : Term Role Var) :
    (guarded r x y z).guards observer = x.guards observer ++
      (if r = observer then y.guards observer ++ z.guards observer else
        ((y.guards observer ++ z.guards observer).map (Guard.addOutside y.root)).map
          (Guard.addOutside z.root)).map (Guard.addMany x.root) := rfl

/-- Observer membership equals the finite conjunction/disjunction guards,
with exactly one possible other owner furnishing the negative tests. -/
theorem Term.guard_semantics {Role : Type u} {Var : Type v} [DecidableEq Role]
    (t : Term Role Var) (observer other : Role)
    (ht : t.OwnersIn (fun r => r = observer ∨ r = other)) (v : Var → WinnerSet Role) :
    observer ∈ (t.eval v).val ↔ Eval (t.guards observer)
      (fun j => (v j).Ambiguous) (fun j => v j ≠ WinnerSet.singleton other)
      (fun j => observer ∈ (v j).val) := by
  induction t using Term.induction_owner with
  | var j => simp [Term.eval_var, Term.guards_var, Eval, Guard.Holds]
  | step s t hs ht' =>
    simp only [Term.eval_step, Term.guards_step, WinnerSet.mem_reset, eval_append, eval_many,
      ht' ht.2, hs ht.1, Term.ambiguous_iff]
  | guarded r x y z hx hy hz =>
    by_cases he : r = observer
    · subst r
      simp only [Term.eval_guarded, WinnerSet.guardedChoice, WinnerSet.mem_reset,
        WinnerSet.mem_choice_owner, Term.guards_guarded, ite_true, eval_append, eval_many,
        hx ht.2.1, hy ht.2.2.1, hz ht.2.2.2, Term.ambiguous_iff]
    · have ho : r = other := ht.1.resolve_left he
      subst r
      simp only [Term.eval_guarded, WinnerSet.guardedChoice, WinnerSet.mem_reset,
        WinnerSet.mem_choice_other other observer he, Term.guards_guarded, ite_eq_right he,
        eval_append, eval_many, eval_outside,
        hx ht.2.1, hy ht.2.2.1, hz ht.2.2.2, Term.ambiguous_iff]
      have hy' := y.eq_singleton_iff v other
      have hz' := z.eq_singleton_iff v other
      grind

theorem Guard.dominates_sound {Var : Type*} (weak strong : Guard Var)
    (h : weak.Dominates strong) (M N V : Var → Prop)
    (hmn : ∀ j, M j → N j) (hvn : ∀ j, V j → N j)
    (hs : strong.Holds M N V) : weak.Holds M N V := by
  refine ⟨fun j hj => hs.1 j (h.2.1 j hj), ?_, h.1 ▸ hs.2.2⟩
  intro j hj
  rcases h.2.2 j hj with hm | hn | he
  · exact hmn j (hs.1 j hm)
  · exact hs.2.1 j hn
  · exact he ▸ hvn strong.source hs.2.2

theorem covers_sound {Var : Type*} (left right : List (Guard Var)) (h : Covers left right)
    (M N V : Var → Prop) (hmn : ∀ j, M j → N j) (hvn : ∀ j, V j → N j) :
    Eval left M N V → Eval right M N V := by
  rintro ⟨g, hg, hs⟩
  obtain ⟨q, hq, hdom⟩ := h g hg
  exact ⟨q, hq, q.dominates_sound g hdom M N V hmn hvn hs⟩

/-- The generated list counts original leaf occurrences, including repeats. -/
theorem Term.guards_length {Role : Type u} {Var : Type v} [DecidableEq Role]
    (t : Term Role Var) (observer : Role) : (t.guards observer).length = t.leafCount := by
  induction t using Term.induction_owner with
  | var => rfl
  | step s t hs ht => simp only [Term.guards_step, List.length_append, List.length_map, hs, ht, Term.leafCount_step]; omega
  | guarded r x y z hx hy hz =>
    by_cases he : r = observer <;>
      simp only [Term.guards_guarded, he, ite_true, ite_false, List.length_append, List.length_map, hx, hy, hz, Term.leafCount_guarded] <;> omega

end KFOL.Owner
