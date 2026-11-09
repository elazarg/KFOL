module

public import KFOL.Owner.Separation

/-! # Observer completeness and the single-outsider equality criterion -/

@[expose] public section

namespace KFOL.Owner

universe u v

variable {Role : Type u} {Var : Type v} [DecidableEq Role]

theorem Term.observation_implication_iff [DecidableEq Var] (left right : Term Role Var)
    (observer other background : Role)
    (hko : observer ≠ other) (hkb : observer ≠ background) (hob : other ≠ background)
    (hl : left.OwnersIn (fun r => r = observer ∨ r = other))
    (hr : right.OwnersIn (fun r => r = observer ∨ r = other)) :
    Covers (left.guards observer) (right.guards observer) ↔
      ∀ v, observer ∈ (left.eval v).val → observer ∈ (right.eval v).val := by
  rw [covers_iff observer other background hko hkb hob]
  simp only [← left.guard_semantics observer other hl, ← right.guard_semantics observer other hr]

theorem Term.observation_equation_iff [DecidableEq Var] (left right : Term Role Var)
    (observer other background : Role)
    (hko : observer ≠ other) (hkb : observer ≠ background) (hob : other ≠ background)
    (hl : left.OwnersIn (fun r => r = observer ∨ r = other))
    (hr : right.OwnersIn (fun r => r = observer ∨ r = other)) :
    (Covers (left.guards observer) (right.guards observer) ∧
      Covers (right.guards observer) (left.guards observer)) ↔
      ∀ v, (observer ∈ (left.eval v).val ↔ observer ∈ (right.eval v).val) := by
  rw [left.observation_implication_iff right observer other background hko hkb hob hl hr,
    right.observation_implication_iff left observer other background hko hkb hob hr hl]
  constructor
  · exact fun h v => ⟨h.1 v, h.2 v⟩
  · exact fun h => ⟨fun v => (h v).mp, fun v => (h v).mpr⟩

/-- The failed guard itself indexes the explicit countervaluation, with
at most two winners per input and only the three named roles used. -/
theorem Term.observation_countervaluation [DecidableEq Var] (left right : Term Role Var)
    (observer other background : Role)
    (hko : observer ≠ other) (hkb : observer ≠ background) (hob : other ≠ background)
    (hl : left.OwnersIn (fun r => r = observer ∨ r = other))
    (hr : right.OwnersIn (fun r => r = observer ∨ r = other))
    (h : ¬Covers (left.guards observer) (right.guards observer)) :
    ∃ g ∈ left.guards observer,
      observer ∈ (left.eval (minimalVal observer other background g)).val ∧
      observer ∉ (right.eval (minimalVal observer other background g)).val ∧
      ∀ j, ∃ a ∈ ({observer, other, background} : Set Role),
        ∃ b ∈ ({observer, other, background} : Set Role),
          minimalVal observer other background g j =
            (WinnerSet.singleton a).union (WinnerSet.singleton b) := by
  obtain ⟨g, hg, hleft, hright⟩ := countervaluation_of_not_covers observer other background
    hko hkb hob _ _ h
  exact ⟨g, hg, (left.guard_semantics observer other hl _).mpr hleft,
    fun hm => hright ((right.guard_semantics observer other hr _).mp hm),
    minimalVal_pair observer other background g⟩

theorem Term.guards_other (t : Term Role Var) (owner first second : Role)
    (ht : t.OwnersIn (fun r => r = owner)) (hf : first ≠ owner) (hs : second ≠ owner) :
    t.guards first = t.guards second := by
  induction t using Term.induction_owner with
  | var j => rfl
  | step s t hl hr => simp only [Term.guards_step, hl ht.1, hr ht.2]
  | guarded r x y z hx hy hz =>
    have he : r = owner := ht.1
    subst r
    simp only [Term.guards_guarded, ite_eq_right hf.symm, ite_eq_right hs.symm,
      hx ht.2.1, hy ht.2.2.1, hz ht.2.2.2]

theorem covers_forget (left right : List (Guard Var)) (h : Covers left right) :
    Covers (left.map Guard.forget) (right.map Guard.forget) := by
  intro g hg
  obtain ⟨source, hs, rfl⟩ := List.mem_map.mp hg
  obtain ⟨target, ht, he⟩ := h source hs
  refine ⟨target.forget, List.mem_map.mpr ⟨target, ht, rfl⟩, he.1, he.2.1, ?_⟩
  simp [Guard.forget]

@[simp] theorem forget_addMany (j : Var) (g : Guard Var) :
    (g.addMany j).forget = g.forget.addMany j := rfl

@[simp] theorem forget_addOutside (j : Var) (g : Guard Var) :
    (g.addOutside j).forget = g.forget := rfl

/-- The owner's guard list is recovered from any outsider list by removing
only the non-owner-atom tests. -/
theorem Term.owner_guards_from_other (t : Term Role Var) (owner outsider : Role)
    (ht : t.OwnersIn (fun r => r = owner)) (ho : outsider ≠ owner) :
    t.guards owner = (t.guards outsider).map Guard.forget := by
  induction t using Term.induction_owner with
  | var j => rfl
  | step s t hl hr =>
    simp only [Term.guards_step, List.map_append, List.map_map, hl ht.1, hr ht.2,
      Function.comp_def, forget_addMany]
  | guarded r x y z hx hy hz =>
    have he : r = owner := ht.1
    subst r
    simp only [Term.guards_guarded, ite_true, ite_eq_right ho.symm, List.map_append, List.map_map,
      hx ht.2.1, hy ht.2.2.1, hz ht.2.2.2, Function.comp_def, forget_addMany, forget_addOutside]

/-- A single outsider's two-way guard coverage characterizes equality on
all winner-set valuations, for arbitrary variable and role types. -/
theorem Term.single_table_equation_iff [DecidableEq Var] (three : Fin 3 ↪ Role)
    (left right : Term Role Var) (owner outsider : Role) (ho : outsider ≠ owner)
    (hl : left.OwnersIn (fun r => r = owner))
    (hr : right.OwnersIn (fun r => r = owner)) :
    (∀ v : Var → WinnerSet Role, left.eval v = right.eval v) ↔
      Covers (left.guards outsider) (right.guards outsider) ∧
        Covers (right.guards outsider) (left.guards outsider) := by
  have outL := left.owners_mono _ (fun r => r = outsider ∨ r = owner) hl (fun _ h => Or.inr h)
  have outR := right.owners_mono _ (fun r => r = outsider ∨ r = owner) hr (fun _ h => Or.inr h)
  obtain ⟨background, hbo, hbk⟩ := exists_role_outside_pair three owner outsider
  have outTest := left.observation_equation_iff right outsider owner background
    ho hbk.symm hbo.symm outL outR
  constructor
  · intro he
    exact outTest.mpr (fun v => by rw [he v])
  · intro hout v
    apply Subtype.ext
    ext k
    by_cases hk : k = owner
    · subst k
      have ownerL := left.owners_mono _ (fun r => r = owner ∨ r = outsider) hl (fun _ h => Or.inl h)
      have ownerR := right.owners_mono _ (fun r => r = owner ∨ r = outsider) hr (fun _ h => Or.inl h)
      have ownTest := left.observation_equation_iff right owner outsider background
        ho.symm hbo.symm hbk.symm ownerL ownerR
      apply ownTest.mp _ v
      rw [left.owner_guards_from_other owner outsider hl ho,
        right.owner_guards_from_other owner outsider hr ho]
      exact ⟨covers_forget _ _ hout.1, covers_forget _ _ hout.2⟩
    · have lallowed := left.owners_mono _ (fun r => r = k ∨ r = owner) hl (fun _ h => Or.inr h)
      have rallowed := right.owners_mono _ (fun r => r = k ∨ r = owner) hr (fun _ h => Or.inr h)
      obtain ⟨b, hbk', hbo'⟩ := exists_role_outside_pair three k owner
      have kt := left.observation_equation_iff right k owner b hk hbk'.symm hbo'.symm lallowed rallowed
      apply kt.mp _ v
      rw [left.guards_other owner k outsider hl hk ho,
        right.guards_other owner k outsider hr hk ho]
      exact hout

theorem dominatesB_correct [DecidableEq Var] (weak strong : Guard Var) :
    dominatesB weak strong = true ↔ weak.Dominates strong := by
  simp [dominatesB, Guard.Dominates, Bool.and_eq_true, List.all_eq_true, and_assoc]

theorem coversB_correct [DecidableEq Var] (left right : List (Guard Var)) :
    coversB left right = true ↔ Covers left right := by
  simp [coversB, Covers, List.all_eq_true, List.any_eq_true, dominatesB_correct]

/-- Executable observer-equivalence checker correctness. -/
theorem Term.observationB_correct [DecidableEq Var]
    (left right : Term Role Var) (observer other background : Role)
    (hko : observer ≠ other) (hkb : observer ≠ background) (hob : other ≠ background)
    (hl : left.OwnersIn (fun r => r = observer ∨ r = other))
    (hr : right.OwnersIn (fun r => r = observer ∨ r = other)) :
    equationB observer left right = true ↔
      ∀ v, observer ∈ (left.eval v).val ↔ observer ∈ (right.eval v).val := by
  rw [← left.observation_equation_iff right observer other background hko hkb hob hl hr]
  simp [Term.equationB, Bool.and_eq_true, coversB_correct]

/-- Executable one-outsider equality checker correctness; no runtime claim
is included in this semantic theorem. -/
theorem Term.equationB_correct [DecidableEq Var] (three : Fin 3 ↪ Role)
    (owner outsider : Role) (ho : outsider ≠ owner) (left right : Term Role Var)
    (hl : left.OwnersIn (fun r => r = owner)) (hr : right.OwnersIn (fun r => r = owner)) :
    equationB outsider left right = true ↔ ∀ v : Var → WinnerSet Role, left.eval v = right.eval v := by
  rw [left.single_table_equation_iff three right owner outsider ho hl hr]
  simp [Term.equationB, Bool.and_eq_true, coversB_correct]

end KFOL.Owner
