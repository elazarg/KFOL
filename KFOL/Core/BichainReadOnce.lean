module

public import KFOL.Core.BichainCanonical

/-! # Read-once Boolean formulas realize their canonical extensions

Disjoint child supports allow a pivotal child edge to be combined with a
Boolean endpoint assignment for its sibling. No value-table enumeration is used.
-/

@[expose] public section
namespace KFOL.Bichain

namespace Value

private theorem inf_possible_iff : ∀ x y : Value,
    inf x y = .possible ↔
      (x = .possible ∧ y ≠ .b) ∨ (y = .possible ∧ x ≠ .b) := by decide +kernel
private theorem sup_possible_iff : ∀ x y : Value,
    sup x y = .possible ↔
      (x = .possible ∧ y ≠ .c) ∨ (y = .possible ∧ x ≠ .c) := by decide +kernel

private theorem inf_comm : ∀ x y : Value, inf x y = inf y x := by decide +kernel
private theorem sup_comm : ∀ x y : Value, sup x y = sup y x := by decide +kernel

private theorem lower_inf : ∀ x y : Value,
    ofBool (inf x y == .c) = inf (ofBool (x == .c)) (ofBool (y == .c)) := by decide +kernel
private theorem lower_sup : ∀ x y : Value,
    ofBool (sup x y == .c) = sup (ofBool (x == .c)) (ofBool (y == .c)) := by decide +kernel
private theorem upper_inf : ∀ x y : Value,
    ofBool (inf x y != .b) = inf (ofBool (x != .b)) (ofBool (y != .b)) := by decide +kernel
private theorem upper_sup : ∀ x y : Value,
    ofBool (sup x y != .b) = sup (ofBool (x != .b)) (ofBool (y != .b)) := by decide +kernel

end Value

variable {Var : Type*} [DecidableEq Var]

omit [DecidableEq Var] in
/-- Every bichain input defines a genuine Boolean interval. -/
theorem cubeLower_le_cubeUpper (v : Var → Value) : cubeLower v ≤ cubeUpper v := by
  intro j
  change (v j == .c) ≤ (v j != .b)
  cases v j <;> decide

namespace Term

/-- Evaluation depends only on the names present in the term. -/
theorem eval_agree_variables (t : Term Var) (v w : Var → Value)
    (h : ∀ j ∈ t.vars, v j = w j) : t.eval v = t.eval w := by
  induction t with
  | var j => exact h j (Finset.mem_singleton_self j)
  | inf s t ihs iht =>
    exact congrArg₂ Value.inf (ihs (fun j hj => h j (Finset.mem_union_left _ hj)))
      (iht (fun j hj => h j (Finset.mem_union_right _ hj)))
  | sup s t ihs iht =>
    exact congrArg₂ Value.sup (ihs (fun j hj => h j (Finset.mem_union_left _ hj)))
      (iht (fun j hj => h j (Finset.mem_union_right _ hj)))
  | union s t ihs iht =>
    exact congrArg₂ Value.union (ihs (fun j hj => h j (Finset.mem_union_left _ hj)))
      (iht (fun j hj => h j (Finset.mem_union_right _ hj)))

theorem IsReadOnce.isPure {t : Term Var} (ht : t.IsReadOnce) : t.IsPure := by
  induction t with
  | var => trivial
  | inf s t ihs iht => exact ⟨ihs ht.1, iht ht.2.1⟩
  | sup s t ihs iht => exact ⟨ihs ht.1, iht ht.2.1⟩
  | union => exact ht.elim

omit [DecidableEq Var] in
theorem pure_eval_cubeLower (t : Term Var) (ht : t.IsPure) (v : Var → Value) :
    t.eval (fun j => Value.ofBool (cubeLower v j)) = Value.ofBool (t.eval v == .c) := by
  induction t with
  | var => rfl
  | inf s t ihs iht =>
    simpa only [eval, ihs ht.1, iht ht.2] using (Value.lower_inf (s.eval v) (t.eval v)).symm
  | sup s t ihs iht =>
    simpa only [eval, ihs ht.1, iht ht.2] using (Value.lower_sup (s.eval v) (t.eval v)).symm
  | union => exact ht.elim

omit [DecidableEq Var] in
theorem pure_eval_cubeUpper (t : Term Var) (ht : t.IsPure) (v : Var → Value) :
    t.eval (fun j => Value.ofBool (cubeUpper v j)) = Value.ofBool (t.eval v != .b) := by
  induction t with
  | var => rfl
  | inf s t ihs iht =>
    simpa only [eval, ihs ht.1, iht ht.2] using (Value.upper_inf (s.eval v) (t.eval v)).symm
  | sup s t ihs iht =>
    simpa only [eval, ihs ht.1, iht ht.2] using (Value.upper_sup (s.eval v) (t.eval v)).symm
  | union => exact ht.elim

omit [DecidableEq Var] in
private theorem pure_upper_c (t : Term Var) (ht : t.IsPure) (v : Var → Value)
    (hv : t.eval v ≠ .b) : t.eval (fun j => Value.ofBool (cubeUpper v j)) = .c := by
  rw [pure_eval_cubeUpper t ht]
  cases h : t.eval v <;> simp_all [Value.ofBool] <;> rfl

omit [DecidableEq Var] in
private theorem pure_lower_b (t : Term Var) (ht : t.IsPure) (v : Var → Value)
    (hv : t.eval v ≠ .c) : t.eval (fun j => Value.ofBool (cubeLower v j)) = .b := by
  rw [pure_eval_cubeLower t ht]
  cases h : t.eval v <;> simp_all [Value.ofBool] <;> rfl

/-- A Boolean cube contains both endpoints of a pivotal term edge. -/
private def Pivotal (t : Term Var) (lower upper : Var → Bool) (j : Var) : Prop :=
  ∃ w : Var → Bool, InCube lower upper w ∧ w j = false ∧
    InCube lower upper (Function.update w j true) ∧
    t.eval (fun i => Value.ofBool (w i)) = .b ∧
    t.eval (fun i => Value.ofBool (Function.update w j true i)) = .c

/-- Merge a child edge and a disjoint sibling's endpoint assignment. -/
private theorem merge_edge (s t : Term Var) (lower upper w endpoint : Var → Bool) (j : Var)
    (hd : Disjoint s.vars t.vars) (hj : j ∈ s.vars)
    (hw : InCube lower upper w) (hwu : InCube lower upper (Function.update w j true))
    (he : InCube lower upper endpoint) :
    ∃ w', InCube lower upper w' ∧ w' j = w j ∧
      InCube lower upper (Function.update w' j true) ∧
      s.eval (fun i => Value.ofBool (w' i)) = s.eval (fun i => Value.ofBool (w i)) ∧
      s.eval (fun i => Value.ofBool (Function.update w' j true i)) =
        s.eval (fun i => Value.ofBool (Function.update w j true i)) ∧
      t.eval (fun i => Value.ofBool (w' i)) = t.eval (fun i => Value.ofBool (endpoint i)) ∧
      t.eval (fun i => Value.ofBool (Function.update w' j true i)) =
        t.eval (fun i => Value.ofBool (endpoint i)) := by
  classical
  let w' := fun i => if i ∈ s.vars then w i else endpoint i
  have hmix : ∀ a b, InCube lower upper a → InCube lower upper b →
      InCube lower upper (fun i => if i ∈ s.vars then a i else b i) := by
    intro a b ha hb
    constructor
    · intro i
      change lower i ≤ (if i ∈ s.vars then a i else b i)
      split_ifs
      · exact ha.1 i
      · exact hb.1 i
    · intro i
      change (if i ∈ s.vars then a i else b i) ≤ upper i
      split_ifs
      · exact ha.2 i
      · exact hb.2 i
  have hupdate : Function.update w' j true =
      fun i => if i ∈ s.vars then Function.update w j true i else endpoint i := by
    funext i
    by_cases hij : i = j
    · subst i; simp [hj]
    · simp [w', hij]
  refine ⟨w', hmix w endpoint hw he, by simp [w', hj], ?_, ?_, ?_, ?_, ?_⟩
  · rw [hupdate]
    exact hmix _ _ hwu he
  · apply eval_agree_variables
    intro i hi
    simp [w', hi]
  · apply eval_agree_variables
    intro i hi
    rw [hupdate]
    simp [hi]
  · apply eval_agree_variables
    intro i hi
    have hni : i ∉ s.vars := fun hsi => Finset.disjoint_left.mp hd hsi hi
    simp [w', hni]
  · apply eval_agree_variables
    intro i hi
    have hni : i ∉ s.vars := fun hsi => Finset.disjoint_left.mp hd hsi hi
    rw [hupdate]
    simp [hni]

private theorem pivotal_inf_left (s t : Term Var) (lower upper endpoint : Var → Bool)
    (j : Var) (hd : Disjoint s.vars t.vars) (hj : j ∈ s.vars)
    (hp : Pivotal s lower upper j) (he : InCube lower upper endpoint)
    (hte : t.eval (fun i => Value.ofBool (endpoint i)) = .c) :
    Pivotal (.inf s t) lower upper j := by
  obtain ⟨w, hw, hwj, hwu, hwb, hwc⟩ := hp
  obtain ⟨w', hw', hwj', hwu', hs₀, hs₁, ht₀, ht₁⟩ :=
    merge_edge s t lower upper w endpoint j hd hj hw hwu he
  refine ⟨w', hw', hwj'.trans hwj, hwu', ?_, ?_⟩
  · change Value.inf _ _ = .b
    rw [hs₀, ht₀, hwb, hte]
    rfl
  · change Value.inf _ _ = .c
    rw [hs₁, ht₁, hwc, hte]
    rfl

private theorem pivotal_sup_left (s t : Term Var) (lower upper endpoint : Var → Bool)
    (j : Var) (hd : Disjoint s.vars t.vars) (hj : j ∈ s.vars)
    (hp : Pivotal s lower upper j) (he : InCube lower upper endpoint)
    (hte : t.eval (fun i => Value.ofBool (endpoint i)) = .b) :
    Pivotal (.sup s t) lower upper j := by
  obtain ⟨w, hw, hwj, hwu, hwb, hwc⟩ := hp
  obtain ⟨w', hw', hwj', hwu', hs₀, hs₁, ht₀, ht₁⟩ :=
    merge_edge s t lower upper w endpoint j hd hj hw hwu he
  refine ⟨w', hw', hwj'.trans hwj, hwu', ?_, ?_⟩
  · change Value.sup _ _ = .b
    rw [hs₀, ht₀, hwb, hte]
    rfl
  · change Value.sup _ _ = .c
    rw [hs₁, ht₁, hwc, hte]
    rfl

private theorem pivotal_congr {s t : Term Var} (h : ∀ v, s.eval v = t.eval v)
    {lower upper : Var → Bool} {j : Var} : Pivotal s lower upper j → Pivotal t lower upper j := by
  rintro ⟨w, hw, hwj, hwu, hwb, hwc⟩
  exact ⟨w, hw, hwj, hwu, (h _).symm.trans hwb, (h _).symm.trans hwc⟩

private theorem readOnce_pivotal (t : Term Var) (ht : t.IsReadOnce) (v : Var → Value)
    (hp : t.eval v = .possible) :
    ∃ j, j ∈ t.vars ∧ v j = .possible ∧ Pivotal t (cubeLower v) (cubeUpper v) j := by
  have hlu := cubeLower_le_cubeUpper v
  induction t with
  | var j =>
    change v j = .possible at hp
    refine ⟨j, Finset.mem_singleton_self j, hp, cubeLower v, ⟨le_rfl, hlu⟩, ?_, ?_, ?_, ?_⟩
    · change (v j == .c) = false
      rw [hp]
      rfl
    · constructor
      · intro i
        by_cases hij : i = j
        · subst i
          simp only [Function.update_self]
          change (v j == .c) ≤ true
          rw [hp]
          decide
        · simp [hij]
      · intro i
        by_cases hij : i = j
        · subst i
          simp only [Function.update_self]
          change true ≤ (v j != .b)
          rw [hp]
          decide
        · simpa [hij] using hlu i
    · change Value.ofBool (v j == .c) = .b
      rw [hp]
      rfl
    · simp [eval]
      rfl
  | inf s t ihs iht =>
    rcases (Value.inf_possible_iff _ _).mp hp with ⟨hs, ht'⟩ | ⟨ht', hs⟩
    · obtain ⟨j, hj, hjp, hpj⟩ := ihs ht.1 hs
      refine ⟨j, Finset.mem_union_left _ hj, hjp, ?_⟩
      exact pivotal_inf_left s t _ _ (cubeUpper v) j ht.2.2 hj hpj ⟨hlu, le_rfl⟩
        (pure_upper_c t ht.2.1.isPure v ht')
    · obtain ⟨j, hj, hjp, hpj⟩ := iht ht.2.1 ht'
      refine ⟨j, Finset.mem_union_right _ hj, hjp, ?_⟩
      apply pivotal_congr (s := .inf t s) (t := .inf s t)
        (fun w => Value.inf_comm (t.eval w) (s.eval w))
      exact pivotal_inf_left t s _ _ (cubeUpper v) j ht.2.2.symm hj hpj ⟨hlu, le_rfl⟩
        (pure_upper_c s ht.1.isPure v hs)
  | sup s t ihs iht =>
    rcases (Value.sup_possible_iff _ _).mp hp with ⟨hs, ht'⟩ | ⟨ht', hs⟩
    · obtain ⟨j, hj, hjp, hpj⟩ := ihs ht.1 hs
      refine ⟨j, Finset.mem_union_left _ hj, hjp, ?_⟩
      exact pivotal_sup_left s t _ _ (cubeLower v) j ht.2.2 hj hpj ⟨le_rfl, hlu⟩
        (pure_lower_b t ht.2.1.isPure v ht')
    · obtain ⟨j, hj, hjp, hpj⟩ := iht ht.2.1 ht'
      refine ⟨j, Finset.mem_union_right _ hj, hjp, ?_⟩
      apply pivotal_congr (s := .sup t s) (t := .sup s t)
        (fun w => Value.sup_comm (t.eval w) (s.eval w))
      exact pivotal_sup_left t s _ _ (cubeLower v) j ht.2.2.symm hj hpj ⟨le_rfl, hlu⟩
        (pure_lower_b s ht.1.isPure v hs)
  | union => exact ht.elim

/-- A marked pivotal Boolean edge forces possible in every term with that
Boolean restriction. Repeated sources and observer union are permitted. -/
theorem possible_of_essential (t : Term Var) (f : (Var → Bool) → Bool)
    (hbool : ∀ a, t.eval (fun i => Value.ofBool (a i)) = Value.ofBool (f a))
    (v : Var → Value) (j : Var) (hj : v j = .possible)
    (he : Essential f (cubeLower v) (cubeUpper v) j) : t.eval v = .possible := by
  obtain ⟨w, hw, hwj, hwu, hf₀, hf₁⟩ := he
  have ht₀ : t.eval (fun i => Value.ofBool (w i)) = .b := by rw [hbool, hf₀]; rfl
  have ht₁ : t.eval (fun i => Value.ofBool (Function.update w j true i)) = .c := by
    rw [hbool, hf₁]; rfl
  obtain ⟨i, hi₁, hi₀, hi⟩ := t.stable_separating_source _ _ ht₁ ht₀
  have hij : i = j := by
    by_contra hne
    simp [Function.update_of_ne hne, hi₀] at hi₁
  subst i
  apply hi v
  · intro i hai
    have hu : cubeUpper v i = true := (Bool.le_iff_imp.mp (hwu.2 i)) hai
    simpa [cubeUpper] using hu
  · intro i hvi
    apply (Bool.le_iff_imp.mp (hw.1 i))
    change (v i == .c) = true
    rw [hvi]
    rfl
  · exact hj

private theorem ofBool_injective : Function.Injective Value.ofBool := by
  intro x y h
  cases x <;> cases y <;> simp_all [Value.ofBool]

/-- Every read-once formula realizes the independently defined canonical
extension of its Boolean function. -/
theorem IsReadOnce.canonical [Fintype Var] {t : Term Var} (ht : t.IsReadOnce)
    (f : (Var → Bool) → Bool)
    (hbool : ∀ a, t.eval (fun i => Value.ofBool (a i)) = Value.ofBool (f a)) :
    ∀ v, t.eval v = canonicalExtension f v := by
  intro v
  have hl : f (cubeLower v) = (t.eval v == .c) :=
    ofBool_injective ((hbool _).symm.trans (pure_eval_cubeLower t ht.isPure v))
  have hu : f (cubeUpper v) = (t.eval v != .b) :=
    ofBool_injective ((hbool _).symm.trans (pure_eval_cubeUpper t ht.isPure v))
  cases hv : t.eval v with
  | b =>
    rw [hv] at hl hu
    change f (cubeLower v) = false at hl
    change f (cubeUpper v) = false at hu
    simp [canonicalExtension, hl, hu]
  | c =>
    rw [hv] at hl hu
    change f (cubeLower v) = true at hl
    simp [canonicalExtension, hl]
  | possible =>
    rw [hv] at hl hu
    obtain ⟨j, _, hj, w, hw, hwj, hwu, hw₀, hw₁⟩ := readOnce_pivotal t ht v hv
    have he : Essential f (cubeLower v) (cubeUpper v) j := by
      refine ⟨w, hw, hwj, hwu, ?_, ?_⟩
      · exact ofBool_injective ((hbool _).symm.trans hw₀)
      · exact ofBool_injective ((hbool _).symm.trans hw₁)
    change f (cubeLower v) = false at hl
    change f (cubeUpper v) = true at hu
    simp [canonicalExtension, hl, hu, show ∃ i, v i = .possible ∧
      Essential f (cubeLower v) (cubeUpper v) i from ⟨j, hj, he⟩]
  | neutral =>
    rw [hv] at hl hu
    have hn : ¬ ∃ j, v j = .possible ∧ Essential f (cubeLower v) (cubeUpper v) j := by
      rintro ⟨j, hj, he⟩
      have hp := possible_of_essential t f hbool v j hj he
      rw [hv] at hp
      contradiction
    change f (cubeLower v) = false at hl
    change f (cubeUpper v) = true at hu
    simp [canonicalExtension, hl, hu, hn]

end Term
end KFOL.Bichain
