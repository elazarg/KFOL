module

public import KFOL.Owner.Guards
public import KFOL.Algorithms.FiniteTermCode
public import Mathlib.Tactic.Linarith

/-! # Uniform outsider guards and polynomial native annotation size

Every input is the original one-owner tree. Bounds retain the binary lengths
of sparse variable names and every repeated root prerequisite. -/

@[expose] public section

namespace KFOL.Owner

universe u v

namespace Term

variable {Role : Type u} {Var : Type v}

@[simp] theorem root_withOwner (t : Term Unit Var) (owner : Role) :
    (t.withOwner owner).root = t.root := by
  induction t using induction_owner with
  | var => rfl
  | step s t hs ht => exact ht
  | guarded r x y z hx hy hz => exact hx

private theorem withOwner_step_aux (owner : Role) (s t : Term Unit Var) :
    (step s t).withOwner owner = step (s.withOwner owner) (t.withOwner owner) := rfl

private theorem withOwner_guarded_aux (owner : Role) (r : Unit) (x y z : Term Unit Var) :
    (guarded r x y z).withOwner owner =
      guarded owner (x.withOwner owner) (y.withOwner owner) (z.withOwner owner) := rfl

/-- At every outsider, all H nodes contribute both outside tests. The raw
lists, their order and repeated tests are independent of the role carrier. -/
theorem guards_withOwner_outsider [DecidableEq Role] (t : Term Unit Var)
    (owner observer : Role) (hne : observer ≠ owner) :
    (t.withOwner owner).guards observer = (t.withOwner false).guards true := by
  induction t using induction_owner with
  | var => rfl
  | step s t hs ht =>
    simp only [withOwner_step_aux, guards_step, root_withOwner, hs, ht]
  | guarded r x y z hx hy hz =>
    simp only [withOwner_guarded_aux, guards_guarded, hne.symm, Bool.false_eq_true, ite_false,
      root_withOwner, hx, hy, hz]

end Term

namespace Guard

@[simp] theorem payloadWeight_addMany {Var : Type*} (weight : Var → ℕ) (j : Var) (g : Guard Var) :
    (g.addMany j).payloadWeight weight = g.payloadWeight weight + 2 * weight j := by
  simp only [payloadWeight, addMany, List.map_cons, List.sum_cons]
  omega

@[simp] theorem payloadWeight_addOutside {Var : Type*} (weight : Var → ℕ) (j : Var) (g : Guard Var) :
    (g.addOutside j).payloadWeight weight = g.payloadWeight weight + weight j := by
  simp only [payloadWeight, addOutside, List.map_cons, List.sum_cons]
  omega

end Guard

namespace Term

variable [Fintype (FiniteTermCode.Operation (Symbol Unit))]

private theorem length_encode_var (j : ℕ) :
    (FiniteTermCode.encode (Symbol Unit) (.var j)).length = 2 * j.bits.length + 3 := by
  simp only [FiniteTermCode.encode_var, List.length_cons, Words.delimit_length, Words.BinaryNatCode.encode]

private theorem length_encode_step (s t : Term Unit ℕ) :
    1 + (FiniteTermCode.encode (Symbol Unit) s).length + (FiniteTermCode.encode (Symbol Unit) t).length ≤
      (FiniteTermCode.encode (Symbol Unit) (step s t)).length := by
  simp [step, FiniteTermCode.encode_func, List.ofFn_succ]
  omega

private theorem length_encode_guarded (r : Unit) (x y z : Term Unit ℕ) :
    1 + (FiniteTermCode.encode (Symbol Unit) x).length + (FiniteTermCode.encode (Symbol Unit) y).length +
      (FiniteTermCode.encode (Symbol Unit) z).length ≤
      (FiniteTermCode.encode (Symbol Unit) (guarded r x y z)).length := by
  simp [guarded, FiniteTermCode.encode_func, List.ofFn_succ]
  omega

/-- The root label occupies an original variable leaf in the code. -/
theorem root_nameWeight_le_encode (t : Term Unit ℕ) :
    2 * t.root.bits.length + 1 ≤ (FiniteTermCode.encode (Symbol Unit) t).length := by
  induction t using induction_owner with
  | var j => rw [root_var, length_encode_var]; omega
  | step s t hs ht =>
    have h := length_encode_step s t
    rw [root_step]
    omega
  | guarded r x y z hx hy hz =>
    have h := length_encode_guarded r x y z
    rw [root_guarded]
    omega

theorem leafCount_le_encode (t : Term Unit ℕ) :
    t.leafCount ≤ (FiniteTermCode.encode (Symbol Unit) t).length := by
  induction t using induction_owner with
  | var j => rw [leafCount_var, length_encode_var]; omega
  | step s t hs ht =>
    have h := length_encode_step s t
    rw [leafCount_step]
    omega
  | guarded r x y z hx hy hz =>
    have h := length_encode_guarded r x y z
    rw [leafCount_guarded]
    omega

end Term
end KFOL.Owner

namespace KFOL.Owner.Term

universe u v

variable [Fintype (FiniteTermCode.Operation (Symbol Unit))]

omit [Fintype (FiniteTermCode.Operation (Symbol Unit))] in
private theorem quadratic_extension (child total parent : ℕ) (hchild : child ≤ total)
    (hparent : total + 1 ≤ parent) :
    2 * child ^ 2 + 2 * total ≤ 2 * parent ^ 2 := by
  have hc := Nat.pow_le_pow_left hchild 2
  have hp := Nat.pow_le_pow_left hparent 2
  nlinarith

/-- A raw guard's framed payload has quadratic size in the original tree
code, including repeated long root names. -/
theorem guard_payloadWeight_le_encode (t : Term Unit ℕ) (g : Guard ℕ)
    (hg : g ∈ (t.withOwner false).guards true) :
    g.payloadWeight (fun j => 2 * j.bits.length + 1) ≤
      2 * (FiniteTermCode.encode (Symbol Unit) t).length ^ 2 := by
  induction t using induction_owner generalizing g with
  | var j =>
    change g ∈ [⟨j, [], []⟩] at hg
    have he : g = ⟨j, [], []⟩ := List.mem_singleton.mp hg
    subst g
    rw [length_encode_var]
    simp only [Guard.payloadWeight, List.map_nil, List.sum_nil, Nat.mul_zero, Nat.add_zero]
    nlinarith
  | step s t hs ht =>
    rw [withOwner_step_aux, guards_step] at hg
    have hcode := length_encode_step s t
    rcases List.mem_append.mp hg with hg | hg
    · have hbound := ht g hg
      have hsquare := Nat.pow_le_pow_left
        (show (FiniteTermCode.encode (Symbol Unit) t).length ≤
          (FiniteTermCode.encode (Symbol Unit) (step s t)).length by omega) 2
      omega
    · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
      rw [Guard.payloadWeight_addMany, root_withOwner]
      have hbound := hs h hh
      have hroot := root_nameWeight_le_encode t
      have hext := quadratic_extension
        (FiniteTermCode.encode (Symbol Unit) s).length
        ((FiniteTermCode.encode (Symbol Unit) s).length + (FiniteTermCode.encode (Symbol Unit) t).length)
        (FiniteTermCode.encode (Symbol Unit) (step s t)).length (by omega) (by omega)
      omega
  | guarded r x y z hx hy hz =>
    rw [withOwner_guarded_aux, guards_guarded] at hg
    simp only [Bool.false_eq_true, ite_false] at hg
    have hcode := length_encode_guarded r x y z
    rcases List.mem_append.mp hg with hg | hg
    · have hbound := hx g hg
      have hsquare := Nat.pow_le_pow_left
        (show (FiniteTermCode.encode (Symbol Unit) x).length ≤
          (FiniteTermCode.encode (Symbol Unit) (guarded r x y z)).length by omega) 2
      omega
    · obtain ⟨g₁, hg₁, rfl⟩ := List.mem_map.mp hg
      obtain ⟨g₂, hg₂, rfl⟩ := List.mem_map.mp hg₁
      obtain ⟨g₃, hg₃, rfl⟩ := List.mem_map.mp hg₂
      rw [Guard.payloadWeight_addMany, Guard.payloadWeight_addOutside,
        Guard.payloadWeight_addOutside, root_withOwner, root_withOwner, root_withOwner]
      have hrootx := root_nameWeight_le_encode x
      have hrooty := root_nameWeight_le_encode y
      have hrootz := root_nameWeight_le_encode z
      rcases List.mem_append.mp hg₃ with hg₃ | hg₃
      · have hbound := hy g₃ hg₃
        have hext := quadratic_extension
          (FiniteTermCode.encode (Symbol Unit) y).length
          ((FiniteTermCode.encode (Symbol Unit) x).length +
            (FiniteTermCode.encode (Symbol Unit) y).length + (FiniteTermCode.encode (Symbol Unit) z).length)
          (FiniteTermCode.encode (Symbol Unit) (guarded r x y z)).length (by omega) (by omega)
        omega
      · have hbound := hz g₃ hg₃
        have hext := quadratic_extension
          (FiniteTermCode.encode (Symbol Unit) z).length
          ((FiniteTermCode.encode (Symbol Unit) x).length +
            (FiniteTermCode.encode (Symbol Unit) y).length + (FiniteTermCode.encode (Symbol Unit) z).length)
          (FiniteTermCode.encode (Symbol Unit) (guarded r x y z)).length (by omega) (by omega)
        omega

end KFOL.Owner.Term

namespace KFOL.Owner.Term

universe u v

@[simp] theorem leafCount_withOwner {Role : Type u} {Var : Type v} (t : Term Unit Var) (owner : Role) :
    (t.withOwner owner).leafCount = t.leafCount := by
  induction t using induction_owner with
  | var => rfl
  | step s t hs ht =>
    change (s.withOwner owner).leafCount + (t.withOwner owner).leafCount = s.leafCount + t.leafCount
    rw [hs, ht]
  | guarded r x y z hx hy hz =>
    change (x.withOwner owner).leafCount + (y.withOwner owner).leafCount + (z.withOwner owner).leafCount =
      x.leafCount + y.leafCount + z.leafCount
    rw [hx, hy, hz]

private theorem sum_map_le_constant {α : Type*} (xs : List α) (f : α → ℕ) (bound : ℕ)
    (h : ∀ x ∈ xs, f x ≤ bound) : (xs.map f).sum ≤ xs.length * bound := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self ..)
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- The complete root/raw-guard annotation has cubic size in the original
encoded one-owner tree. The bound is uniform in role count and binary labels,
and valid for every numbering of the fixed Unit signature. -/
theorem guardAnnotationWeight_le_encode
    [Fintype (FiniteTermCode.Operation (Symbol Unit))] (t : Term Unit ℕ) :
    (t.withOwner false).guardAnnotationWeight (fun j => 2 * j.bits.length + 1) true ≤
      6 * ((FiniteTermCode.encode (Symbol Unit) t).length + 1) ^ 3 := by
  let N := (FiniteTermCode.encode (Symbol Unit) t).length
  have hroot : 2 * t.root.bits.length + 1 ≤ N := t.root_nameWeight_le_encode
  have hlength : ((t.withOwner false).guards true).length ≤ N := by
    rw [guards_length, leafCount_withOwner]
    exact t.leafCount_le_encode
  have hsum := sum_map_le_constant ((t.withOwner false).guards true)
    (fun g => 2 * g.payloadWeight (fun j => 2 * j.bits.length + 1) + 1)
    (4 * N ^ 2 + 1) (by
      intro g hg
      have h := t.guard_payloadWeight_le_encode g hg
      change g.payloadWeight (fun j => 2 * j.bits.length + 1) ≤ 2 * N ^ 2 at h
      omega)
  have hmul := Nat.mul_le_mul_right (4 * N ^ 2 + 1) hlength
  rw [guardAnnotationWeight, root_withOwner]
  change 2 * t.root.bits.length + 1 + _ ≤ 6 * (N + 1) ^ 3
  nlinarith

/-- The same original-code bound applies at every actual outsider role. -/
theorem guardAnnotationWeight_withOwner_le_encode {Role : Type u} [DecidableEq Role]
    [Fintype (FiniteTermCode.Operation (Symbol Unit))] (t : Term Unit ℕ)
    (owner observer : Role) (hne : observer ≠ owner) :
    (t.withOwner owner).guardAnnotationWeight (fun j => 2 * j.bits.length + 1) observer ≤
      6 * ((FiniteTermCode.encode (Symbol Unit) t).length + 1) ^ 3 := by
  simpa only [guardAnnotationWeight, guards_withOwner_outsider t owner observer hne,
    root_withOwner] using t.guardAnnotationWeight_le_encode

end KFOL.Owner.Term
