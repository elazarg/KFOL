module

public import KFOL.Core.AtomicNative

/-! # The proper atomic two-role algebra as two compatible Boolean bits -/

@[expose] public section

namespace KFOL.Core

universe u

variable {Role : Type u} [DecidableEq Role]

attribute [local instance] Native.structureOf

/-- The two roles used by the padded grid's local labels. -/
def pairRoles (three : Fin 3 ↪ Role) : Set Role := {three 0,three 1}

omit [DecidableEq Role] in
theorem pairRoles_proper (three : Fin 3 ↪ Role) : pairRoles three ≠ Set.univ := by
  have h20 := three.injective.ne (show (2 : Fin 3) ≠ 0 by decide)
  have h21 := three.injective.ne (show (2 : Fin 3) ≠ 1 by decide)
  intro he
  have hm : three 2 ∈ pairRoles three := he.symm ▸ Set.mem_univ _
  simp [pairRoles, h20, h21] at hm

/-- Simultaneous positive bits receive the neutral lower label, as in the
paper's generator assignment; the ideal never has simultaneous bits. -/
def pairLabelValue (three : Fin 3 ↪ Role) (a b : Bool) : Native Role :=
  if a && !b then .atom (three 0) else if b && !a then .atom (three 1) else .lower

def pairLabel (three : Fin 3 ↪ Role) (a b : Bool) : Native.atomicRestriction (pairRoles three) := by
  refine ⟨pairLabelValue three a b, ?_⟩
  constructor
  · intro role he
    cases a <;> cases b <;> simp_all [pairLabelValue, pairRoles]
  · change pairLabelValue three a b ≠ Native.upper
    cases a <;> cases b <;> simp [pairLabelValue]

@[simp] theorem pairLabel_val (three : Fin 3 ↪ Role) (a b : Bool) :
    (pairLabel three a b).val = pairLabelValue three a b := rfl

@[simp] theorem pairLabel_atom_zero (three : Fin 3 ↪ Role) (a b : Bool) :
    (pairLabel three a b).val = Native.atom (three 0) ↔ a = true ∧ b = false := by
  have h10 := three.injective.ne (show (1 : Fin 3) ≠ 0 by decide)
  cases a <;> cases b <;> simp [pairLabelValue, h10]

@[simp] theorem pairLabel_atom_one (three : Fin 3 ↪ Role) (a b : Bool) :
    (pairLabel three a b).val = Native.atom (three 1) ↔ b = true ∧ a = false := by
  have h01 := three.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  cases a <;> cases b <;> simp [pairLabelValue, h01]

/-- The noncrossing bit pairs form the actual atomic two-role subalgebra.
This lemma proves its complete table, for every owner in the original signature. -/
theorem pairLabel_operation (three : Fin 3 ↪ Role) (owner : Role) (a b c d : Bool)
    (hab : ¬ (a = true ∧ b = true)) (hcd : ¬ (c = true ∧ d = true)) :
    pairLabel three (if owner = three 0 then a || c else a && c)
      (if owner = three 1 then b || d else b && d) =
        operation owner (pairLabel three a b) (pairLabel three c d) := by
  apply Subtype.ext
  have h01 := three.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hop (x y : Native.atomicRestriction (pairRoles three)) :
      (operation owner x y).val = Native.choice owner x.val y.val := rfl
  rw [hop]
  cases a <;> cases b <;> cases c <;> cases d
  all_goals simp_all only [Bool.false_eq_true, not_false_eq_true,
    and_false, and_true, not_true_eq_false, pairLabel_val]
  all_goals by_cases h0 : owner = three 0
  all_goals by_cases h1 : owner = three 1
  all_goals simp_all [pairLabelValue, Native.choice, Native.join, Ne.symm h01]
  all_goals aesop

end KFOL.Core
