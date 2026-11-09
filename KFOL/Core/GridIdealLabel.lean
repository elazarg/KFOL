module

public import KFOL.Core.GridProfiles
public import KFOL.Core.PairLabel

/-! # The actual typed homomorphism on the complete grid's lower ideal -/

@[expose] public section

namespace KFOL.Core.Grid

universe u

open FirstOrder

variable {Role : Type u} [DecidableEq Role]

attribute [local instance] Native.structureOf Equational.coreStructure structureOf

/-- The lower ideal has no simultaneous positive row and column bits. -/
theorem ideal_bits_disjoint {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role)
    (i : Fin r) (j : Fin s) (x : span (r := r) (s := s) three)
    (hx : Core.join three x (lower three) = lower three) :
    ¬ (A hr three i x = true ∧ B hs three j x = true) := by
  rcases (lower_ideal_exact hr hs three x).mp hx with rfl | rfl | rfl
  · simp [B_T hr hs]
  · simp [A_S hr hs]
  · simp

/-- The paper's eta is a concrete homomorphism, computed from the two
Boolean block maps. Its domain is the independently defined lower ideal. -/
def idealLabel {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role)
    (i : Fin r) (j : Fin s) :
    Core.ideal (span_inVariety (r := r) (s := s) three) three (lower three) →[
      Equational.language (Equational.CoreSymbol Role)] Native.atomicRestriction (pairRoles three) where
  toFun x := pairLabel three (A hr three i x.val) (B hs three j x.val)
  map_fun' := by
    intro n f args
    cases f with
    | choice owner =>
      rw [funMap_choice, funMap_choice]
      change pairLabel three (A hr three i (Core.operation owner (args 0).val (args 1).val))
        (B hs three j (Core.operation owner (args 0).val (args 1).val)) = _
      rw [A_operation, B_operation]
      exact pairLabel_operation three owner _ _ _ _
        (ideal_bits_disjoint hr hs three i j (args 0).val (args 0).property)
        (ideal_bits_disjoint hr hs three i j (args 1).val (args 1).property)

/-- Eta's typing is exactly nonabsorption at e, for every owner in the
original signature, including owners outside the two labeling roles. -/
theorem idealLabel_typed {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role)
    (i : Fin r) (j : Fin s)
    (x : Core.ideal (span_inVariety (r := r) (s := s) three) three (lower three)) (owner : Role) :
    (idealLabel hr hs three i j x).val = Native.atom owner ↔
      Core.operation owner (lower three) x.val ≠ lower three := by
  change pairLabelValue three (A hr three i x.val) (B hs three j x.val) = Native.atom owner ↔ _
  rcases (lower_ideal_exact hr hs three x.val).mp x.property with hx | hx | hx
  · rw [hx, lower_operation_T hr hs, A_T hr hs, B_T hr hs]
    by_cases ho : owner = three 0
    · subst owner; simp [pairLabelValue, T_ne_lower hr hs]
    · simp [pairLabelValue, ho, Ne.symm ho]
  · rw [hx, lower_operation_S hr hs, A_S hr hs, B_S hr hs]
    by_cases ho : owner = three 1
    · subst owner; simp [pairLabelValue, S_ne_lower hr hs]
    · simp [pairLabelValue, ho, Ne.symm ho]
  · rw [hx, A_lower, B_lower, operation_idem (span_inVariety three)]
    simp [pairLabelValue]

/-- Inclusion of any subalgebra containing e induces the actual homomorphism
of lower ideals; it does not assume the subalgebra contains T or S. -/
def idealInclusion {r s : ℕ} (three : Fin 3 ↪ Role)
    (C : (Equational.language (Equational.CoreSymbol Role)).Substructure (span (r := r) (s := s) three))
    [Nonempty C] (he : lower three ∈ C) :
    Core.ideal ((span_inVariety three).substructure C) three ⟨lower three,he⟩ →[
      Equational.language (Equational.CoreSymbol Role)]
      Core.ideal (span_inVariety (r := r) (s := s) three) three (lower three) where
  toFun x := ⟨x.val.val, congrArg (fun c : C => c.val) x.property⟩
  map_fun' := by intro n f args; rfl

end KFOL.Core.Grid
