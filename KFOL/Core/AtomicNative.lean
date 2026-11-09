module

public import KFOL.Core.Quotients

/-! # The atomic native quotient, with its actual collapse homomorphism -/

@[expose] public section

namespace KFOL.Core.Native

universe u

open FirstOrder

variable {Role : Type u} [DecidableEq Role]

attribute [local instance] structureOf

omit [DecidableEq Role] in
@[simp] theorem collapseUpper_eq_atom (x : Native Role) (r : Role) :
    collapseUpper x = .atom r ↔ x = .atom r := by cases x <;> simp [collapseUpper]

omit [DecidableEq Role] in
@[simp] theorem collapseUpper_ne_upper (x : Native Role) : collapseUpper x ≠ .upper := by
  cases x <;> simp [collapseUpper]

omit [DecidableEq Role] in
theorem collapseUpper_eq_self {x : Native Role} (hx : x ≠ .upper) : collapseUpper x = x := by
  cases x <;> simp_all [collapseUpper]

theorem collapseUpper_choice (r : Role) (x y : Native Role) :
    collapseUpper (choice r x y) = choice r (collapseUpper x) (collapseUpper y) := by
  apply ext_atoms_upper
  · intro i
    rw [collapseUpper_eq_atom, choice_eq_atom, choice_eq_atom]
    split <;> simp only [collapseUpper_eq_atom]
  · simp only [collapseUpper_ne_upper, false_iff, choice_eq_upper]
    simp

/-- The atomic R-algebra retains R's atoms and a single ambiguity marker. -/
def atomicRestriction (R : Set Role) :
    (Equational.language (Equational.CoreSymbol Role)).Substructure (Native Role) :=
  restriction R ⊓ omission none

theorem atomic_ne_upper {R : Set Role} (x : atomicRestriction R) : x.val ≠ .upper := x.property.2

@[simp] theorem operation_restriction (R : Set Role) (r : Role) (x y : restriction R) :
    (Core.operation r x y).val = choice r x.val y.val := rfl

@[simp] theorem operation_atomic (R : Set Role) (r : Role) (x y : atomicRestriction R) :
    (Core.operation r x y).val = choice r x.val y.val := rfl

/-- The actual quotient identifying the two markers, in the full role
signature even when only some role atoms occur in the carrier. -/
def collapseHom (R : Set Role) :
    restriction R →[Equational.language (Equational.CoreSymbol Role)] atomicRestriction R where
  toFun x := ⟨collapseUpper x.val,
    ⟨fun r hr => x.property r ((collapseUpper_eq_atom x.val r).mp hr), collapseUpper_ne_upper x.val⟩⟩
  map_fun' := by
    intro n f args
    cases f with
    | choice r =>
      apply Subtype.ext
      exact collapseUpper_choice r (args 0).val (args 1).val
  map_rel' := by intro n r; exact nomatch r

/-- The atomic restriction itself is a subalgebra of the full atomic
winner-set quotient; properness is not needed for this membership statement. -/
theorem atomicRestriction_inVariety (three : Fin 3 ↪ Role) (R : Set Role) :
    letI := Equational.coreStructure Role
    Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) (atomicRestriction R) := by
  let _ := Equational.coreStructure Role
  have : Nonempty (atomicRestriction R) := by
    refine ⟨⟨.lower, ?_⟩⟩
    constructor
    · intro r he
      cases he
    · change Native.lower ≠ Native.upper
      simp
  let f : atomicRestriction R →[Equational.language (Equational.CoreSymbol Role)] omission none :=
    { toFun x := ⟨x.val, x.property.2⟩
      map_fun' := by intro n f args; rfl
      map_rel' := by intro n r; exact nomatch r }
  exact Equational.InVariety.of_injective (omission_inVariety three none) f (by
    intro x y he
    have hv : x.val = y.val := congrArg (fun z : omission (Role := Role) none => z.val) he
    exact Subtype.ext hv)

end KFOL.Core.Native
