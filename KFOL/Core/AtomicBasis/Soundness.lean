module

public import KFOL.Core.AtomicBasis.Presentation

/-! # Soundness of every displayed atomic basis equation -/

@[expose] public section

namespace KFOL.Core.AtomicBasis

universe u

variable {Role : Type u} [DecidableEq Role]

@[simp] theorem boolean_operation (i r : Role) (x y : Bool) :
    letI := booleanStructure i
    operation r x y = if r = i then x || y else x && y := rfl

theorem boolean_join (three : Fin 3 ↪ Role) (i : Role) (x y : Bool) :
    letI := booleanStructure i
    join three x y = (x && y) := by
  let _ := booleanStructure i
  have h01 := three.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have h02 := three.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have h12 := three.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  simp only [join, boolean_operation]
  split_ifs <;> cases x <;> cases y <;> simp_all

theorem boolean_laws (three : Fin 3 ↪ Role) (i : Role) :
    letI := booleanStructure i
    LiftingLaws (join three) (operation (Role := Role) (M := Bool)) := by
  let _ := booleanStructure i
  have h : LiftingLaws (fun x y : Bool => x && y)
      (fun r x y => if r = i then x || y else x && y) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x; cases x <;> rfl
    · intro x y; cases x <;> cases y <;> rfl
    · intro x y z; cases x <;> cases y <;> cases z <;> rfl
    · intro r x; split_ifs <;> cases x <;> rfl
    · intro r x y; split_ifs <;> cases x <;> cases y <;> rfl
    · intro r x y z; split_ifs <;> cases x <;> cases y <;> cases z <;> rfl
    · intro r x y z; split_ifs <;> cases x <;> cases y <;> cases z <;> rfl
    · intro r s hrs x y
      split_ifs <;> cases x <;> cases y <;> simp_all
    · intro r s hrs x y
      split_ifs <;> cases x <;> cases y <;> simp_all
  have hj : join three = fun x y : Bool => x && y :=
    funext (fun x => funext (boolean_join three i x))
  rw [hj]
  exact h

theorem boolean_reset (three : Fin 3 ↪ Role) (rs : List Role) (covers : ∀ r, r ∈ rs)
    (i : Role) (x y : Bool) :
    letI := booleanStructure i
    reset three rs x y = y := by
  let _ := booleanStructure i
  have aux (xs : List Role) (b y : Bool) (hb : (b && y) = b) :
      xs.foldl (fun acc r => if r = i then y || acc else y && acc) b =
        if i ∈ xs then y else b := by
    induction xs generalizing b with
    | nil => simp
    | cons r xs ih =>
      simp only [List.foldl_cons]
      by_cases hri : r = i
      · subst r
        cases y <;> cases b <;> simp_all
      · have hir : i ≠ r := Ne.symm hri
        cases y <;> cases b <;> simp_all
  unfold reset
  rw [boolean_join three i]
  simp only [boolean_operation]
  rw [aux rs (x && y) y (by cases x <;> cases y <;> rfl), ite_eq_left (covers i)]

/-- Every owner indicator verifies the basis; their joint injectivity reflects it. -/
theorem atomic_models (three : Fin 3 ↪ Role) (rs : List Role) (covers : ∀ r, r ∈ rs) :
    letI := structureOf Role
    Equational.Models (theory three rs) (Carrier Role) := by
  let _ := structureOf Role
  intro e he v
  apply indicators_separate
  intro i
  let _ := booleanStructure i
  have hm := (models_iff three rs).mpr
    ⟨boolean_laws three i, boolean_reset three rs covers i⟩
  have hh := hm e he (fun j => indicator i (v j))
  change (indicatorHom i) (e.lhs.realize v) = (indicatorHom i) (e.rhs.realize v)
  rw [← FirstOrder.Language.HomClass.realize_term (indicatorHom i),
    ← FirstOrder.Language.HomClass.realize_term (indicatorHom i)]
  exact hh

end KFOL.Core.AtomicBasis
