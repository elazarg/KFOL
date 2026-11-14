module

public import KFOL.Definitions.DependentSchedule
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Data.Set.Lattice.Disjoint

/-! # Full policies glue over legal views by a fiber product

Information sets may cross a private dynamic boundary. Separate component
policies must then agree on those shared decision views. A plain product
is valid at an information-separating boundary.
-/

@[expose] public section

namespace KFOL.DependentSchedule.Views

universe u v

variable {View : Type u} {Answer : View → Type v} {P Q : Set View}

def restrict (h : P ⊆ Q) (policy : Policy Answer Q) : Policy Answer P :=
  fun view => policy ⟨view.val, h view.property⟩

def split (policy : Policy Answer (P ∪ Q)) : GluingData Answer P Q :=
  ⟨(restrict Set.subset_union_left policy, restrict Set.subset_union_right policy),
    fun _ _ _ => rfl⟩

noncomputable def glue (data : GluingData Answer P Q) : Policy Answer (P ∪ Q) := by
  classical
  intro view
  exact if hp : view.val ∈ P then data.val.1 ⟨view.val, hp⟩
    else data.val.2 ⟨view.val, view.property.resolve_left hp⟩

@[simp] theorem glue_left (data : GluingData Answer P Q) (view : P) :
    glue data ⟨view.val, Or.inl view.property⟩ = data.val.1 view := by
  classical
  simp [glue, view.property]

@[simp] theorem glue_right (data : GluingData Answer P Q) (view : Q) :
    glue data ⟨view.val, Or.inr view.property⟩ = data.val.2 view := by
  classical
  unfold glue
  split
  · rename_i hp
    exact data.property view.val hp view.property
  · rfl

theorem split_glue (data : GluingData Answer P Q) : split (glue data) = data := by
  apply Subtype.ext
  apply Prod.ext
  · funext view
    exact glue_left data view
  · funext view
    exact glue_right data view

theorem glue_split (policy : Policy Answer (P ∪ Q)) : glue (split policy) = policy := by
  classical
  funext view
  unfold glue
  split <;> rfl

/-- Restriction and gluing are inverse for the entire legal policy table,
including decisions on histories inconsistent with its own earlier actions. -/
noncomputable def unionEquivGluing (Answer : View → Type v) (P Q : Set View) :
    Policy Answer (P ∪ Q) ≃ GluingData Answer P Q where
  toFun := split
  invFun := glue
  left_inv := glue_split
  right_inv := split_glue

theorem agree_of_disjoint (h : Disjoint P Q) (first : Policy Answer P)
    (second : Policy Answer Q) : Agree first second := by
  intro view hp hq
  exact False.elim (Set.disjoint_left.mp h hp hq)

/-- The usual independent product is recovered when no decision information
set occurs on both sides of the boundary. -/
noncomputable def unionEquivProd (Answer : View → Type v) (P Q : Set View)
    (h : Disjoint P Q) : Policy Answer (P ∪ Q) ≃ Policy Answer P × Policy Answer Q where
  toFun := fun policy => (split policy).val
  invFun := fun pair => glue ⟨pair, agree_of_disjoint h pair.1 pair.2⟩
  left_inv := glue_split
  right_inv := fun pair => congrArg Subtype.val (split_glue ⟨pair, agree_of_disjoint h pair.1 pair.2⟩)

/-- Whole-player deviations split into component deviations with the shared
information-set choices still coupled by `GluingData`. -/
theorem deviation_split_iff {Role : Type*} (owner : View → Role) (player : Role)
    (source target : Policy Answer (P ∪ Q)) :
    Deviation owner player source target ↔
      Deviation owner player (split source).val.1 (split target).val.1 ∧
      Deviation owner player (split source).val.2 (split target).val.2 := by
  constructor
  · intro h
    constructor
    · intro view hv
      exact h ⟨view.val, Or.inl view.property⟩ hv
    · intro view hv
      exact h ⟨view.val, Or.inr view.property⟩ hv
  · rintro ⟨hP, hQ⟩ view hv
    rcases view.property with hp | hq
    · exact hP ⟨view.val, hp⟩ hv
    · exact hQ ⟨view.val, hq⟩ hv

/-- Even one hidden Boolean request shared across the cut prevents arbitrary
independent choice of the two component policies. -/
theorem shared_boolean_request_not_independent :
    ¬Agree (Answer := fun _ : PUnit => Bool) (fun _ : (Set.univ : Set PUnit) => false)
      (fun _ : (Set.univ : Set PUnit) => true) := by
  intro h
  exact Bool.false_ne_true (h PUnit.unit (Set.mem_univ _) (Set.mem_univ _))

end KFOL.DependentSchedule.Views
