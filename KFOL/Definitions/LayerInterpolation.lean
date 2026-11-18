module

public import KFOL.Definitions.CoreInterpolation

/-! # Row constraints at a prescribed number of completion layers -/

@[expose] public section

namespace KFOL.Core.Interpolation

universe u v w
variable {Role : Type u} {Row : Type v} {Var : Type w}
variable [DecidableEq Row] [DecidableEq Role]

/-- At a completion gate choose the bounded rows which receive singleton
outputs. On the remaining bounded rows every child must fit. The profile
condition asks which atomic and positive challenges these children can meet. -/
def LayerFits (values : Row → Var → WinnerSet Role) (U : Row → Set Role) :
    ℕ → Finset Row → Finset (Row × Role) → Option (Row × Role) → Prop
  | 0, N, D, p => ∃ j, Fits N U D p (fun i => values i j)
  | d + 1, N, D, p =>
    ∃ B ⊆ N, ∃ r : Row → Role, (∀ i ∈ B, r i ∈ U i) ∧
      ProfileCondition (fun E o => LayerFits values U d (N \ B) E o)
        (D ∪ B.image (fun i => (i, r i))) p

/-- For exact outputs at depth at most \(d\), ask for bounded nonemptiness
and for each prescribed winner separately. -/
def RecognizesAtDepth [Fintype Row] (values : Row → Var → WinnerSet Role)
    (U : Row → Set Role) (d : ℕ) : Prop :=
  LayerFits values U d Finset.univ ∅ none ∧
    ∀ i k, k ∈ U i → LayerFits values U d Finset.univ ∅ (some (i, k))

/-- Apply the depth test to the complete table of a proposed operation. -/
noncomputable def RecognizesOperationAtDepth [Fintype Role] [Fintype Var]
    (f : (Var → WinnerSet Role) → WinnerSet Role) (d : ℕ) : Prop := by
  classical
  let _ : Fintype (WinnerSet Role) := Fintype.ofFinite (WinnerSet Role)
  exact RecognizesAtDepth (fun v j => v j) (fun v => (f v).val) d

end KFOL.Core.Interpolation
