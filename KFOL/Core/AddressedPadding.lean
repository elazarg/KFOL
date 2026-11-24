module

public import KFOL.Core.AddressedRectangle

/-! # Two private labels for a rectangle cut

The left dummy is never excluded by a right vertex and the right dummy
never belongs to a left vertex. Neither extends the eligible cell. Their
private address tracks preserve the geometry of the original labels.
-/

@[expose] public section
namespace KFOL.Core.AddressedPadding

open Bichain AddressedRails AddressedRectangle

variable {Label Row Track Bit : Type*}

def extendRow (left : Row → Bool) (rows : Row → Label → Value) (z : Row) :
    Label ⊕ Bool → Value
  | .inl x => rows z x
  | .inr true => if left z then .c else .neutral
  | .inr false => if left z then .neutral else .b

/-- Both starting endpoint flags are true at the left dummy and false
at the right dummy. -/
def extendEndpoint (x : Label → Bool) : Label ⊕ Bool → Bool := Sum.elim x id

private theorem transport [DecidableEq Row] {rows : Row → Label → Value} (left : Row → Bool)
    {S : Finset Row} {x y : Label → Bool} (hc : CubeCut rows S (.separate x y))
    (x' y' : Label ⊕ Bool → Bool)
    (xp : ∀ j, x' (.inl j) = x j) (yp : ∀ j, y' (.inl j) = y j)
    (xf : x' (.inr false) = false) (yt : y' (.inr true) = true) :
    CubeCut (extendRow left rows) S (.separate x' y') := by
  generalize eq : CubeQuery.separate x y = q at hc
  induction hc generalizing x y x' y' with
  | @cover budget selected q sub cov _ _ hl hr =>
    cases eq
    apply CubeCut.cover sub
    · rintro (j | b) mem
      · obtain ⟨z, hz, mark⟩ := cov j ⟨(xp j).symm ▸ mem.1, (yp j).symm ▸ mem.2⟩
        exact ⟨z, hz, mark⟩
      · obtain ⟨a, d⟩ := mem
        cases b <;> simp_all
    · intro z hz
      apply hl z hz (x := cubeLower (rows z)) (y := y) _ _ (fun _ => rfl) yp _ yt rfl
      cases side : left z <;> simp [extendRow, cubeLower, side]
    · intro z hz
      apply hr z hz (x := x) (y := cubeUpper (rows z)) _ _ xp (fun _ => rfl) xf _ rfl
      cases side : left z <;> simp [extendRow, cubeUpper, side]

theorem cut_with_private_labels [DecidableEq Row] {rows : Row → Label → Value} (left : Row → Bool)
    {S : Finset Row} {x y : Label → Bool} (hc : CubeCut rows S (.separate x y)) :
    CubeCut (extendRow left rows) S (.separate (extendEndpoint x) (extendEndpoint y)) :=
  transport left hc _ _ (fun _ => rfl) (fun _ => rfl) rfl rfl

/-- Add one track for each private label. Only the track distinguishes
the two new labels, so their digit strings may both be constant zero. -/
def extendBook (B : Book Label Track Bit) : Book (Label ⊕ Bool) (Track ⊕ Bool) Bit where
  track := Sum.map B.track id
  digit f := f.elim B.digit (fun _ _ => false)
  unique f h same bits := by
    cases f with
    | inr v =>
      cases h with
      | inl => cases same
      | inr w => exact congrArg Sum.inr (Sum.inr.inj same)
    | inl f =>
      cases h with
      | inr => cases same
      | inl h =>
        exact congrArg Sum.inl (B.unique f h (Sum.inl.inj same) bits)

def extendSet (F : Set Label) (side : Bool) : Set (Label ⊕ Bool) :=
  {j | j.elim (· ∈ F) (· = side)}

theorem sparse_extend (B : Book Label Track Bit) {F : Set Label} (side : Bool) (h : B.Sparse F) :
    (extendBook B).Sparse (extendSet F side) := by
  rintro (f | f) hf (g | g) hg eq
  · exact congrArg Sum.inl (h f hf g hg (Sum.inl.inj eq))
  · cases eq
  · cases eq
  · exact congrArg Sum.inr (Sum.inr.inj eq)

theorem sparseOrFull_extend (B : Book Label Track Bit) {F : Set Label} (side : Bool)
    (h : B.SparseOrFull F) : (extendBook B).SparseOrFull (extendSet F side) := by
  rintro (t | t)
  · obtain localSparse | all := h t
    · left
      rintro (f | f) hf (g | g) hg ft gt
      · exact congrArg Sum.inl (localSparse f hf g hg (Sum.inl.inj ft) (Sum.inl.inj gt))
      · cases gt
      · cases ft
      · cases ft
    · right
      rintro (f | f) ft
      · exact all f (Sum.inl.inj ft)
      · cases ft
  · left
    rintro (f | f) hf (g | g) hg ft gt
    · cases ft
    · cases ft
    · cases gt
    · exact congrArg Sum.inr ((Sum.inr.inj ft).trans (Sum.inr.inj gt).symm)

def extendRows {B : Book Label Track Bit} (R : Rows B Row) : Rows (extendBook B) Row where
  left := R.left
  mark := fun z => .inl (R.mark z)
  posted := fun z => extendSet (R.posted z) (R.left z)
  sparseLeft z side := sparse_extend B _ (R.sparseLeft z side)
  sparseRight z side := sparseOrFull_extend B _ (R.sparseRight z side)
  apart z f hf same := by
    cases f with
    | inl f => exact R.apart z f hf (Sum.inl.inj same)
    | inr => cases same

theorem cube_extend {B : Book Label Track Bit} (R : Rows B Row) :
    (extendRows R).cube = extendRow R.left R.cube := by
  classical
  funext z f
  cases f with
  | inl f =>
    cases side : R.left z <;> by_cases m : f = R.mark z <;> by_cases p : f ∈ R.posted z <;>
      simp [Rows.cube, extendRows, extendSet, extendRow, m, p, side]
  | inr b => cases b <;> cases side : R.left z <;> simp [Rows.cube, extendRows, extendSet, extendRow, side]

theorem cut_extendRows [DecidableEq Row] {B : Book Label Track Bit} (R : Rows B Row)
    {S : Finset Row} {x y : Label → Bool} (hc : CubeCut R.cube S (.separate x y)) :
    CubeCut (extendRows R).cube S (.separate (extendEndpoint x) (extendEndpoint y)) := by
  rw [cube_extend]
  exact cut_with_private_labels R.left hc

end KFOL.Core.AddressedPadding
