module

public import KFOL.Complexity.AddressedPointLanguage
public import KFOL.Complexity.AddressedPointCorrectness

/-! # Relating the emitted winner table to its semantic operation -/

@[expose] public section
namespace KFOL.Complexity.AddressedPoint

open AddressTableOutput FullSparseEvaluation Core.AddressedRails Core.AddressedRectangle
open Core.AddressedPadding Core.AddressedRecognition Core.ProfileBudgets Core.AddressSize
open AddressedEnvelope
attribute [local instance] Equational.coreStructure

def filled (K a b c q n : ℕ) (layout : Layout) : TableInput :=
  (arity q n,(List.range (count K q n)).map fun i => point K a b c layout (tuple K (arity q n) i))

theorem filled_getD {K a b c q n : ℕ} (layout : Layout) (i : ℕ) (hi : i < count K q n) :
    (filled K a b c q n layout).2.getD i [] = point K a b c layout (tuple K (arity q n) i) := by
  simp [filled,List.getD_eq_getElem?_getD,hi]

theorem rawAccepts_table_iff {K q n : ℕ} {L Track Row : Type*} [Fintype L] [Fintype Track]
    {B : Book L Track (Fin (width n))} (three : Fin 3 ↪ Fin K) (R : Rows B Row) (S : Finset Row)
    (x y : L → Bool) (ids : L ⊕ Bool ↪ ℕ) (tracks : (Track ⊕ Bool) ≃ Fin q)
    (layout : Layout)
    (codes : CodePresentation ids (extendBook B)
      (fun u => (coordEquiv tracks (width n) (some u)).val) layout.1)
    (left : RowPresentation ids (extendRows R) S true (sideEndpoint true x y) layout.2.1)
    (right : RowPresentation ids (extendRows R) S false (sideEndpoint false x y) layout.2.2) :
    RawAccepts K (filled K (three 0).val (three 1).val (three 2).val q n layout) ↔
      ∃ t : CoreTerm (Fin K) (Option (Rail (Track ⊕ Bool) (Fin (width n)))),
        ∀ v, t.realize v = Core.AddressedRecognition.table three R S x y v := by
  let rank := coordEquiv tracks (width n)
  apply rawAccepts_iff (Nat.zero_lt_of_lt (three 0).isLt) rank (by simp [count,arity])
    (Core.AddressedRecognition.table three R S x y)
  intro i hi v all
  change Represents ((filled K (three 0).val (three 1).val (three 2).val q n layout).2.getD i []) _
  rw [filled_getD _ i hi]
  have input (j) : Represents ((tuple K (arity q n) i).getD (rank j).val []) (v j) := by
    rw [tuple_getD K (arity q n) i (rank j).val (rank j).isLt]
    exact all j
  exact point_represents three R S x y ids _ layout codes left right _ v (input none) (fun u => input (some u))

end KFOL.Complexity.AddressedPoint
