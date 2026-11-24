module

public import KFOL.Complexity.TablePeelingSemantics
public import KFOL.Complexity.TablePeelingMasksMachine
public import KFOL.Complexity.ExplicitSourceHardness
public import KFOL.Complexity.ExplicitSourceSpace

/-! # PSPACE-completeness of recognition from either explicit table

Checking the full table reduces to exact interpolation. A split certificate
plays one bounded round for each row and possible role. The initial
nonemptiness test rejects every row that would require the empty menu.
-/

@[expose] public section
namespace KFOL.Complexity.TablePeelingSpace

open Cslib.Complexity TablePeeling TablePeelingClock TablePeelingMasks

/-- Exact interpolation of an arbitrary list of rows is in PSPACE. -/
theorem interpolation_mem_PSPACE {K : ℕ} (hk : 0 < K) : {x | Accepts hk x} ∈ PSPACE inputEncoding := by
  have starts : {x | initialOk K x = true} ∈ P inputEncoding :=
    ⟨initialOk K,initialOk_poly K,fun _ => Iff.rfl⟩
  have game := TablePeelingGame.mem_PSPACE (width_poly K) (rounds_poly K)
    (gate_poly K) (endTest_poly K) (clock K) (clock_bound K)
  convert inter_mem_PSPACE (P_subset_PSPACE starts) game using 1
  ext x
  exact TablePeelingSemantics.accepts_iff_wins hk x

/-- Membership for a fixed, nonempty finite set of owners, with binary-coded
menus and a unary-coded arity. -/
theorem winner_mem_PSPACE {K : ℕ} (hk : 0 < K) :
    {p | AddressedPoint.RawAccepts K p} ∈ PSPACE AddressedPoint.tableEncoding :=
  (raw_reducible hk).mem_PSPACE (interpolation_mem_PSPACE hk)

/-- The raw winner-set table language is PSPACE-complete. -/
theorem winner_complete {K : ℕ} (three : Fin 3 ↪ Fin K) :
    PSPACEComplete AddressedPoint.tableEncoding {p | AddressedPoint.RawAccepts K p} :=
  ⟨winner_mem_PSPACE (Nat.zero_lt_of_lt (three 0).isLt), ExplicitTableHardness.pspaceHard three⟩

/-- The Boolean source-probe table language is PSPACE-complete. -/
theorem source_complete {K : ℕ} (three : Fin 3 ↪ Fin K) :
    PSPACEComplete AddressedSourceOutput.sourceEncoding (AddressedSourceOutput.language three) :=
  ⟨ExplicitSourceSpace.mem_PSPACE_of_winner three (winner_complete three).1,
    ExplicitSourceHardness.pspaceHard three⟩

/-- The two complete table presentations are PSPACE-complete for every
fixed owner set of cardinality at least three. -/
theorem complete {K : ℕ} (three : Fin 3 ↪ Fin K) :
    PSPACEComplete AddressedPoint.tableEncoding {p | AddressedPoint.RawAccepts K p} ∧
      PSPACEComplete AddressedSourceOutput.sourceEncoding (AddressedSourceOutput.language three) :=
  ⟨winner_complete three, source_complete three⟩

private theorem criterion_iff {B : Type} {encB : B ↪ List Bool} {L : Set B}
    (completeL : PSPACEComplete encB L) :
    L ∈ P encB ↔ ∀ {A : Type} (e : A ↪ List Bool), P e = PSPACE e :=
  ⟨fun fast _ e => P_subset_PSPACE.antisymm (fun language inSpace =>
      (completeL.2 e language inSpace).mem_P fast),
    fun eq => (eq encB).symm ▸ completeL.1⟩

/-- A polynomial-time criterion exists on either explicit presentation
exactly when polynomial time equals polynomial space. -/
theorem polynomial_criterion_iff {K : ℕ} (three : Fin 3 ↪ Fin K) :
    ({p | AddressedPoint.RawAccepts K p} ∈ P AddressedPoint.tableEncoding ↔
        ∀ {A : Type} (e : A ↪ List Bool), P e = PSPACE e) ∧
    (AddressedSourceOutput.language three ∈ P AddressedSourceOutput.sourceEncoding ↔
        ∀ {A : Type} (e : A ↪ List Bool), P e = PSPACE e) :=
  ⟨criterion_iff (winner_complete three), criterion_iff (source_complete three)⟩

end KFOL.Complexity.TablePeelingSpace
