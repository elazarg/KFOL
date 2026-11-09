module

public import KFOL.Core.GridPigeonhole
public import KFOL.Core.GridCountermodel
public import KFOL.Core.UpperMap
public import KFOL.Core.HomRange
public import Mathlib.Data.Finset.Option

/-! # Arbitrary finitely generated subalgebras of the grid upper clone -/

@[expose] public section

namespace KFOL.Core.Grid

universe u

open FirstOrder

variable {Role : Type u} [DecidableEq Role]

attribute [local instance] Native.structureOf Equational.coreStructure structureOf

/-- A uniform local-membership theorem for arbitrary generators of the
upper clone. Using r,s>2^d permits one cover for all cases, including sets
that omit the new point. No original-source-generator assumption is made. -/
theorem generated_clone_inVariety {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role)
    (d : ℕ) (hdr : 2 ^ d < r) (hds : 2 ^ d < s)
    (X : Finset (Option (span (r := r) (s := s) three))) (hX : X.card ≤ d) :
    letI := upperStructure (Role := Role) (lower (r := r) (s := s) three)
    Nonempty (Language.Substructure.closure (Equational.language (Equational.CoreSymbol Role)) (X : Set (Option (span (r := r) (s := s) three)))) →
      Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role)
        (Language.Substructure.closure (Equational.language (Equational.CoreSymbol Role)) (X : Set (Option (span (r := r) (s := s) three)))) := by
  classical
  let _ := upperStructure (Role := Role) (lower (r := r) (s := s) three)
  intro hne
  let _ := hne
  let Y := X.eraseNone
  let C := generated three Y
  let e : C := ⟨lower three,lower_mem_generated three Y⟩
  let _ := upperStructure (Role := Role) e
  have hY : Y.card ≤ d := (Finset.card_eraseNone_le X).trans hX
  have hpower : 2 ^ Y.card ≤ 2 ^ d := Nat.pow_le_pow_right (by decide) hY
  have hC := upper_clone_generated_inVariety hr hs three Y (hpower.trans_lt hdr) (hpower.trans_lt hds)
  let f : Option C →[Equational.language (Equational.CoreSymbol Role)] Option (span (r := r) (s := s) three) :=
    upperMap C.subtype.toHom C.subtype.injective e
  apply hC.generated_of_range f (X : Set (Option (span (r := r) (s := s) three))) ?_
  intro x hx
  cases x with
  | none => exact ⟨none,rfl⟩
  | some x =>
    have hy : x ∈ Y := Finset.mem_eraseNone.mpr hx
    have hc : x ∈ C := Language.Substructure.subset_closure (Or.inr hy)
    exact ⟨some ⟨x,hc⟩,rfl⟩

/-- For every variable bound there is an actual finite counteralgebra,
outside both ambient varieties, with every nonempty subalgebra generated
by at most that many arbitrary elements in the winner-core variety. -/
theorem finite_local_countermodel [Finite Role] (three : Fin 3 ↪ Role) (d : ℕ) :
    ∃ (B : Type u) (_str : (Equational.language (Equational.CoreSymbol Role)).Structure B),
      Nonempty B ∧ Finite B ∧
      ¬ Equational.InVariety (Equational.CoreSymbol Role) (Native Role) B ∧
      ¬ Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) B ∧
      (∀ X : Finset B, X.card ≤ d →
        Nonempty (Language.Substructure.closure (Equational.language (Equational.CoreSymbol Role)) (X : Set B)) →
        Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role)
          (Language.Substructure.closure (Equational.language (Equational.CoreSymbol Role)) (X : Set B))) := by
  let r : ℕ := 2 ^ d + 2
  have hr : 2 ≤ r := Nat.le_add_left 2 (2 ^ d)
  have hdr : 2 ^ d < r := by omega
  let B := Option (span (r := r) (s := r) three)
  let str := upperStructure (Role := Role) (lower (r := r) (s := r) three)
  let _ := str
  refine ⟨B,str,inferInstance,inferInstance,clone_not_in_native_variety hr hr three,
    clone_not_in_core_variety hr hr three,?_⟩
  intro X hX hne
  exact generated_clone_inVariety hr hr three d hdr hdr X hX hne

end KFOL.Core.Grid
