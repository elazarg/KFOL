module

public import Mathlib.Order.Lattice
public import Mathlib.Data.List.Fold

/-! # Finite meets from complementary commuting semilattice endomorphisms -/

@[expose] public section

namespace KFOL.Core.AtomicBasis

universe u v

variable {I : Type u} {M : Type v} [SemilatticeSup M]

/-- Complementary deflationary maps have a finite meet given by composition.
No meets are assumed in the ambient semilattice. -/
theorem complementary_fold_glb (F : I → M → M)
    (hmono : ∀ i, Monotone (F i))
    (hdefl : ∀ i x, F i x ≤ x)
    (hjoin : ∀ i x y, F i (x ⊔ y) = F i x ⊔ F i y)
    (hcomm : ∀ i j x, F i (F j x) = F j (F i x))
    (hcover : ∀ i j, i ≠ j → ∀ x, F i x ⊔ F j x = x)
    (rs : List I) (hn : rs.Nodup) (u w : M) :
    w ≤ rs.foldr F u ↔ w ≤ u ∧ ∀ i ∈ rs, w ≤ F i u := by
  have defl (xs : List I) (x : M) : xs.foldr F x ≤ x := by
    induction xs with
    | nil => exact le_rfl
    | cons i xs ih => exact (hdefl i _).trans ih
  have mono (xs : List I) : Monotone (xs.foldr F) := by
    induction xs with
    | nil => exact monotone_id
    | cons i xs ih => exact (hmono i).comp ih
  have comm (xs : List I) (i : I) (x : M) :
      xs.foldr F (F i x) = F i (xs.foldr F x) := by
    induction xs with
    | nil => rfl
    | cons j xs ih => simpa only [List.foldr_cons, ih] using hcomm j i (xs.foldr F x)
  have cover (xs : List I) (i : I) (hi : i ∉ xs) (x : M) :
      xs.foldr F x ⊔ F i x = x := by
    induction xs with
    | nil => exact sup_eq_left.mpr (hdefl i x)
    | cons j xs ih =>
      have hji : j ≠ i := fun he => hi (by simp [he])
      have hit : i ∉ xs := fun he => hi (List.mem_cons_of_mem _ he)
      have he := congrArg (F j) (ih hit)
      rw [hjoin] at he
      apply le_antisymm
      · exact sup_le ((hdefl j _).trans (defl xs x)) (hdefl i x)
      · calc
          x = F j x ⊔ F i x := (hcover j i hji x).symm
          _ ≤ F j (xs.foldr F x) ⊔ F i x := by
            apply sup_le _ le_sup_right
            rw [← he]
            exact sup_le_sup_left (hdefl j (F i x)) _
  induction rs with
  | nil => simp
  | cons i rs ih =>
    obtain ⟨hi, hns⟩ := List.nodup_cons.mp hn
    rw [List.foldr_cons]
    constructor
    · intro hw
      have hp := hw.trans (hdefl i _)
      obtain ⟨hwu, hrs⟩ := (ih hns).mp hp
      refine ⟨hwu, ?_⟩
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hw.trans (hmono j (defl rs u))
      · exact hrs j hj
    · rintro ⟨hwu, hrs⟩
      have hwp : w ≤ rs.foldr F u := (ih hns).mpr
        ⟨hwu, fun j hj => hrs j (List.mem_cons_of_mem _ hj)⟩
      have hwi := hrs i List.mem_cons_self
      rw [← cover rs i hi w]
      apply sup_le
      · rw [← comm]
        exact mono rs hwi
      · exact hmono i hwp

end KFOL.Core.AtomicBasis
