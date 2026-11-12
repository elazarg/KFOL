module

public import KFOL.Core.AtomicBasis.Lifting
public import KFOL.Core.AtomicBasis.Complementary
public import Mathlib.Order.LatticeIntervals

/-! # Reset is the meet of the owner closures below a common bound -/

@[expose] public section

namespace KFOL.Core.AtomicBasis.LiftingLaws

universe u v

variable {Role : Type u} {M : Type v} {add : M → M → M} {op : Role → M → M → M}
    (h : LiftingLaws add op) [Nontrivial Role]

include h

theorem fold_glb (rs : List Role) (hn : rs.Nodup) {x u w : M} :
    letI := h.semilattice
    x ≤ u → x ≤ w →
    (w ≤ rs.foldr (fun i v => op i x v) u ↔ w ≤ u ∧ ∀ i ∈ rs, w ≤ op i x u) := by
  let _ := h.semilattice
  intro hxu hxw
  let F (i : Role) (v : Set.Ici x) : Set.Ici x :=
    ⟨op i x v, h.le_closure i v.property⟩
  have hmono (i : Role) : Monotone (F i) := fun _ _ hab => h.monotone_right i x hab
  have hdefl (i : Role) (v : Set.Ici x) : F i v ≤ v :=
    h.op_bound_upper i v.property le_rfl
  have hjoin (i : Role) (v w : Set.Ici x) : F i (v ⊔ w) = F i v ⊔ F i w := by
    apply Subtype.val_injective
    exact h.op_add i x v w
  have hcomm (i j : Role) (v : Set.Ici x) : F i (F j v) = F j (F i v) := by
    apply Subtype.val_injective
    by_cases hij : i = j
    · subst j; rfl
    · exact h.birkhoff i j hij x v
  have hcover (i j : Role) (hij : i ≠ j) (v : Set.Ici x) : F i v ⊔ F j v = v := by
    apply Subtype.val_injective
    change add (op i x v) (op j x v) = v
    rw [h.cover i j hij]
    exact sup_eq_right.mpr v.property
  have he := complementary_fold_glb F hmono hdefl hjoin hcomm hcover rs hn
    (⟨u, hxu⟩ : Set.Ici x) (⟨w, hxw⟩ : Set.Ici x)
  have coe (xs : List Role) (v : Set.Ici x) :
      (xs.foldr F v).val = xs.foldr (fun i v => op i x v) v.val := by
    induction xs with
    | nil => rfl
    | cons i xs ih => change op i x (xs.foldr F v).val = _; rw [ih]; rfl
  change w ≤ (rs.foldr F ⟨u, hxu⟩).val ↔ _ at he
  rw [coe] at he
  exact he

/-- The closures separate a principal ideal whenever reset is projection. -/
theorem closures_separate (rs : List Role) (hn : rs.Nodup)
    (hreset : ∀ u x, rs.foldl (fun v i => op i x v) (add u x) = x) {u x y : M} :
    letI := h.semilattice
    x ≤ u → y ≤ u → (∀ i, op i x u = op i y u) → x = y := by
  let _ := h.semilattice
  intro hx hy he
  have separate (a b : M) (ha : a ≤ u) (hb : b ≤ u)
      (he : ∀ i, op i a u = op i b u) : a ≤ b := by
    have hw : a ⊔ b ≤ u := sup_le ha hb
    have hbnd (i : Role) (_hi : i ∈ rs.reverse) : a ⊔ b ≤ op i b u := by
      exact sup_le ((he i) ▸ h.le_closure i ha) (h.le_closure i hb)
    have hp := (h.fold_glb rs.reverse (by simpa using hn) hb le_sup_right).mpr ⟨hw, hbnd⟩
    have hr := hreset u b
    rw [show add u b = u from sup_eq_left.mpr hb, List.foldl_eq_foldr_reverse] at hr
    rw [hr] at hp
    exact le_sup_left.trans hp
  exact le_antisymm (separate x y hx hy he) (separate y x hy hx (fun i => (he i).symm))

end KFOL.Core.AtomicBasis.LiftingLaws
