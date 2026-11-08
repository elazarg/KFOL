module

public import KFOL.Reset.Basis.Laws

/-! # Path products, deletion of repetitions and suffix absorption -/

@[expose] public section

namespace KFOL.Reset

universe u

/-- A left-associated path with a fixed final value. These paths are proof
constructions; duplicate variables are allowed and removed by proved laws. -/
def path {M : Type u} (op : M → M → M) (r : M) : List M → M
  | [] => r
  | x :: xs => op (xs.foldl op x) r

namespace Laws

variable {M : Type u} {op : M → M → M} (h : Laws op)
local infixl:70 " ⋄ " => op
local infix:50 " ≼ " => Below (op := op)
include h

theorem foldl_mono {a b : M} (hab : a ≼ b) (xs : List M) :
    xs.foldl op a ≼ xs.foldl op b := by
  induction xs generalizing a b with
  | nil => exact hab
  | cons x xs ih => exact ih (h.below_op_left hab x)

/-- Every earlier occurrence can be deleted when the same value occurs later. -/
theorem foldl_repeat (a b : M) (xs : List M) :
    (xs.foldl op (a ⋄ b)) ⋄ b = (xs.foldl op a) ⋄ b := by
  induction xs generalizing a with
  | nil => exact h.repeat_right a b
  | cons x xs ih =>
    change (xs.foldl op ((a ⋄ b) ⋄ x)) ⋄ b = (xs.foldl op (a ⋄ x)) ⋄ b
    calc
      _ = (xs.foldl op (((a ⋄ b) ⋄ x) ⋄ b)) ⋄ b := (ih _).symm
      _ = (xs.foldl op ((a ⋄ x) ⋄ b)) ⋄ b := by rw [h.exchange]
      _ = (xs.foldl op (a ⋄ x)) ⋄ b := ih _

/-- Repetitions may be removed across an arbitrarily long suffix. -/
theorem foldl_delete (a b : M) (xs : List M) (hb : b ∈ xs) :
    xs.foldl op (a ⋄ b) = xs.foldl op a := by
  obtain ⟨ys, zs, rfl⟩ := List.mem_iff_append.mp hb
  simp only [List.foldl_append, List.foldl_cons]
  rw [h.foldl_repeat]

/-- Delete any block whose values all occur in the subsequent block. -/
theorem foldl_delete_block (a : M) (xs ys : List M) (hxy : ∀ x ∈ xs, x ∈ ys) :
    (xs ++ ys).foldl op a = ys.foldl op a := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    change (xs ++ ys).foldl op (a ⋄ x) = ys.foldl op a
    rw [ih _ (fun z hz => hxy z (List.mem_cons_of_mem _ hz))]
    exact h.foldl_delete a x ys (hxy x (List.mem_cons_self))

/-- A repeated initial value can also be removed when a final copy remains. -/
theorem foldl_delete_initial (a b : M) (xs : List M) :
    (xs.foldl op (a ⋄ b)) ⋄ a = (xs.foldl op b) ⋄ a := by
  calc
    _ = (xs.foldl op ((a ⋄ b) ⋄ a)) ⋄ a := (h.foldl_repeat _ _ _).symm
    _ = (xs.foldl op (b ⋄ a)) ⋄ a := by rw [h.absorb]
    _ = (xs.foldl op b) ⋄ a := h.foldl_repeat _ _ _

theorem path_fixed (r : M) (xs : List M) : path op r xs ⋄ r = path op r xs := by
  cases xs with
  | nil => exact h.idem r
  | cons x xs => exact h.repeat_right _ _

theorem path_initial_root (r : M) (xs : List M) : path op r (r :: xs) = path op r xs := by
  cases xs with
  | nil => exact h.idem r
  | cons x xs => exact h.foldl_delete_initial _ _ _

/-- Flattening a right path gives an upper bound in the natural order. -/
theorem op_foldl_below (a b : M) (xs : List M) :
    a ⋄ xs.foldl op b ≼ xs.foldl op (a ⋄ b) := by
  induction xs generalizing b with
  | nil => exact h.below_refl _
  | cons x xs ih =>
    exact h.below_trans (ih (b ⋄ x)) (h.foldl_mono (h.reassoc_below a b x) xs)

/-- A product of paths lies below their concatenation. -/
theorem path_concat_below (r : M) (xs ys : List M) :
    path op r xs ⋄ path op r ys ≼ path op r (xs ++ ys) := by
  cases ys with
  | nil =>
    rw [List.append_nil]
    change path op r xs ⋄ r ≼ path op r xs
    rw [h.path_fixed]
    exact h.below_refl _
  | cons y ys =>
    cases xs with
    | nil =>
      change r ⋄ (ys.foldl op y ⋄ r) ≼ ys.foldl op y ⋄ r
      rw [h.e11]
      exact h.below_refl _
    | cons x xs =>
      have he := h.op_foldl_below (path op r (x :: xs)) y (ys ++ [r])
      have hd : (ys ++ [r]).foldl op ((xs.foldl op x ⋄ r) ⋄ y) =
          (xs ++ y :: ys ++ [r]).foldl op x := by
        have hh := h.foldl_delete (xs.foldl op x) r (y :: ys ++ [r]) (by simp)
        simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using hh
      simp only [path, List.foldl_append, List.foldl_cons, List.foldl_nil] at he
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at hd
      rw [hd] at he
      simpa only [path, List.cons_append, List.foldl_append, List.foldl_cons,
        List.foldl_nil] using he

/-- A path lies below every suffix beginning at one of its positions. -/
theorem path_below_suffix (r x : M) (before after : List M) :
    path op r (before ++ x :: after) ≼ path op r (x :: after) := by
  cases before with
  | nil => exact h.below_refl _
  | cons y ys =>
    change (ys ++ x :: after).foldl op y ⋄ r ≼ after.foldl op x ⋄ r
    have he := h.foldl_mono (h.op_below_right (ys.foldl op y) x) (after ++ [r])
    simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using he

/-- The suffix-coverage step: prerequisites already present in the target
suffix can be deleted after concatenating the two common-root paths. -/
theorem path_fusion (r x : M) (xs zs : List M)
    (hz : ∀ z ∈ zs, z ∈ xs ++ [r]) :
    path op r xs ⋄ path op r (x :: zs) ≼ path op r (x :: xs) := by
  rw [h.comm_of_fixed (h.path_fixed r xs) (h.path_fixed r (x :: zs))]
  have he := h.path_concat_below r (x :: zs) xs
  have hd : path op r ((x :: zs) ++ xs) = path op r (x :: xs) := by
    change (zs ++ xs).foldl op x ⋄ r = xs.foldl op x ⋄ r
    have hh := h.foldl_delete_block x zs (xs ++ [r]) hz
    simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using hh
  rwa [hd] at he

end Laws
end KFOL.Reset
