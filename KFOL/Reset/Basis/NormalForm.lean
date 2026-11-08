module

public import KFOL.Reset.Basis.Words
public import KFOL.Reset.Selection

/-! # Common-root path normal forms in every six-law algebra -/

@[expose] public section

namespace KFOL.Reset

universe u v

/-- Generic interpretation delegates to mathlib realization. -/
def interpret {M : Type u} {Var : Type v} (op : M → M → M) (v : Var → M) (t : Term Var) : M :=
  let _ := structureOf op
  t.realize v

namespace Term

/-- Prefixes of the common-root constituents. No choice of normal-form order
or deletion of duplicate variable labels is needed for the completeness proof. -/
def paths {Var : Type v} : Term Var → List (List Var)
  | .var _ => [[]]
  | .func .reset args =>
    (paths (args 0)).map (fun p => p ++ [root (args 0)]) ++ paths (args 1)

@[simp] theorem paths_step {Var : Type v} (s t : Term Var) :
    (step s t).paths = s.paths.map (fun p => p ++ [s.root]) ++ t.paths := rfl

theorem paths_ne_nil {Var : Type v} (t : Term Var) : t.paths ≠ [] := by
  induction t using induction_reset with
  | var => simp [paths]
  | step s t _ ih =>
    rw [paths_step]
    intro he
    exact ih (List.append_eq_nil_iff.mp he).2

end Term

namespace Laws

variable {M : Type u} {op : M → M → M} (h : Laws op)
local infixl:70 " ⋄ " => op
local infix:50 " ≼ " => Below (op := op)
include h

theorem foldr_fixed (r : M) (xs : List M) (hx : ∀ x ∈ xs, x ⋄ r = x) :
    xs.foldr op r ⋄ r = xs.foldr op r := by
  induction xs with
  | nil => exact h.idem r
  | cons x xs ih =>
    exact h.below_trans (h.op_below_right x _)
      (ih (fun a ha => hx a (List.mem_cons_of_mem _ ha)))

theorem below_foldr {b r : M} (hbr : b ≼ r) (xs : List M)
    (hx : ∀ x ∈ xs, b ≼ x) : b ≼ xs.foldr op r := by
  induction xs with
  | nil => exact hbr
  | cons x xs ih =>
    exact h.below_op (hx x List.mem_cons_self)
      (ih (fun a ha => hx a (List.mem_cons_of_mem _ ha)))

theorem foldr_below_mem (r : M) (xs : List M) (hx : ∀ x ∈ xs, x ⋄ r = x)
    {a : M} (ha : a ∈ xs) : xs.foldr op r ≼ a := by
  induction xs with
  | nil => cases ha
  | cons x xs ih =>
    have htail := h.foldr_fixed r xs (fun a ha => hx a (List.mem_cons_of_mem _ ha))
    rcases List.mem_cons.mp ha with he | ha
    · subst a
      change (x ⋄ xs.foldr op r) ⋄ x = x ⋄ xs.foldr op r
      rw [h.comm_of_fixed (hx x List.mem_cons_self) htail]
      exact h.repeat_right _ _
    · exact h.below_trans (h.op_below_right x _) (ih
        (fun a ha => hx a (List.mem_cons_of_mem _ ha)) ha)

theorem foldr_append (r : M) (xs ys : List M)
    (hx : ∀ x ∈ xs, x ⋄ r = x) (hy : ∀ y ∈ ys, y ⋄ r = y) :
    (xs ++ ys).foldr op r = xs.foldr op r ⋄ ys.foldr op r := by
  induction xs with
  | nil =>
    change ys.foldr op r = r ⋄ ys.foldr op r
    rw [h.comm_of_fixed (h.idem r) (h.foldr_fixed r ys hy), h.foldr_fixed r ys hy]
  | cons x xs ih =>
    change x ⋄ (xs ++ ys).foldr op r = (x ⋄ xs.foldr op r) ⋄ ys.foldr op r
    rw [ih (fun a ha => hx a (List.mem_cons_of_mem _ ha))]
    exact h.assoc_of_fixed (hx x List.mem_cons_self)
      (h.foldr_fixed r xs (fun a ha => hx a (List.mem_cons_of_mem _ ha)))

theorem foldr_map_right (q r : M) (xs : List M) (hne : xs ≠ [])
    (hx : ∀ x ∈ xs, x ⋄ q = x) :
    xs.foldr op q ⋄ r = (xs.map (fun x => x ⋄ r)).foldr op r := by
  induction xs with
  | nil => exact False.elim (hne rfl)
  | cons x xs ih =>
    cases xs with
    | nil =>
      change (x ⋄ q) ⋄ r = (x ⋄ r) ⋄ r
      rw [hx x List.mem_cons_self, h.repeat_right]
    | cons y ys =>
      change (x ⋄ (y :: ys).foldr op q) ⋄ r =
        (x ⋄ r) ⋄ ((y :: ys).map (fun x => x ⋄ r)).foldr op r
      rw [h.distribute_of_fixed (hx x List.mem_cons_self)
        (h.foldr_fixed q _ (fun a ha => hx a (List.mem_cons_of_mem _ ha))) r]
      rw [ih (by simp) (fun a ha => hx a (List.mem_cons_of_mem _ ha))]

end Laws

@[simp] theorem path_append {M : Type u} (op : M → M → M) (r q : M) (xs : List M) :
    path op r (xs ++ [q]) = op (path op q xs) r := by
  cases xs <;> simp [path, List.foldl_append]

namespace Laws

variable {M : Type u} {op : M → M → M} (h : Laws op)
include h

/-- Each term is a product of left paths sharing its rightmost variable,
proved from the six equations in an arbitrary algebra. -/
theorem interpret_normal {Var : Type v} (v : Var → M) (t : Term Var) :
    interpret op v t =
      (t.paths.map (fun p => path op (v t.root) (p.map v))).foldr op (v t.root) := by
  induction t using Term.induction_reset with
  | var j => exact (h.idem (v j)).symm
  | step s t hs ht =>
    let S := s.paths.map (fun p => path op (v s.root) (p.map v))
    let T := t.paths.map (fun p => path op (v t.root) (p.map v))
    have hS : ∀ a ∈ S, op a (v s.root) = a := by
      rintro a ha
      obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha
      exact h.path_fixed _ _
    have hT : ∀ a ∈ T, op a (v t.root) = a := by
      rintro a ha
      obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha
      exact h.path_fixed _ _
    have hne : S ≠ [] := by
      intro he
      exact s.paths_ne_nil (List.map_eq_nil_iff.mp he)
    change op (interpret op v s) (interpret op v t) = _
    rw [hs, ht]
    change op (S.foldr op (v s.root)) (T.foldr op (v t.root)) = _
    have hmap : ((s.paths.map (fun p => p ++ [s.root])).map
        (fun p => path op (v t.root) (p.map v))) = S.map (fun a => op a (v t.root)) := by
      simp only [S, List.map_map, Function.comp_def, List.map_append, List.map_cons,
        List.map_nil, path_append]
    simp only [Term.paths_step, Term.root_step, List.map_append]
    rw [hmap, h.foldr_append _ _ _
      (by rintro a ha; obtain ⟨_, _, rfl⟩ := List.mem_map.mp ha; exact h.repeat_right _ _) hT]
    rw [← h.foldr_map_right _ _ S hne hS]
    have hf := h.foldr_fixed (v t.root) T hT
    have he := h.e10 (S.foldr op (v s.root)) (v t.root) (T.foldr op (v t.root))
    simpa only [hf] using he.symm

end Laws
end KFOL.Reset
