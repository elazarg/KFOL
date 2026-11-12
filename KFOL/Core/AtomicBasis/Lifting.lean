module

public import KFOL.Definitions.AtomicBasis
public import Mathlib.Order.Lattice

/-! # Closure maps in arbitrary models of the displayed lifting laws -/

@[expose] public section

namespace KFOL.Core.AtomicBasis.LiftingLaws

universe u v

variable {Role : Type u} {M : Type v} {add : M → M → M} {op : Role → M → M → M}
    (h : LiftingLaws add op)

@[instance_reducible] def semilattice : SemilatticeSup M :=
  letI : Max M := ⟨add⟩
  SemilatticeSup.mk' h.add_comm h.add_assoc h.add_idem

include h

theorem add_op (i : Role) (x y z : M) : op i (add x y) z = add (op i x z) (op i y z) := by
  rw [h.op_comm, h.op_add, h.op_comm i z x, h.op_comm i z y]

theorem monotone_right (i : Role) (x : M) :
    letI := h.semilattice
    Monotone (op i x) := by
  let _ := h.semilattice
  intro a b hab
  change add (op i x a) (op i x b) = op i x b
  rw [← h.op_add, show add a b = b from sup_eq_right.mpr hab]

theorem monotone_left (i : Role) (x : M) :
    letI := h.semilattice
    Monotone (fun y => op i y x) := by
  let _ := h.semilattice
  simpa only [h.op_comm] using h.monotone_right i x

theorem monotone_op (i : Role) {a b c d : M} :
    letI := h.semilattice
    a ≤ b → c ≤ d → op i a c ≤ op i b d := by
  let _ := h.semilattice
  intro hab hcd
  exact (h.monotone_left i c hab).trans (h.monotone_right i b hcd)

theorem op_bound [Nontrivial Role] (i : Role) (x y : M) :
    letI := h.semilattice
    op i x y ≤ add x y := by
  let _ := h.semilattice
  obtain ⟨j, hji⟩ := exists_ne i
  calc
    op i x y ≤ add (op i x y) (op j x y) := le_sup_left
    _ = add x y := h.cover i j hji.symm x y

theorem op_bound_upper [Nontrivial Role] (i : Role) {x y u : M} :
    letI := h.semilattice
    x ≤ u → y ≤ u → op i x y ≤ u := by
  let _ := h.semilattice
  intro hx hy
  exact (h.op_bound i x y).trans (sup_le hx hy)

theorem le_closure (i : Role) {x u : M} :
    letI := h.semilattice
    x ≤ u → x ≤ op i x u := by
  let _ := h.semilattice
  intro hx
  simpa only [h.op_idem] using h.monotone_right i x hx

theorem closure_idem (i : Role) (x u : M) : op i (op i x u) u = op i x u := by
  rw [h.op_assoc, h.op_idem]

/-- The two-owner interchange at the join of the arguments. -/
theorem interchange (i j : Role) (hij : i ≠ j) (x y : M) :
    op i (op j x y) (add x y) = op j (op i x y) (add x y) := by
  calc
    op i (op j x y) (add x y) = add (op i x (op j x y)) (op i y (op j y x)) := by
      rw [h.op_add, h.op_comm i (op j x y) x, h.op_comm i (op j x y) y,
        h.op_comm j y x]
    _ = add (op j x (op i x y)) (op j y (op i y x)) := by
      rw [h.birkhoff i j hij, h.birkhoff i j hij]
    _ = op j (op i x y) (add x y) := by
      rw [h.op_comm i y x, h.op_comm j x (op i x y),
        h.op_comm j y (op i x y), ← h.op_add]

theorem interchange_eq_join [Nontrivial Role] (i j : Role) (hij : i ≠ j) (x y : M) :
    op i (op j x y) (add x y) = add x y := by
  let _ := h.semilattice
  apply le_antisymm
  · exact h.op_bound_upper i (h.op_bound j x y) le_rfl
  · have h1 := h.le_closure i (h.op_bound j x y)
    have h2 := h.le_closure j (h.op_bound i x y)
    rw [← h.interchange i j hij x y] at h2
    calc
      add x y = add (op i x y) (op j x y) := (h.cover i j hij x y).symm
      _ ≤ op i (op j x y) (add x y) := sup_le h2 h1

/-- Each owner closure sends every other choice to neutral join. -/
theorem closure_other [Nontrivial Role] (i j : Role) (hij : i ≠ j) {x y u : M} :
    letI := h.semilattice
    x ≤ u → y ≤ u →
      op i (op j x y) u = add (op i x u) (op i y u) := by
  let _ := h.semilattice
  intro hx hy
  rw [← h.add_op]
  apply le_antisymm
  · exact h.monotone_left i u (h.op_bound j x y)
  · have hv : add x y ≤ op i (op j x y) u := by
      rw [← h.interchange_eq_join i j hij x y]
      exact h.monotone_right i (op j x y) (sup_le hx hy)
    have he := h.monotone_left i u hv
    simpa only [h.closure_idem] using he

/-- Each owner closure preserves its own choice. -/
theorem closure_own (i : Role) (x y u : M) :
    op i (op i x y) u = op i (op i x u) (op i y u) := by
  calc
    op i (op i x y) u = op i x (op i y u) := h.op_assoc _ _ _ _
    _ = op i x (op i y (op i u u)) := by rw [h.op_idem]
    _ = op i x (op i (op i y u) u) := by rw [h.op_assoc]
    _ = op i x (op i u (op i y u)) := by rw [h.op_comm i (op i y u) u]
    _ = op i (op i x u) (op i y u) := (h.op_assoc _ _ _ _).symm

end KFOL.Core.AtomicBasis.LiftingLaws
