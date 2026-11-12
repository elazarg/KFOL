module

public import KFOL.Core.AtomicBasis.Quotient
public import KFOL.Core.AtomicBasis.Lifting
public import KFOL.Equational.Preservation
public import Mathlib.Order.PrimeSeparator

/-! # Distributive-lattice images of the owner closures -/

@[expose] public section

namespace KFOL.Core.AtomicBasis

universe u v

open FirstOrder

variable {Role : Type u} [DecidableEq Role]

@[instance_reducible] def latticeStructure (i : Role) (M : Type v) [Lattice M] :
    (Equational.language (Equational.CoreSymbol Role)).Structure M where
  funMap f args := match f with
    | .choice r => if r = i then args 0 ⊓ args 1 else args 0 ⊔ args 1
  RelMap r := nomatch r

@[simp] theorem lattice_operation {M : Type v} [Lattice M] (i r : Role) (x y : M) :
    letI := latticeStructure i M
    operation r x y = if r = i then x ⊓ y else x ⊔ y := rfl

/-- Prime-ideal membership reverses the lattice order, matching the owner
Boolean image (own OR, foreign AND). -/
noncomputable def primeIdealHom {M : Type v} [DistribLattice M] (i : Role)
    (J : Order.Ideal M) (hJ : Order.Ideal.IsPrime J) :
    letI := latticeStructure i M
    letI := booleanStructure i
    M →[Equational.language (Equational.CoreSymbol Role)] Bool := by
  classical
  letI := latticeStructure i M
  letI := booleanStructure i
  refine { toFun := fun x => decide (x ∈ J), map_fun' := ?_ }
  intro n f args
  cases f with
  | choice r =>
    change decide ((if r = i then args 0 ⊓ args 1 else args 0 ⊔ args 1) ∈ J) =
      if r = i then decide (args 0 ∈ J) || decide (args 1 ∈ J)
      else decide (args 0 ∈ J) && decide (args 1 ∈ J)
    by_cases hri : r = i
    · simp only [ite_eq_left hri]
      rw [show args 0 ⊓ args 1 ∈ J ↔ args 0 ∈ J ∨ args 1 ∈ J from
        ⟨hJ.mem_or_mem, fun h => h.elim (J.lower inf_le_left) (J.lower inf_le_right)⟩]
      simp
    · simp only [ite_eq_right hri, Order.Ideal.sup_mem_iff]
      simp

/-- Every distributive-lattice owner image satisfies all identities of its
Boolean image. This uses mathlib's proved prime-ideal separation theorem. -/
theorem lattice_holds_of_boolean {M : Type v} [DistribLattice M] (i : Role)
    (e : Equational.Identity (Equational.CoreSymbol Role))
    (he : letI := booleanStructure i; e.Holds Bool) :
    letI := latticeStructure i M
    e.Holds M := by
  classical
  let _ := latticeStructure i M
  let _ := booleanStructure i
  intro v
  have test (a b : M) (hab : ¬a ≤ b)
      (heq : ∀ J (hJ : Order.Ideal.IsPrime J),
        (primeIdealHom i J hJ) a = (primeIdealHom i J hJ) b) : False := by
    have hd : Disjoint (Order.PFilter.principal a : Set M) (Order.Ideal.principal b : Set M) := by
      apply Set.disjoint_left.mpr
      intro z hz hzb
      exact hab (hz.trans hzb)
    obtain ⟨J, hJ, hIJ, hdisj⟩ := DistribLattice.prime_ideal_of_disjoint_filter_ideal hd
    have hb : b ∈ J := hIJ Order.Ideal.mem_principal_self
    have ha : a ∈ J := by
      have hh := heq J hJ
      change decide (a ∈ J) = decide (b ∈ J) at hh
      simpa [hb] using hh
    exact Set.disjoint_left.mp hdisj (show a ∈ Order.PFilter.principal a from le_rfl) ha
  have hall (J : Order.Ideal M) (hJ : Order.Ideal.IsPrime J) :
      (primeIdealHom i J hJ) (e.lhs.realize v) =
        (primeIdealHom i J hJ) (e.rhs.realize v) := by
    rw [← FirstOrder.Language.HomClass.realize_term, ← FirstOrder.Language.HomClass.realize_term]
    exact he _
  apply le_antisymm
  · by_contra hab
    exact test _ _ hab hall
  · by_contra hab
    exact test _ _ hab (fun J hJ => (hall J hJ).symm)

namespace LiftingLaws

variable {M : Type v} {add : M → M → M} {op : Role → M → M → M}
    (h : AtomicBasis.LiftingLaws add op) [Nontrivial Role]

/-- A fixed point of one owner closure below a common upper bound. -/
abbrev Point (i : Role) (u : M) := {x : M // letI := h.semilattice; x ≤ u ∧ op i x u = x}

@[instance_reducible] def pointLattice (i : Role) (u : M) : Lattice (h.Point i u) := by
  letI := h.semilattice
  let sup (a b : h.Point i u) : h.Point i u :=
    ⟨add a.val b.val, sup_le a.property.1 b.property.1, by
      rw [h.add_op, a.property.2, b.property.2]⟩
  let inf (a b : h.Point i u) : h.Point i u :=
    ⟨op i a.val b.val, h.op_bound_upper i a.property.1 b.property.1, by
      rw [h.closure_own, a.property.2, b.property.2]⟩
  refine { (PartialOrder.lift Subtype.val Subtype.val_injective) with
    sup := sup
    inf := inf
    le_sup_left := ?_
    le_sup_right := ?_
    sup_le := ?_
    inf_le_left := ?_
    inf_le_right := ?_
    le_inf := ?_ }
  · intro a b; exact le_sup_left (α := M)
  · intro a b; exact le_sup_right (α := M)
  · intro a b c hab hac
    change a.val ≤ c.val at hab
    change b.val ≤ c.val at hac
    exact sup_le hab hac
  · intro a b
    change op i a.val b.val ≤ a.val
    exact (h.monotone_right i a.val b.property.1).trans_eq a.property.2
  · intro a b
    change op i a.val b.val ≤ b.val
    rw [h.op_comm i a.val b.val]
    exact (h.monotone_right i b.val a.property.1).trans_eq b.property.2
  · intro a b c hab hac
    change a.val ≤ op i b.val c.val
    simpa only [h.op_idem] using h.monotone_op i hab hac

@[instance_reducible] def pointDistribLattice (i : Role) (u : M) : DistribLattice (h.Point i u) := by
  let _ := h.pointLattice i u
  apply DistribLattice.ofInfSupLe
  intro a b c
  apply le_of_eq
  apply Subtype.val_injective
  exact h.op_add i a.val b.val c.val

end LiftingLaws

end KFOL.Core.AtomicBasis
