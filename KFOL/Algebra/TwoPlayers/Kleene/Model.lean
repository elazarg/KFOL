module

public import KFOL.Definitions.Kleene
public import Mathlib.Order.Lattice
public import Mathlib.Data.Finset.Lattice.Prod

/-! # Order structure and involution consequences of the Kleene laws -/

@[expose] public section

namespace KFOL.TwoPlayers.Kleene

universe u

namespace Laws

variable {M : Type u} {zero one : M} {plus times : M → M → M} {neg : M → M}
    (h : Laws zero one plus times neg)

@[instance_reducible] def lattice : Lattice M :=
  letI : Max M := ⟨plus⟩
  letI : Min M := ⟨times⟩
  Lattice.mk' h.semilattice.add_comm h.semilattice.add_assoc
    h.semilattice.mul_comm h.semilattice.mul_assoc h.add_mul h.mul_add

@[instance_reducible] def distribLattice : DistribLattice M := by
  letI := h.lattice
  exact DistribLattice.ofInfSupLe (fun x y z => by
    change times x (plus y z) ≤ plus (times x y) (times x z)
    rw [h.semilattice.mul_add])

@[instance_reducible] def boundedOrder : @BoundedOrder M h.lattice.toLE := by
  letI := h.lattice
  exact { bot := zero
          top := one
          bot_le := fun x => h.zero_add x
          le_top := fun x => inf_eq_left.mp (by
      change times x one = x
      rw [h.semilattice.mul_comm,h.one_mul]) }

end Laws

section Order

variable {M : Type u} [DistribLattice M] [BoundedOrder M]
    (neg : M → M) (hn : ∀ x, neg (neg x) = x)
    (hd : ∀ x y, neg (x ⊓ y) = neg x ⊔ neg y) (h0 : neg ⊥ = ⊤)

omit [BoundedOrder M] in
include hn hd in
/-- De Morgan for joins follows from involution and De Morgan for meets. -/
theorem neg_sup (x y : M) : neg (x ⊔ y) = neg x ⊓ neg y := by
  have he := congrArg neg (hd (neg x) (neg y))
  simpa only [hn] using he.symm

include hn h0 in
theorem neg_top : neg ⊤ = ⊥ := by rw [← h0,hn]

omit [BoundedOrder M] in
include hd in
theorem neg_antitone : Antitone neg := by
  intro x y hxy
  have hmeet : x ⊓ y = x := inf_eq_left.mpr hxy
  have he := hd x y
  rw [hmeet] at he
  exact le_sup_right.trans_eq he.symm

include hn hd h0 in
theorem neg_finset_sup {Index : Type*} (S : Finset Index) (f : Index → M) :
    neg (S.sup f) = S.inf (fun x => neg (f x)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using h0
  | @insert i S hi ih => simp only [Finset.sup_insert,Finset.inf_insert,neg_sup neg hn hd,ih]

include hn hd h0 in
theorem neg_finset_inf {Index : Type*} (S : Finset Index) (f : Index → M) :
    neg (S.inf f) = S.sup (fun x => neg (f x)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using neg_top neg hn h0
  | @insert i S hi ih => simp only [Finset.inf_insert,Finset.sup_insert,hd,ih]

end Order

end KFOL.TwoPlayers.Kleene
