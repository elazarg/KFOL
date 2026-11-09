module

public import KFOL.Definitions.Dissemilattice
public import KFOL.Algebra.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Order.Lattice

/-! # Semantic laws, the literal seven equations, and their two generators -/

@[expose] public section

namespace KFOL.Dissemilattice

universe u v

open FirstOrder

variable {M : Type u} [(Equational.language Symbol).Structure M]

@[simp] theorem funMap_join (args : Fin 2 → M) :
    Language.Structure.funMap (L := Equational.language Symbol) Symbol.join args = add (args 0) (args 1) := by
  unfold add
  congr 1
  funext i
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl <;> rfl

@[simp] theorem funMap_mul (args : Fin 2 → M) :
    Language.Structure.funMap (L := Equational.language Symbol) Symbol.mul args = mul (args 0) (args 1) := by
  unfold mul
  congr 1
  funext i
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl <;> rfl

@[simp] theorem realize_join {Var : Type v} (s t : Term Var) (v : Var → M) :
    (joinTerm s t).realize v = add (s.realize v) (t.realize v) := by
  change Language.Structure.funMap _ (fun i => (if i = 0 then s else t).realize v) = _
  unfold add
  congr 1
  funext i
  split <;> rfl

@[simp] theorem realize_mul {Var : Type v} (s t : Term Var) (v : Var → M) :
    (mulTerm s t).realize v = mul (s.realize v) (t.realize v) := by
  change Language.Structure.funMap _ (fun i => (if i = 0 then s else t).realize v) = _
  unfold mul
  congr 1
  funext i
  split <;> rfl

/-- The semantic seven-law structure is equivalent to satisfaction of the
independently listed seven actual finite-arity identities. -/
theorem laws_iff_models : Laws (M := M) add mul ↔ Equational.Models theory M := by
  constructor
  · intro h e he
    obtain ⟨i,rfl⟩ := he
    intro v
    change Fin 3 → M at v
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [basisAxiom] using h.add_idem (v 0)
    · simpa [basisAxiom] using h.add_comm (v 0) (v 1)
    · simpa [basisAxiom] using h.add_assoc (v 0) (v 1) (v 2)
    · simpa [basisAxiom] using h.mul_idem (v 0)
    · simpa [basisAxiom] using h.mul_comm (v 0) (v 1)
    · simpa [basisAxiom] using h.mul_assoc (v 0) (v 1) (v 2)
    · simpa [basisAxiom] using h.mul_add (v 0) (v 1) (v 2)
  · intro h
    have hi (i : Fin 7) := h (basisAxiom i) ⟨i,rfl⟩
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    · intro x; simpa [basisAxiom] using hi 0 (fun _ => x)
    · intro x y; simpa [basisAxiom] using hi 1 ![x,y,x]
    · intro x y z; simpa [basisAxiom] using hi 2 ![x,y,z]
    · intro x; simpa [basisAxiom] using hi 3 (fun _ => x)
    · intro x y; simpa [basisAxiom] using hi 4 ![x,y,x]
    · intro x y z; simpa [basisAxiom] using hi 5 ![x,y,z]
    · intro x y z; simpa [basisAxiom] using hi 6 ![x,y,z]

/-- The raw winner operation distributes over actual union, without any
assumption that the other distributive or lattice absorption laws hold. -/
theorem winner_mul_add {Role : Type v} (owner : Role) (x y z : WinnerSet Role) :
    WinnerSet.choice owner x (y.union z) =
      (WinnerSet.choice owner x y).union (WinnerSet.choice owner x z) := by
  classical
  by_cases hx : x = WinnerSet.singleton owner <;>
    by_cases hy : y = WinnerSet.singleton owner <;>
    by_cases hz : z = WinnerSet.singleton owner
  all_goals simp_all [WinnerSet.choice,WinnerSet.union_eq_singleton_iff]
  all_goals apply Subtype.ext
  all_goals ext r
  all_goals simp only [WinnerSet.val_union,Set.mem_union]
  all_goals tauto

/-- All seven equations hold in the actual raw winner-set fragment. -/
theorem winner_laws {Role : Type v} (owner : Role) :
    letI := winnerStructure owner
    Laws (M := WinnerSet Role) add mul := by
  let _ := winnerStructure owner
  refine ⟨WinnerSet.union_self,WinnerSet.union_comm,?_,
    fun x => WinnerSet.choice_self x owner,
    fun x y => WinnerSet.choice_comm x y owner,
    fun x y z => WinnerSet.choice_assoc x y owner z,winner_mul_add owner⟩
  intro x y z
  apply Subtype.ext
  exact Set.union_assoc _ _ _

/-- The concrete three-element tables satisfy exactly the required seven
laws; this finite table check is kernel evaluated. -/
theorem three_laws : Laws Three.add Three.mul := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  all_goals intros
  all_goals repeat first | rfl | rename_i x; cases x

namespace Laws

variable {plus times : M → M → M} (h : Laws plus times)

include h

omit [(Equational.language Symbol).Structure M] in
/-- Right distribution follows by commutativity of the owned operation. -/
theorem add_mul (x y z : M) : times (plus x y) z = plus (times x z) (times y z) := by
  rw [h.mul_comm,h.mul_add,h.mul_comm z x,h.mul_comm z y]

omit [(Equational.language Symbol).Structure M] in
/-- The join order and the meet order are separate semilattice structures.
No lattice or absorption interface is asserted. -/
@[instance_reducible] def joinSemilattice : SemilatticeSup M :=
  letI : Max M := ⟨plus⟩
  SemilatticeSup.mk' h.add_comm h.add_assoc h.add_idem

omit [(Equational.language Symbol).Structure M] in
@[instance_reducible] def meetSemilattice : SemilatticeInf M :=
  letI : Min M := ⟨times⟩
  SemilatticeInf.mk' h.mul_comm h.mul_assoc h.mul_idem

end Laws

end KFOL.Dissemilattice
