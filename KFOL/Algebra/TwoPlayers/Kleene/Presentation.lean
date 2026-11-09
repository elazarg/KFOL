module

public import KFOL.Algebra.TwoPlayers.Kleene.Model
public import Mathlib.Data.Fin.VecNotation

/-! # Literal finite equations are exactly the raw bounded Kleene laws -/

@[expose] public section

namespace KFOL.TwoPlayers.Kleene

universe u v

open FirstOrder

variable {M : Type u} [inst : (Equational.language Symbol).Structure M]

@[simp] theorem funMap_neg (args : Fin 1 → M) :
    Language.Structure.funMap (L := Equational.language Symbol) .neg args = operationNeg M (args 0) := by
  unfold operationNeg
  congr 1
  funext i
  have hi : i = 0 := by omega
  subst i
  rfl

@[simp] theorem funMap_join (args : Fin 2 → M) :
    Language.Structure.funMap (L := Equational.language Symbol) .join args =
      operationJoin M (args 0) (args 1) := by
  unfold operationJoin
  congr 1
  funext i
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl <;> rfl

@[simp] theorem funMap_meet (args : Fin 2 → M) :
    Language.Structure.funMap (L := Equational.language Symbol) .meet args =
      operationMeet M (args 0) (args 1) := by
  unfold operationMeet
  congr 1
  funext i
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl <;> rfl

@[simp] theorem realize_bot {Var : Type v} (v : Var → M) :
    (botTerm : Term Var).realize v = operationZero M := by
  change Language.Structure.funMap (L := Equational.language Symbol) .bot _ = _
  unfold operationZero
  congr 1
  funext i
  exact Fin.elim0 i

@[simp] theorem realize_top {Var : Type v} (v : Var → M) :
    (topTerm : Term Var).realize v = operationOne M := by
  change Language.Structure.funMap (L := Equational.language Symbol) .top _ = _
  unfold operationOne
  congr 1
  funext i
  exact Fin.elim0 i

@[simp] theorem realize_neg {Var : Type v} (t : Term Var) (v : Var → M) :
    (negTerm t).realize v = operationNeg M (t.realize v) := rfl

@[simp] theorem realize_join {Var : Type v} (s t : Term Var) (v : Var → M) :
    (joinTerm s t).realize v = operationJoin M (s.realize v) (t.realize v) := by
  change Language.Structure.funMap _ (fun i => (if i = 0 then s else t).realize v) = _
  unfold operationJoin
  congr 1
  funext i
  split <;> rfl

@[simp] theorem realize_meet {Var : Type v} (s t : Term Var) (v : Var → M) :
    (meetTerm s t).realize v = operationMeet M (s.realize v) (t.realize v) := by
  change Language.Structure.funMap _ (fun i => (if i = 0 then s else t).realize v) = _
  unfold operationMeet
  congr 1
  funext i
  split <;> rfl

/-- An arbitrary structure is exactly reconstructed from its five operations. -/
theorem structure_eq : inst = structureOf (operationZero M) (operationOne M)
    (operationJoin M) (operationMeet M) (operationNeg M) := by
  apply Language.Structure.ext
  · funext n f args
    cases f
    · change Language.Structure.funMap (L := Equational.language Symbol) .bot args = operationZero M
      unfold operationZero
      congr 1
      funext i
      exact Fin.elim0 i
    · change Language.Structure.funMap (L := Equational.language Symbol) .top args = operationOne M
      unfold operationOne
      congr 1
      funext i
      exact Fin.elim0 i
    · exact funMap_neg args
    · exact funMap_join args
    · exact funMap_meet args
  · funext n r
    cases r

/-- Satisfaction of the literal fifteen equations is equivalent to the
independently stated raw lattice and negation laws. -/
theorem laws_iff_models :
    Laws (operationZero M) (operationOne M) (operationJoin M) (operationMeet M) (operationNeg M) ↔
      Equational.Models basis M := by
  constructor
  · intro h e he
    obtain ⟨i,rfl⟩ := he
    intro v
    change Fin 3 → M at v
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
        i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [basisAxiom] using h.semilattice.add_idem (v 0)
    · simpa [basisAxiom] using h.semilattice.add_comm (v 0) (v 1)
    · simpa [basisAxiom] using h.semilattice.add_assoc (v 0) (v 1) (v 2)
    · simpa [basisAxiom] using h.semilattice.mul_idem (v 0)
    · simpa [basisAxiom] using h.semilattice.mul_comm (v 0) (v 1)
    · simpa [basisAxiom] using h.semilattice.mul_assoc (v 0) (v 1) (v 2)
    · simpa [basisAxiom] using h.semilattice.mul_add (v 0) (v 1) (v 2)
    · simpa [basisAxiom] using h.add_mul (v 0) (v 1)
    · simpa [basisAxiom] using h.mul_add (v 0) (v 1)
    · simpa [basisAxiom] using h.zero_add (v 0)
    · simpa [basisAxiom] using h.one_mul (v 0)
    · simpa [basisAxiom] using h.neg_neg (v 0)
    · simpa [basisAxiom] using h.neg_mul (v 0) (v 1)
    · simpa [basisAxiom] using h.neg_zero
    · simpa [basisAxiom] using h.kleene (v 0) (v 1)
  · intro h
    have hi (i : Fin 15) := h (basisAxiom i) ⟨i,rfl⟩
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
      · intro x; simpa [basisAxiom] using hi 0 (fun _ => x)
      · intro x y; simpa [basisAxiom] using hi 1 ![x,y,x]
      · intro x y z; simpa [basisAxiom] using hi 2 ![x,y,z]
      · intro x; simpa [basisAxiom] using hi 3 (fun _ => x)
      · intro x y; simpa [basisAxiom] using hi 4 ![x,y,x]
      · intro x y z; simpa [basisAxiom] using hi 5 ![x,y,z]
      · intro x y z; simpa [basisAxiom] using hi 6 ![x,y,z]
    · intro x y; simpa [basisAxiom] using hi 7 ![x,y,x]
    · intro x y; simpa [basisAxiom] using hi 8 ![x,y,x]
    · intro x; simpa [basisAxiom] using hi 9 (fun _ => x)
    · intro x; simpa [basisAxiom] using hi 10 (fun _ => x)
    · intro x; simpa [basisAxiom] using hi 11 (fun _ => x)
    · intro x y; simpa [basisAxiom] using hi 12 ![x,y,x]
    · simpa [basisAxiom] using hi 13 (fun _ => operationZero M)
    · intro x y; simpa [basisAxiom] using hi 14 ![x,y,x]

end KFOL.TwoPlayers.Kleene
