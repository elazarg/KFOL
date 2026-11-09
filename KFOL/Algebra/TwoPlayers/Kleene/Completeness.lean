module

public import KFOL.Algebra.TwoPlayers.Kleene.Monomials
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.FinCases

/-! # The strong three-valued chain separates every bounded Kleene identity -/

@[expose] public section

namespace KFOL.TwoPlayers.Kleene

universe u v

theorem three_neg_neg (i : Fin 3) : i.rev.rev = i := Fin.rev_rev i

theorem three_neg_inf (i j : Fin 3) : (i ⊓ j).rev = i.rev ⊔ j.rev := by
  fin_cases i <;> fin_cases j <;> decide

theorem three_neg_bot : (⊥ : Fin 3).rev = ⊤ := by decide

/-- The actual three-element generator satisfies every raw presentation law. -/
theorem three_laws : Laws (0 : Fin 3) 2 max min Fin.rev := by
  constructor
  · constructor <;> decide
  all_goals decide

section Model

variable {M : Type u} [DistribLattice M] [BoundedOrder M]
    (neg : M → M) (hn : ∀ x, neg (neg x) = x)
    (hd : ∀ x y, neg (x ⊓ y) = neg x ⊔ neg y) (h0 : neg ⊥ = ⊤)
    (hk : ∀ x y, x ⊓ neg x ≤ y ⊔ neg y)
    {Var : Type v}

include hn hd h0 hk in
/-- Normal-form inequalities transfer from the three-element chain to every
bounded Kleene model, without a bound on the number of variables. -/
theorem normalForm_transfer (F G : NormalForm Var)
    (h : ∀ w : Var → Fin 3,
      evalNormalForm Fin.rev w F ≤ (evalNormalForm Fin.rev w G).rev)
    (v : Var → M) : evalNormalForm neg v F ≤ neg (evalNormalForm neg v G) := by
  unfold evalNormalForm
  rw [neg_finset_sup neg hn hd h0]
  apply Finset.sup_le
  intro A hA
  apply Finset.le_inf
  intro B hB
  apply monomial_transfer neg hn hd hk v A B
  intro w
  calc
    evalMonomial Fin.rev w A ≤ evalNormalForm Fin.rev w F := Finset.le_sup hA
    _ ≤ (evalNormalForm Fin.rev w G).rev := h w
    _ ≤ (evalMonomial Fin.rev w B).rev := Fin.rev_anti (Finset.le_sup hB)

include hn hd h0 hk in
/-- All term inequalities true on the three-element chain are true in every
bounded distributive lattice with De Morgan involution and the Kleene law. -/
theorem inequality_of_three (s t : Term Var)
    (h : let _ := threeStructure
      ∀ w : Var → Fin 3, s.realize w ≤ t.realize w) :
    let _ := structureOf (⊥ : M) ⊤ (· ⊔ ·) (· ⊓ ·) neg
    ∀ v : Var → M, s.realize v ≤ t.realize v := by
  classical
  let := structureOf (⊥ : M) ⊤ (· ⊔ ·) (· ⊓ ·) neg
  have source : ∀ w : Var → Fin 3,
      evalNormalForm Fin.rev w (normalForm false s) ≤
        (evalNormalForm Fin.rev w (normalForm true t)).rev := by
    let := threeStructure
    intro w
    have hs := normalForm_sound Fin.rev w three_neg_neg three_neg_inf three_neg_bot s false
    have ht := normalForm_sound Fin.rev w three_neg_neg three_neg_inf three_neg_bot t true
    simp only [Bool.false_eq_true,ite_false,ite_true] at hs ht
    rw [hs,ht,Fin.rev_rev]
    exact h w
  dsimp only
  intro v
  have he := normalForm_transfer neg hn hd h0 hk (normalForm false s) (normalForm true t) source v
  have hs := normalForm_sound neg v hn hd h0 s false
  have ht := normalForm_sound neg v hn hd h0 t true
  simp only [Bool.false_eq_true,ite_false,ite_true] at hs ht
  rw [hs,ht,hn] at he
  exact he

include hn hd h0 hk in
/-- The three-element chain generates all bounded Kleene algebras. -/
theorem equality_of_three (s t : Term Var)
    (h : let _ := threeStructure
      ∀ w : Var → Fin 3, s.realize w = t.realize w) :
    let _ := structureOf (⊥ : M) ⊤ (· ⊔ ·) (· ⊓ ·) neg
    ∀ v : Var → M, s.realize v = t.realize v := by
  dsimp only
  intro v
  exact le_antisymm
    (inequality_of_three neg hn hd h0 hk s t (fun w => (h w).le) v)
    (inequality_of_three neg hn hd h0 hk t s (fun w => (h w).ge) v)

end Model

end KFOL.TwoPlayers.Kleene
