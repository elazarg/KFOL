module

public import KFOL.Algebra.TwoPlayers.Kleene.NormalForm
public import Mathlib.Order.Fin.Basic

/-! # The complete literal obstruction for bounded Kleene inequalities -/

@[expose] public section

namespace KFOL.TwoPlayers.Kleene

universe u v

/-- Opposite signs of one variable occur across the two monomials. -/
def Cross {Var : Type v} (A B : Monomial Var) : Prop :=
  ∃ x b, (x,b) ∈ A ∧ (x,!b) ∈ B

/-- Both signs of one variable occur in one monomial. -/
def HasPair {Var : Type v} (A : Monomial Var) : Prop :=
  ∃ x, (x,false) ∈ A ∧ (x,true) ∈ A

/-- Set literals of A to top when consistent, and unmentioned variables to
ambiguity. Its definition does not depend on the inequality to be tested. -/
def probe {Var : Type v} [DecidableEq Var] (A : Monomial Var) (x : Var) : Fin 3 :=
  if (x,false) ∈ A then 2 else if (x,true) ∈ A then 0 else 1

section Probe

variable {Var : Type v} [DecidableEq Var] (A B : Monomial Var)

theorem probe_literal_top (ha : ¬HasPair A) (l : Literal Var) (hl : l ∈ A) :
    evalLiteral Fin.rev (probe A) l = (2 : Fin 3) := by
  rcases l with ⟨x,b⟩
  cases b
  · simp [evalLiteral,probe,hl]
  · have hnot : (x,false) ∉ A := fun h => ha ⟨x,h,hl⟩
    simp [evalLiteral,probe,hnot,hl]

theorem probe_other_literal (hab : ¬Cross A B) (l : Literal Var) (hl : l ∈ B) :
    (1 : Fin 3) ≤ evalLiteral Fin.rev (probe A) l := by
  rcases l with ⟨x,b⟩
  cases b
  · have hnot : (x,true) ∉ A := fun h => hab ⟨x,true,h,hl⟩
    by_cases hx : (x,false) ∈ A <;> simp [evalLiteral,probe,hx,hnot]
  · have hnot : (x,false) ∉ A := fun h => hab ⟨x,false,h,hl⟩
    by_cases hx : (x,true) ∈ A <;> simp [evalLiteral,probe,hx,hnot]

theorem probe_monomial_top (ha : ¬HasPair A) : evalMonomial Fin.rev (probe A) A = (2 : Fin 3) := by
  apply top_le_iff.mp
  exact Finset.le_inf (fun l hl => by rw [probe_literal_top A ha l hl]; exact le_rfl)

theorem probe_other_monomial (hab : ¬Cross A B) :
    (1 : Fin 3) ≤ evalMonomial Fin.rev (probe A) B :=
  Finset.le_inf (fun l hl => probe_other_literal A B hab l hl)

/-- Every universal three-valued monomial inequality has one of the two
literal explanations, including empty meets. -/
theorem monomial_cover_of_three
    (h : ∀ v : Var → Fin 3, evalMonomial Fin.rev v A ≤ (evalMonomial Fin.rev v B).rev) :
    Cross A B ∨ (HasPair A ∧ HasPair B) := by
  classical
  by_cases hc : Cross A B
  · exact Or.inl hc
  by_cases ha : HasPair A
  · by_cases hb : HasPair B
    · exact Or.inr ⟨ha,hb⟩
    · have hcb : ¬Cross B A := by
        rintro ⟨x,b,hb,ha⟩
        exact hc ⟨x,!b,ha,by simpa using hb⟩
      have htest := h (probe B)
      rw [probe_monomial_top B hb] at htest
      have hlo := probe_other_monomial B A hcb
      exact False.elim ((by decide : ¬((1 : Fin 3) ≤ 0)) (hlo.trans htest))
  · have htest := h (probe A)
    rw [probe_monomial_top A ha] at htest
    have hlo := probe_other_monomial A B hc
    have hrev : (evalMonomial Fin.rev (probe A) B).rev ≤ (1 : Fin 3) := Fin.rev_anti hlo
    exact False.elim ((by decide : ¬((2 : Fin 3) ≤ 1)) (htest.trans hrev))

end Probe

section Transfer

variable {M : Type u} [DistribLattice M] [BoundedOrder M]
    (neg : M → M) (hn : ∀ x, neg (neg x) = x)
    (hd : ∀ x y, neg (x ⊓ y) = neg x ⊔ neg y)
    (hk : ∀ x y, x ⊓ neg x ≤ y ⊔ neg y)
    {Var : Type v} (v : Var → M)

omit [DistribLattice M] [BoundedOrder M] in
include hn in
theorem literal_complement (l : Literal Var) :
    evalLiteral neg v l = neg (evalLiteral neg v (l.1,!l.2)) := by
  rcases l with ⟨x,b⟩
  cases b <;> simp [evalLiteral,hn]

include hn hd in
theorem monomial_le_neg_of_cross (A B : Monomial Var) (hc : Cross A B) :
    evalMonomial neg v A ≤ neg (evalMonomial neg v B) := by
  obtain ⟨x,b,ha,hb⟩ := hc
  calc
    evalMonomial neg v A ≤ evalLiteral neg v (x,b) := Finset.inf_le ha
    _ = neg (evalLiteral neg v (x,!b)) := literal_complement neg hn v (x,b)
    _ ≤ neg (evalMonomial neg v B) := neg_antitone neg hd (Finset.inf_le hb)

include hn hd hk in
theorem monomial_le_neg_of_pairs (A B : Monomial Var) (ha : HasPair A) (hb : HasPair B) :
    evalMonomial neg v A ≤ neg (evalMonomial neg v B) := by
  obtain ⟨x,hx0,hx1⟩ := ha
  obtain ⟨y,hy0,hy1⟩ := hb
  have hA : evalMonomial neg v A ≤ v x ⊓ neg (v x) :=
    le_inf (Finset.inf_le hx0) (Finset.inf_le hx1)
  have hB : evalMonomial neg v B ≤ v y ⊓ neg (v y) :=
    le_inf (Finset.inf_le hy0) (Finset.inf_le hy1)
  calc
    evalMonomial neg v A ≤ v x ⊓ neg (v x) := hA
    _ ≤ v y ⊔ neg (v y) := hk _ _
    _ = neg (v y ⊓ neg (v y)) := by rw [hd,hn,sup_comm]
    _ ≤ neg (evalMonomial neg v B) := neg_antitone neg hd hB

include hn hd hk in
/-- Every three-valued monomial inequality is valid in every bounded Kleene
model. This is the separating-valuation core of completeness. -/
theorem monomial_transfer (A B : Monomial Var)
    (h : ∀ w : Var → Fin 3, evalMonomial Fin.rev w A ≤ (evalMonomial Fin.rev w B).rev) :
    evalMonomial neg v A ≤ neg (evalMonomial neg v B) := by
  classical
  rcases monomial_cover_of_three A B h with hc | ⟨ha,hb⟩
  · exact monomial_le_neg_of_cross neg hn hd v A B hc
  · exact monomial_le_neg_of_pairs neg hn hd hk v A B ha hb

end Transfer

end KFOL.TwoPlayers.Kleene
