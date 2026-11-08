module

public import KFOL.Algebra

/-! The explicit basis, arbitrary carrier structures and genuine nonconsequences. -/

@[expose] public section

namespace KFOLTest.ResetBasis

open KFOL KFOL.Reset KFOL.Reset.Term

-- Padded declarations count actual variables, while the equations themselves
-- remain the exact six pieces of syntax displayed in the paper.
example : (basisAxiom 0).variableCount = 1 := by decide
example : (basisAxiom 1).variableCount = 2 := by decide
example : (basisAxiom 5).variableCount = 3 := by decide

-- The arbitrary-algebra interface permits empty carriers; variety membership
-- separately imposes nonemptiness. Right projection satisfies all six laws.
example (M : Type) :
    let _ := structureOf (fun (_ y : M) => y)
    Equational.Models basis M := by
  let _ := structureOf (fun (_ y : M) => y)
  apply models_basis_iff.mpr
  constructor <;> intros <;> rfl

-- Idempotency by itself is insufficient: left projection fails R2.
example :
    let _ := structureOf (fun (x _ : Bool) => x)
    ¬Equational.Models basis Bool := by
  let _ := structureOf (fun (x _ : Bool) => x)
  change ¬Equational.Models basis Bool
  intro hm
  have bad := (models_basis_iff.mp hm).absorb false true
  change false = true at bad
  cases bad

private def three : Fin 3 ↪ Fin 3 := Function.Embedding.refl _

-- A nested consequence is derivable for arbitrary terms, not only variables
-- appearing in the original finite-arity presentation.
example {Var : Type} (x y z : Reset.Term Var) :
    Equational.Derives basis (step (step x y) (step z y)) (step x (step z y)) := by
  apply (derives_iff_eval_eq three _ _).mpr
  intro v
  exact (winnerSet_laws (Fin 3)).e10 (x.eval v) (y.eval v) (z.eval v)

private def leftAssoc : Reset.Term (Fin 3) := step (step (.var 0) (.var 1)) (.var 2)
private def rightAssoc : Reset.Term (Fin 3) := step (.var 0) (step (.var 1) (.var 2))

-- The basis does not accidentally add associativity. This separates a false
-- equation by a concrete winner-set valuation, then uses soundness.
example : ¬Equational.Derives basis leftAssoc rightAssoc := by
  intro hd
  let v : Fin 3 → WinnerSet (Fin 3) := fun i =>
    chainValue three (if i = 0 then 2 else if i = 1 then 0 else 1)
  have he := (derives_iff_eval_eq three leftAssoc rightAssoc).mp hd v
  change ((chainValue three 2).reset (chainValue three 0)).reset (chainValue three 1) =
    (chainValue three 2).reset ((chainValue three 0).reset (chainValue three 1)) at he
  rw [reset_chainValue, reset_chainValue, reset_chainValue, reset_chainValue] at he
  change chainValue three 1 = chainValue three 2 at he
  have hm : three 2 ∈ (chainValue three 1).val ↔ three 2 ∈ (chainValue three 2).val := by rw [he]
  simp only [marker_chainValue] at hm
  exact (by decide : (1 : Fin 3) ≠ 2) (hm.mpr trivial)

end KFOLTest.ResetBasis
