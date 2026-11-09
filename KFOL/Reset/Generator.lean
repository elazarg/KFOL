module

public import KFOL.Reset.Chain
public import KFOL.Algebra.SmallCarriers

/-! # The exact three-element reset generator and its minimum cardinality -/

@[expose] public section

namespace KFOL.Reset

universe u v

private theorem chainValue_injective {Role : Type u} (three : Fin 3 ↪ Role) :
    Function.Injective (chainValue three) := by
  intro i j he
  have ha : (i ≠ 0 ↔ j ≠ 0) := by
    rw [← ambiguous_chainValue three i, ← ambiguous_chainValue three j, he]
  have hm : (i = 2 ↔ j = 2) := by
    rw [← marker_chainValue three i, ← marker_chainValue three j, he]
  apply Fin.ext
  omega

private theorem eval_chain {Role : Type u} {Var : Type v} (three : Fin 3 ↪ Role)
    (t : Term Var) (valuation : Var → Fin 3) :
    let _ := structureOf (fun i j : Fin 3 => if j = 0 then 0 else max i j)
    t.eval (fun j => chainValue three (valuation j)) = chainValue three (t.realize valuation) := by
  let _ := structureOf (fun i j : Fin 3 => if j = 0 then 0 else max i j)
  induction t using Term.induction_reset with
  | var => rfl
  | step s t hs ht =>
    rw [Term.eval_step, hs, ht]
    exact reset_chainValue three _ _

/-- The actual three-element multiplication table has exactly the winner-set
reset identities, for any role type containing three distinct roles. -/
theorem identity_iff_chain {Role : Type u} (three : Fin 3 ↪ Role)
    (e : Equational.Identity Symbol) :
    let _ := structureOf (WinnerSet.reset (Role := Role))
    let _ := structureOf (fun i j : Fin 3 => if j = 0 then 0 else max i j)
    e.Holds (WinnerSet Role) ↔ e.Holds (Fin 3) := by
  let _ := structureOf (WinnerSet.reset (Role := Role))
  let _ := structureOf (fun i j : Fin 3 => if j = 0 then 0 else max i j)
  constructor
  · intro hw valuation
    apply chainValue_injective three
    rw [← eval_chain three e.lhs, ← eval_chain three e.rhs]
    exact hw _
  · intro hc
    apply (Term.eval_eq_iff_chain e.lhs e.rhs three).mpr
    intro valuation hv
    classical
    let w : Fin e.arity → Fin 3 := fun j => (hv j).choose
    have he : valuation = fun j => chainValue three (w j) :=
      funext (fun j => (hv j).choose_spec)
    rw [he, eval_chain, eval_chain, hc w]

private theorem realize_step {M : Type u} [(Equational.language Symbol).Structure M]
    {Var : Type v} (s t : Term Var) (valuation : Var → M) :
    (Term.step s t).realize valuation = operation M (s.realize valuation) (t.realize valuation) := by
  simp only [Term.step, FirstOrder.Language.Term.realize, operation]
  congr 1
  funext i
  by_cases hi : i = 0 <;> simp [hi]

/-- Every finite algebra with precisely the chain's reset identities has
at least three elements. The small-carrier exclusion needs only idempotence. -/
theorem chain_minimum_generator {M : Type u} [Fintype M]
    [(Equational.language Symbol).Structure M]
    (hTheory : ∀ e : Equational.Identity Symbol,
      (letI := structureOf (fun i j : Fin 3 => if j = 0 then 0 else max i j);
        e.Holds (Fin 3)) ↔ e.Holds M) : 3 ≤ Fintype.card M := by
  let _ := structureOf (fun i j : Fin 3 => if j = 0 then 0 else max i j)
  by_contra hn
  have hc : Fintype.card M ≤ 2 := by omega
  let x : Term (Fin 3) := .var 0
  let y : Term (Fin 3) := .var 1
  let z : Term (Fin 3) := .var 2
  let idem : Equational.Identity Symbol := ⟨3, Term.step x x, x⟩
  have hid : idem.Holds (Fin 3) := by
    intro valuation
    have h : ∀ i : Fin 3, (if i = 0 then 0 else max i i) = i := by decide
    exact h (valuation 0)
  have hm := (hTheory idem).mp hid
  have hop : ∀ a : M, operation M a a = a := by
    intro a
    simpa only [idem, x, realize_step, FirstOrder.Language.Term.realize_var] using hm (fun _ => a)
  have hassoc := Algebra.idempotent_assoc_of_card_le_two (operation M) hop hc
  let assoc : Equational.Identity Symbol :=
    ⟨3, Term.step (Term.step x y) z, Term.step x (Term.step y z)⟩
  have ha : assoc.Holds M := by
    intro valuation
    simpa only [assoc, x, y, z, realize_step, FirstOrder.Language.Term.realize_var] using
      hassoc (valuation 0) (valuation 1) (valuation 2)
  have hchain := (hTheory assoc).mpr ha
  have h := hchain ![2, 0, 1]
  change (1 : Fin 3) = 2 at h
  exact (by decide : (1 : Fin 3) ≠ 2) h

end KFOL.Reset
