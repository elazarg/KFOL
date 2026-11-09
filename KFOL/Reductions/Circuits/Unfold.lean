module

public import KFOL.Reductions.Circuits.Basic
public import KFOL.Reset.Chain

/-! Proof-level unfolding and the complete three-value test for reset DAGs.
The native checker evaluates the shared graph; it never computes this tree. -/

@[expose] public section

namespace KFOL.Circuit

universe u v w

/- Exponential unfolding is a proof construction, separate from the original
shared graph and its independent cache evaluator. -/
theorem Equation.unfold_some {σ : ℕ → Type u} {Var : Type v} (equation : Equation σ Var)
    (hwf : equation.WellFormed) :
    ∃ left right : Equational.Term σ Var, equation.unfold = some (left, right) := by
  let _ := Equational.termStructure σ Var
  exact equation.eval_some_of_wellFormed hwf FirstOrder.Language.Term.var

theorem Equation.eval_of_unfold {σ : ℕ → Type u} {Var : Type v} {M : Type w}
    [(Equational.language σ).Structure M] (equation : Equation σ Var)
    (left right : Equational.Term σ Var) (hunfold : equation.unfold = some (left, right))
    (valuation : Var → M) :
    equation.eval valuation = some (left.realize valuation, right.realize valuation) := by
  let _ := Equational.termStructure σ Var
  have hm := equation.eval_map (fun t : Equational.Term σ Var => t.realize valuation)
    (fun {_} _ _ => rfl) FirstOrder.Language.Term.var
  change equation.eval valuation =
    Option.map (fun p : Equational.Term σ Var × Equational.Term σ Var =>
      (p.1.realize valuation, p.2.realize valuation)) equation.unfold at hm
  rw [hunfold] at hm
  exact hm

/- Acyclicity and cache semantics connect the graph to its unfolded terms;
this is not a definition of graph validity by an unrelated certificate. -/
theorem Equation.holds_iff_unfold {σ : ℕ → Type u} {Var : Type v} {M : Type w}
    [(Equational.language σ).Structure M] (equation : Equation σ Var)
    (left right : Equational.Term σ Var) (hunfold : equation.unfold = some (left, right)) :
    equation.Holds M ↔ equation.WellFormed ∧
      ∀ valuation : Var → M, left.realize valuation = right.realize valuation := by
  constructor
  · rintro ⟨hwf, hv⟩
    refine ⟨hwf, fun valuation => ?_⟩
    obtain ⟨value, he⟩ := hv valuation
    have hp := Option.some.inj ((equation.eval_of_unfold left right hunfold valuation).symm.trans he)
    exact (congrArg Prod.fst hp).trans (congrArg Prod.snd hp).symm
  · rintro ⟨hwf, hv⟩
    refine ⟨hwf, fun valuation => ⟨right.realize valuation, ?_⟩⟩
    rw [equation.eval_of_unfold left right hunfold valuation, hv]

/- Every original reset DAG, of arbitrary size and sharing, is completely
tested by assignments in the fixed three-element generator. -/
theorem Equation.reset_holds_iff_chain {Role : Type u} {Var : Type v}
    (three : Fin 3 ↪ Role) (equation : Equation Reset.Symbol Var) :
    let _ := Reset.structureOf (WinnerSet.reset (Role := Role))
    equation.Holds (WinnerSet Role) ↔ equation.WellFormed ∧
      ∀ valuation : Var → WinnerSet Role,
        (∀ j, ∃ stage : Fin 3, valuation j = Reset.chainValue three stage) →
        ∃ value, equation.eval valuation = some (value, value) := by
  let _ := Reset.structureOf (WinnerSet.reset (Role := Role))
  constructor
  · rintro ⟨hwf, hv⟩
    exact ⟨hwf, fun valuation _ => hv valuation⟩
  · rintro ⟨hwf, hv⟩
    obtain ⟨left, right, hu⟩ := equation.unfold_some hwf
    apply (equation.holds_iff_unfold left right hu).mpr
    refine ⟨hwf, ?_⟩
    apply (Reset.Term.eval_eq_iff_chain left right three).mpr
    intro valuation hchain
    obtain ⟨value, he⟩ := hv valuation hchain
    have hp := Option.some.inj ((equation.eval_of_unfold left right hu valuation).symm.trans he)
    exact (congrArg Prod.fst hp).trans (congrArg Prod.snd hp).symm

end KFOL.Circuit

namespace KFOL.Circuit

universe u v

private theorem chainValue_injective {Role : Type u} (three : Fin 3 ↪ Role) :
    Function.Injective (Reset.chainValue three) := by
  intro i j he
  have ha : (i ≠ 0 ↔ j ≠ 0) := by
    rw [← Reset.ambiguous_chainValue three i, ← Reset.ambiguous_chainValue three j, he]
  have hm : (i = 2 ↔ j = 2) := by
    rw [← Reset.marker_chainValue three i, ← Reset.marker_chainValue three j, he]
  apply Fin.ext
  omega

/-- The complete model uses exactly the displayed 3x3 reset table; this is
an algebraic result for original cached graphs, not an enumeration bound. -/
theorem Equation.reset_holds_iff_fin_three {Role : Type u} {Var : Type v}
    (three : Fin 3 ↪ Role) (equation : Equation Reset.Symbol Var) :
    let _ := Reset.structureOf (WinnerSet.reset (Role := Role))
    let _ := Reset.structureOf (fun i j : Fin 3 => if j = 0 then 0 else max i j)
    equation.Holds (WinnerSet Role) ↔ equation.Holds (Fin 3) := by
  classical
  let _ := Reset.structureOf (WinnerSet.reset (Role := Role))
  let _ := Reset.structureOf (fun i j : Fin 3 => if j = 0 then 0 else max i j)
  have hmap : ∀ {n} (symbol : Reset.Symbol n) (args : Fin n → Fin 3),
      Reset.chainValue three (FirstOrder.Language.Structure.funMap (L := Equational.language Reset.Symbol) symbol args) =
        FirstOrder.Language.Structure.funMap (L := Equational.language Reset.Symbol) symbol
          (fun i => Reset.chainValue three (args i)) := by
    intro n symbol args
    cases symbol
    exact (Reset.reset_chainValue three _ _).symm
  constructor
  · rintro ⟨hwf, hv⟩
    refine ⟨hwf, fun valuation => ?_⟩
    obtain ⟨left, right, he⟩ := equation.eval_some_of_wellFormed hwf valuation
    obtain ⟨value, hvv⟩ := hv (fun j => Reset.chainValue three (valuation j))
    have hm := equation.eval_map (Reset.chainValue three) hmap valuation
    rw [he] at hm
    have hp := Option.some.inj (hm.symm.trans hvv)
    have heq : left = right := chainValue_injective three
      ((congrArg Prod.fst hp).trans (congrArg Prod.snd hp).symm)
    exact ⟨right, heq ▸ he⟩
  · rintro ⟨hwf, hv⟩
    apply (equation.reset_holds_iff_chain three).mpr
    refine ⟨hwf, fun valuation hchain => ?_⟩
    let stages : Var → Fin 3 := fun j => (hchain j).choose
    have hvalues : valuation = fun j => Reset.chainValue three (stages j) :=
      funext (fun j => (hchain j).choose_spec)
    obtain ⟨value, he⟩ := hv stages
    have hm := equation.eval_map (Reset.chainValue three) hmap stages
    rw [he] at hm
    refine ⟨Reset.chainValue three value, ?_⟩
    rw [hvalues]
    exact hm

end KFOL.Circuit
