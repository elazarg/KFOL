module

public import KFOL.Definitions.Equational

/-! # Sound equational derivations and finite variable bounds -/

@[expose] public section

namespace KFOL.Equational

universe u v w

variable {σ : ℕ → Type u} {T U : Theory σ}

/-- Derivation remains valid in every algebra satisfying its axioms. -/
theorem Derives.sound {Var : Type v} {s t : Term σ Var} (h : Derives T s t)
    (M : Type w) [(language σ).Structure M] (hM : Models T M) :
    ∀ valuation : Var → M, s.realize valuation = t.realize valuation := by
  induction h with
  | of_mem e he replacement =>
    intro v
    simpa only [FirstOrder.Language.Term.realize_subst] using
      hM e he (fun x => (replacement x).realize v)
  | refl => exact fun _ => rfl
  | symm h ih => exact fun v => (ih v).symm
  | trans h₁ h₂ ih₁ ih₂ => exact fun v => (ih₁ v).trans (ih₂ v)
  | func f s t h ih =>
    intro v
    change FirstOrder.Language.Structure.funMap (L := language σ) f (fun i => (s i).realize v) =
      FirstOrder.Language.Structure.funMap (L := language σ) f (fun i => (t i).realize v)
    exact congrArg _ (funext (fun i => ih i v))
  | subst h replacement ih =>
    intro v
    simpa only [FirstOrder.Language.Term.realize_subst] using
      ih (fun x => (replacement x).realize v)

/-- Adding axioms preserves every derivation. -/
theorem Derives.mono {Var : Type v} {s t : Term σ Var} (h : Derives T s t)
    (hTU : T ⊆ U) : Derives U s t := by
  induction h with
  | of_mem e he replacement => exact .of_mem e (hTU he) replacement
  | refl t => exact .refl t
  | symm h ih => exact .symm ih
  | trans h₁ h₂ ih₁ ih₂ => exact .trans ih₁ ih₂
  | func f s t h ih => exact .func f s t ih
  | subst h replacement ih => exact .subst ih replacement

/-- A finite family has one common finite support bound. The empty theory has
bound zero, and padded variable declarations do not change the measure. -/
theorem finite_hasVariableBound (T : Theory σ) (hT : T.Finite) :
    ∃ n : ℕ, HasVariableBound T n := by
  classical
  refine ⟨hT.toFinset.sup Identity.variableCount, ?_⟩
  intro e he
  exact Finset.le_sup (f := Identity.variableCount) (hT.mem_toFinset.mpr he)

/-- Substitution by variables is the identity on generic terms. -/
theorem subst_var {Var : Type v} (t : Term σ Var) : t.subst (.var) = t := by
  induction t with
  | var => rfl
  | func f args ih => simp only [FirstOrder.Language.Term.subst, ih]

/-- A genuine basis is sound in its generator. -/
theorem IsBasis.models {A : Type w} [(language σ).Structure A] (h : IsBasis A T) : Models T A := by
  intro e he
  apply (h e).mpr
  have hd := Derives.of_mem (T := T) e he (fun i => (.var i : Term σ (Fin e.arity)))
  simpa only [subst_var] using hd

/-- Any nonempty model of a basis belongs to the generator's equational variety. -/
theorem IsBasis.inVariety {A : Type w} {B : Type v}
    [(language σ).Structure A] [(language σ).Structure B] [Nonempty B]
    (h : IsBasis A T) (hB : Models T B) : InVariety σ A B := by
  refine ⟨inferInstance, ?_⟩
  intro e he
  exact ((h e).mp he).sound B hB

end KFOL.Equational
