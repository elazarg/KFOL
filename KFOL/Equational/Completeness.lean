module

public import KFOL.Equational.Preservation

/-!
# Completeness of equational logic

The independent derivation relation is quotiented on the term algebra.
Mathlib's quotient operations make this a model of the hypotheses. Evaluating
at the canonical variables then reflects equality back to derivability. No
HSP representation theorem is assumed or claimed by this construction.
-/

@[expose] public section

namespace KFOL.Equational

universe u v w

open FirstOrder

variable {σ : ℕ → Type u}

/-- Interpreting a term in the syntactic algebra is structural substitution. -/
theorem realize_termStructure {Var : Type v} {Var' : Type w} (t : Term σ Var)
    (replacement : Var → Term σ Var') :
    letI := termStructure σ Var'
    t.realize replacement = t.subst replacement := by
  let _ := termStructure σ Var'
  induction t with
  | var => rfl
  | func f args ih =>
    change Language.Term.func f (fun i => (args i).realize replacement) = _
    simp only [Language.Term.subst, ih]

/-- The quotient by derivability satisfies every hypothesis at every valuation. -/
theorem quotient_models (T : Theory σ) (Var : Type v) :
    letI := termPrestructure T Var
    Models T (Quotient (derivationSetoid T Var)) := by
  let _ := termPrestructure T Var
  change Models T (Quotient (derivationSetoid T Var))
  intro e he v
  let w : Fin e.arity → Term σ Var := fun i => (v i).out
  have hv : (fun i => (⟦w i⟧ : Quotient (derivationSetoid T Var))) = v :=
    funext (fun i => Quotient.out_eq (v i))
  rw [← hv, Language.Term.realize_quotient_mk', Language.Term.realize_quotient_mk']
  rw [realize_termStructure, realize_termStructure]
  exact Quotient.sound (Derives.of_mem e he w)

/-- Semantic validity in all nonempty algebras implies derivability. The free
model lies in the maximum of the signature and variable universes. -/
theorem derives_of_valid_in_models {Var : Type v} (T : Theory σ) (s t : Term σ Var)
    (h : ∀ (M : Type (max u v)) [_str : (language σ).Structure M],
      Nonempty M → Models T M → ∀ valuation : Var → M, s.realize valuation = t.realize valuation) :
    Derives T s t := by
  let _ := termPrestructure T Var
  let Q := Quotient (derivationSetoid T Var)
  have hQ := h Q ⟨⟦s⟧⟩ (quotient_models T Var) (fun x => ⟦Language.Term.var x⟧)
  have canonical (r : Term σ Var) :
      r.realize (fun x => (⟦Language.Term.var x⟧ : Q)) = ⟦r⟧ := by
    rw [Language.Term.realize_quotient_mk', realize_termStructure, subst_var]
  rw [canonical, canonical] at hQ
  exact Quotient.exact hQ

/-- Soundness and completeness, with syntax and semantics defined independently. -/
theorem derives_iff_valid_in_models {Var : Type v} (T : Theory σ) (s t : Term σ Var) :
    Derives T s t ↔
      ∀ (M : Type (max u v)) [_str : (language σ).Structure M],
        Nonempty M → Models T M → ∀ valuation : Var → M,
          s.realize valuation = t.realize valuation :=
  ⟨fun h M _ _ hM => h.sound M hM, derives_of_valid_in_models T s t⟩

/-- A semantic basis argument can be converted into equational derivability.
Testing models in the signature universe suffices for finite-variable identities;
soundness then yields the consequence in every carrier universe. -/
theorem isBasis_iff_models {A : Type w} [(language σ).Structure A] (T : Theory σ) :
    IsBasis A T ↔ Models T A ∧
      ∀ (M : Type u) [_str : (language σ).Structure M] [Nonempty M],
        Models T M → InVariety σ A M := by
  constructor
  · intro h
    exact ⟨h.models, fun _ _ _ hM => h.inVariety hM⟩
  · rintro ⟨hA, hmodels⟩ e
    constructor
    · intro he
      apply derives_of_valid_in_models T e.lhs e.rhs
      intro M str hn hM v
      let _ := hn
      exact (hmodels M hM).2 e he v
    · intro he
      exact he.sound A hA

end KFOL.Equational
