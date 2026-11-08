module

public import KFOL.Algebra

/-! Boundary cases for equational infrastructure: structure values on one
carrier, support rather than declared arity, nullary axioms and empty closures. -/

@[expose] public section

namespace KFOLTest.Equational

open KFOL.Equational FirstOrder

@[instance_reducible] private def projection (right : Bool) :
    (language (CoreSymbol Unit)).Structure Bool where
  funMap f args := match f with
    | .choice _ => args (if right then 1 else 0)
  RelMap r := nomatch r

private def leftLaw : Identity (CoreSymbol Unit) :=
  ⟨2, .func (.choice ()) (fun i => .var i), .var 0⟩

-- Same carrier, same signature, different operations: no global instance hides
-- which algebra satisfies the equation.
example : @Identity.Holds _ leftLaw Bool (projection false) := by
  intro v
  rfl

example : ¬@Identity.Holds _ leftLaw Bool (projection true) := by
  intro h
  have bad := h (fun i => i.val == 1)
  change true = false at bad
  cases bad

private def padded : Identity (CoreSymbol Unit) := ⟨100, .var 99, .var 99⟩

example : padded.variableCount = 1 := by decide

-- Soundness detects non-derivability even though the target equation is valid
-- in another algebra with exactly the same underlying type.
example : ¬Derives (∅ : Theory (CoreSymbol Unit)) leftLaw.lhs leftLaw.rhs := by
  intro h
  let _ := projection true
  have valid : leftLaw.Holds Bool := h.sound Bool (fun _ he => False.elim he)
  have bad := valid (fun i => i.val == 1)
  change true = false at bad
  cases bad

private def ground : Identity (FullSymbol (Fin 2)) :=
  ⟨0, .func (.winner 0) Fin.elim0, .func (.winner 1) Fin.elim0⟩

example : ground.variableCount = 0 := by decide

-- The quotient construction handles an axiom with no variable valuations to
-- choose, and builds the model using the actual constant operations.
example :
    let _ := termPrestructure ({ground} : Theory (FullSymbol (Fin 2))) (Fin 0)
    ground.Holds
      (Quotient (derivationSetoid ({ground} : Theory (FullSymbol (Fin 2))) (Fin 0))) := by
  let _ := termPrestructure ({ground} : Theory (FullSymbol (Fin 2))) (Fin 0)
  exact quotient_models ({ground} : Theory (FullSymbol (Fin 2))) (Fin 0) ground rfl

-- A constant-free core has no ground terms, even though its algebras may be nonempty.
example : IsEmpty (Term (CoreSymbol (Fin 2)) (Fin 0)) := by
  refine ⟨fun t => ?_⟩
  obtain ⟨i, _⟩ := (Core.isCore_decode t).vars_nonempty
  exact Fin.elim0 i

example :
    let _ := coreStructure (Fin 2)
    IsEmpty (Language.Substructure.closure (language (CoreSymbol (Fin 2)))
      (∅ : Set (KFOL.WinnerSet (Fin 2)))) := by
  let _ := coreStructure (Fin 2)
  refine ⟨fun x => ?_⟩
  obtain ⟨t, _⟩ := Language.Substructure.mem_closure_iff_exists_term.mp x.property
  have noTerm : ∀ (r : Term (CoreSymbol (Fin 2)) (∅ : Set (KFOL.WinnerSet (Fin 2)))), False := by
    intro r
    obtain ⟨i, _⟩ := (Core.isCore_decode r).vars_nonempty
    exact i.property
  exact noTerm t

-- Adding the public constants changes the zero-generator boundary.
example :
    let _ := fullStructure (Fin 2)
    Nonempty (Language.Substructure.closure (language (FullSymbol (Fin 2)))
      (∅ : Set (KFOL.WinnerSet (Fin 2)))) := by
  let _ := fullStructure (Fin 2)
  let S := Language.Substructure.closure (language (FullSymbol (Fin 2)))
    (∅ : Set (KFOL.WinnerSet (Fin 2)))
  exact ⟨⟨KFOL.WinnerSet.singleton 0, S.fun_mem (.winner 0) Fin.elim0 (fun i => Fin.elim0 i)⟩⟩

-- An empty product is the trivial algebra and satisfies every identity.
example (e : Identity (CoreSymbol Unit)) :
    let _ := projection false
    let _ := productStructure (σ := CoreSymbol Unit) (fun _ : Fin 0 => Bool)
    e.Holds (Fin 0 → Bool) := by
  let _ := projection false
  exact e.holds_product (fun _ : Fin 0 => Bool) (fun i => Fin.elim0 i)

end KFOLTest.Equational
