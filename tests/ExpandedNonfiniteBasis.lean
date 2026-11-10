module

public import KFOL.Algebra.FullBasis.NonfiniteBasis
public import KFOL.Algebra.TwoPlayers.Algebra

/-! Regressions for owner transport, mixed labels, the two-role boundary,
and identities whose declared arity greatly exceeds their actual support. -/

@[expose] public section
namespace KFOL.Tests.ExpandedNonfiniteBasis
open Equational

@[instance_reducible] private def asymmetric : (language (CoreSymbol (Fin 3))).Structure Bool where
  funMap f args := match f with
    | .choice r => if r = 0 then args 0 else args 1
  RelMap r := nomatch r

attribute [local instance] asymmetric

private def swap01 : Equiv.Perm (Fin 3) := Equiv.swap 0 1

/-- The payload owner is transported inversely, rather than left unchanged. -/
example : Envelope.choice (0 : Fin 3) (some (swap01,true)) (some (swap01,false)) =
    some (swap01,false) := by
  have h : swap01⁻¹ (0 : Fin 3) = 1 := by simp [swap01]
  simp only [Envelope.choice, ite_true, h]
  rfl

example : Envelope.choice (0 : Fin 3) (some (1,true)) (some (swap01,false)) = none := by
  have h : (1 : Equiv.Perm (Fin 3)) ≠ swap01 := by
    intro equal
    have := congrArg (fun p => p 0) equal
    simp [swap01] at this
  simp [Envelope.choice, h]

example (p q : Equiv.Perm (Fin 3)) (x : Envelope.Carrier (Fin 3) Bool) :
    Envelope.rename p (Envelope.rename q x) = Envelope.rename (p * q) x := by
  cases x with
  | none => rfl
  | some pair => simp [Envelope.rename, mul_assoc]

/-- At two roles a named winner can occur in an idempotent term. The purity
hypothesis behind the envelope transfer really requires three roles. -/
theorem two_role_neutral (A : WinnerSet (Fin 2)) :
    WinnerSet.choice 0 A (WinnerSet.singleton 1) = A := by
  obtain ⟨i,rfl⟩ := TwoPlayers.value_surjective (Equiv.refl (Fin 2)) A
  change WinnerSet.choice ((Equiv.refl (Fin 2)) 0)
    (TwoPlayers.value (Equiv.refl (Fin 2)) i) (TwoPlayers.value (Equiv.refl (Fin 2)) 0) = _
  rw [TwoPlayers.choice_top]
  simp

example : let _ := coreStructure (Fin 2)
    Envelope.eval (fun _ : Fin 1 => some (1,WinnerSet.singleton (0 : Fin 2)))
      (.choice (0 : Fin 2) (.var 0) (.winner 1)) = none := rfl

private def paddedCommutativity : Identity (FullSymbol (Fin 3)) :=
  ⟨100, Full.encode (.choice 0 (.var 0) (.var 1)),
    Full.encode (.choice 0 (.var 1) (.var 0))⟩

example : paddedCommutativity.variableCount = 2 := by decide

/-- The countermodel theorem handles a two-variable identity declared at
arity 100, not just identities whose arity field is at most two. -/
example : ∃ (B : Type) (str : (language (FullSymbol (Fin 3))).Structure B),
    Nonempty B ∧ Finite B ∧ @Identity.Holds _ paddedCommutativity B str ∧
      (let _ := fullStructure (Fin 3)
       ¬@InVariety _ (WinnerSet (Fin 3)) B inferInstance str) := by
  let _ := fullStructure (Fin 3)
  obtain ⟨B,str,_,hne,hf,small,_,hnot,_⟩ :=
    FullBasis.finite_countermodels (Function.Embedding.refl (Fin 3)) 2
  refine ⟨B,str,hne,hf,small paddedCommutativity (by decide) ?_,hnot⟩
  change ∀ v : Fin 100 → WinnerSet (Fin 3),
    WinnerSet.choice 0 (v 0) (v 1) = WinnerSet.choice 0 (v 1) (v 0)
  intro v
  exact WinnerSet.choice_comm (v 0) (v 1) 0

end KFOL.Tests.ExpandedNonfiniteBasis
