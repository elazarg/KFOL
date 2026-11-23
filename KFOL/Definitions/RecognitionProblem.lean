module

public import KFOL.Definitions.CoreNormalForm
public import Complexity.Computability.Complexity.Classes.Space.TQBF.Prenex

/-! # Recognition of core term operations from their normal forms

An instance lists the names of finitely many inputs and a family of guards.
It is a yes-instance when the guards are exactly the prime guards of a core
term operation on inputs with those names. The source problem of the
reduction is truth of closed prenex formulas with a matrix in conjunctive
normal form, `Cslib.Complexity.TQBFCNF`.
-/

@[expose] public section

namespace KFOL.Problems

open Turing.MultiTapeTM Cslib.Logic.PL

/-- The names of the inputs, and guards listed as an observer, a source and
the excluded postings of an owner at an input. Owners are numbered. -/
abbrev GuardList := List ℕ × List ((ℕ × ℕ) × List (ℕ × ℕ))

/-- Names and owners are written in binary. -/
abbrev guardListEncoding : GuardList ↪ List Bool :=
  encPair (encList encNat)
    (encList (encPair (encPair encNat encNat) (encList (encPair encNat encNat))))

/-- A list of postings names a guard. -/
def NamesGuard {K : ℕ} {Var : Type} (name : Var → ℕ) {k : Fin K} {j : Var}
    (l : List (ℕ × ℕ)) (g : Core.Sources.Guard k j) : Prop :=
  ∀ a r, (a, r) ∈ l ↔ ∃ q ∈ g, name q.1.val = a ∧ q.2.val.val = r

/-- Every guard of the family is listed, and every listed entry is one of
its guards. -/
def Presents {K : ℕ} {Var : Type} (name : Var → ℕ)
    (entries : List ((ℕ × ℕ) × List (ℕ × ℕ)))
    (G : ∀ (k : Fin K) (j : Var), Finset (Core.Sources.Guard k j)) : Prop :=
  (∀ k j, ∀ g ∈ G k j, ∃ e ∈ entries, e.1 = (k.val, name j) ∧ NamesGuard name e.2 g) ∧
  ∀ e ∈ entries, ∃ k j, ∃ g ∈ G k j, e.1 = (k.val, name j) ∧ NamesGuard name e.2 g

/-- The lists of prime guards of core term operations with `K` owners. -/
def coreNormalForms {K : ℕ} (three : Fin 3 ↪ Fin K) : Set GuardList :=
  {x | ∃ (Var : Type) (_ : Fintype Var) (name : Var ↪ ℕ) (t : Term (Fin K) Var),
    (∀ a, a ∈ x.1 ↔ ∃ j, name j = a) ∧ t.IsCore ∧
      Presents name x.2 (Core.Sources.normalForm three (fun v => t.eval v))}

end KFOL.Problems
