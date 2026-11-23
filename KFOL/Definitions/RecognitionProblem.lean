module

public import KFOL.Definitions.CoreNormalForm
public import Complexity.Computability.Complexity.Problems.TQBF
public import Complexity.Computability.Complexity.Problems.SAT
public import Complexity.Computability.Complexity.Classes.Space

/-! # Recognition of core term operations from their normal forms

An instance lists the names of finitely many inputs and a family of guards.
It is a yes-instance when the guards are exactly the prime guards of a core
term operation on inputs with those names. The source problem is truth of
closed prenex formulas with a matrix in conjunctive normal form.
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

/-- The formula `∃ x₁, ∀ y₁, ⋯, ∃ xₙ, ∀ yₙ, ψ` of a list of rounds `(xᵢ, yᵢ)`
and a matrix `ψ` in conjunctive normal form. -/
def prenexFormula (ps : List (ℕ × ℕ)) (ψ : CNF ℕ) : QBF ℕ :=
  ps.foldr (fun p φ => .ex p.1 (.all p.2 φ)) (QBF.ofCNF ψ)

/-- Rounds and matrix with variables written in binary. -/
abbrev prenexEncoding : List (ℕ × ℕ) × CNF ℕ ↪ List Bool :=
  encPair (encList (encPair encNat encNat)) Cslib.Complexity.encCNF

/-- The true closed prenex formulas. This is the set `Cslib.Complexity.TQBFCNF`
with its encoding `Cslib.Complexity.encPrenexCNF`. -/
def prenexTruth : Set (List (ℕ × ℕ) × CNF ℕ) :=
  {x | prenexFormula x.1 x.2 ∈ Cslib.Complexity.TQBF}

end KFOL.Problems
