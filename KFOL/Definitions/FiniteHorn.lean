module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card

/-! # Finite positive Horn systems

The rules mention only facts. Saturation is bounded by the size of the fact
type, independently of any subsequent semantic interpretation.
-/

@[expose] public section

namespace KFOL.FiniteHorn

universe u

/-- Seed facts and rules with two premises. -/
structure System (Fact : Type u) where
  seed : Fact → Prop
  rule : Fact → Fact → Fact → Prop

/-- Ordinary finite derivability in the specified Horn system. -/
inductive Derives {Fact : Type u} (S : System Fact) : Fact → Prop
  | seed {f} : S.seed f → Derives S f
  | step {a b c} : S.rule a b c → Derives S a → Derives S b → Derives S c

/-- Add all seeds and all conclusions whose two premises are present. -/
noncomputable def step {Fact : Type u} [Fintype Fact] (S : System Fact)
    (D : Finset Fact) : Finset Fact := by
  classical
  exact Finset.univ.filter fun c =>
    c ∈ D ∨ S.seed c ∨ ∃ a ∈ D, ∃ b ∈ D, S.rule a b c

/-- Synchronous rounds, starting with no facts. -/
noncomputable def stage {Fact : Type u} [Fintype Fact] (S : System Fact) : ℕ → Finset Fact
  | 0 => ∅
  | n + 1 => step S (stage S n)

/-- Exactly as many rounds as there are possible facts. -/
@[irreducible] noncomputable def saturate {Fact : Type u} [Fintype Fact]
    (S : System Fact) : Finset Fact :=
  stage S (Fintype.card Fact)

end KFOL.FiniteHorn
