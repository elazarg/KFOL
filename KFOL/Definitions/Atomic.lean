module

public import KFOL.Definitions.Public

/-! # Atomic behavior and the independently specified S2 function class -/

@[expose] public section

namespace KFOL

universe u v w

namespace Atomic

/-- Three values have a repeated entry. -/
def Repeat {A : Type u} (a b c : A) : Prop := a = b ∨ a = c ∨ b = c

/-- The output lies in one fixed pair, allowing the two values to coincide. -/
def AtMostTwo {Input : Type u} {Output : Type v} (f : Input → Output) : Prop :=
  ∃ a b, ∀ x, f x = a ∨ f x = b

/-- One input coordinate, followed by an arbitrary unary map. -/
def EssentiallyUnary {Index : Type u} {Input : Type v} {Output : Type w}
    (f : (Index → Input) → Output) : Prop :=
  ∃ i : Index, ∃ g : Input → Output, ∀ x, f x = g (x i)

/-- Independent relation-preservation semantics on three valuations. -/
def PreservesRepeat {Index : Type u} {Input : Type v} {Output : Type w}
    (f : (Index → Input) → Output) : Prop :=
  ∀ x y z, (∀ i, Repeat (x i) (y i) (z i)) → Repeat (f x) (f y) (f z)

end Atomic

namespace Term

/-- The full-language term always returns an atom on all atomic valuations. -/
def AtomPreserving {Role : Type u} {Var : Type v} (t : Term Role Var) : Prop :=
  ∀ v : Var → Role, ∃ r, t.eval (fun x => WinnerSet.singleton (v x)) = WinnerSet.singleton r

/-- Exact realization of an atomic function by the independent evaluator. -/
def AtomicRealizes {Role : Type u} {Var : Type v} (t : Term Role Var) (f : (Var → Role) → Role) : Prop :=
  ∀ v, t.eval (fun x => WinnerSet.singleton (v x)) = WinnerSet.singleton (f v)

end Term

end KFOL
