module

public import KFOL.Definitions.Reset

/-! Native acyclic graph syntax, independent validity, shared-cache semantics
and graph builders. Proof-level unfolding is separate from native evaluation. -/

@[expose] public section

namespace KFOL.Circuit

universe u v w

/- Nodes contain either an original input name or one original operation
with its correctly typed finite vector of prior-node references. -/
inductive Gate (σ : ℕ → Type u) (Var : Type v) where
  | input : Var → Gate σ Var
  | func {n : ℕ} : σ n → (Fin n → ℕ) → Gate σ Var

namespace Gate

variable {σ : ℕ → Type u} {Var : Type v} {M : Type w}

def references : Gate σ Var → List ℕ
  | .input _ => []
  | .func _ refs => List.ofFn refs

/- Strictly earlier references, independent of a circuit's evaluator. -/
def ValidAt (position : ℕ) : Gate σ Var → Prop
  | .input _ => True
  | .func _ refs => ∀ i, refs i < position

instance (position : ℕ) (gate : Gate σ Var) : Decidable (gate.ValidAt position) := by
  cases gate <;> dsimp [ValidAt] <;> infer_instance

/- Reject out-of-cache references before indexing; no default value or
numeric-maximum iteration is part of the semantics. -/
def eval [(Equational.language σ).Structure M] (valuation : Var → M) (cache : List M) : Gate σ Var → Option M
  | .input j => some (valuation j)
  | .func f refs =>
    if h : ∀ i, refs i < cache.length then
      some (FirstOrder.Language.Structure.funMap (L := Equational.language σ) f (fun i => cache[refs i]'(h i)))
    else none

end Gate

/- Topological validation from a current prefix length. This definition
inspects the finite graph and does not mention valuations or evaluation. -/
def ValidFrom {σ : ℕ → Type u} {Var : Type v} : ℕ → List (Gate σ Var) → Prop
  | _, [] => True
  | position, gate :: gates => gate.ValidAt position ∧ ValidFrom (position + 1) gates

instance {σ : ℕ → Type u} {Var : Type v} (position : ℕ) (gates : List (Gate σ Var)) :
    Decidable (ValidFrom position gates) := by
  induction gates generalizing position with
  | nil => exact isTrue trivial
  | cons gate gates ih => dsimp [ValidFrom]; exact instDecidableAnd

def runFrom {σ : ℕ → Type u} {Var : Type v} {M : Type w}
    [(Equational.language σ).Structure M] (valuation : Var → M) :
    List (Gate σ Var) → List M → Option (List M)
  | [], cache => some cache
  | gate :: gates, cache => do
    let value ← gate.eval valuation cache
    runFrom valuation gates (cache ++ [value])

/- One shared DAG, with two designated outputs; the graph is not duplicated
between the sides of an equation. -/
structure Equation (σ : ℕ → Type u) (Var : Type v) where
  gates : List (Gate σ Var)
  left : ℕ
  right : ℕ

namespace Equation

variable {σ : ℕ → Type u} {Var : Type v} {M : Type w}

def WellFormed (equation : Equation σ Var) : Prop :=
  ValidFrom 0 equation.gates ∧ equation.left < equation.gates.length ∧ equation.right < equation.gates.length

instance (equation : Equation σ Var) : Decidable equation.WellFormed := by
  unfold WellFormed
  infer_instance

def eval [(Equational.language σ).Structure M] (equation : Equation σ Var)
    (valuation : Var → M) : Option (M × M) := do
  let cache ← runFrom valuation equation.gates []
  let left ← cache[equation.left]?
  let right ← cache[equation.right]?
  return (left, right)

/- Equality concerns actual well-formed acyclic graphs. Invalid nodes or
outputs cannot make two absent evaluations count as an equation. -/
def Holds (equation : Equation σ Var) (M : Type w) [(Equational.language σ).Structure M] : Prop :=
  equation.WellFormed ∧ ∀ valuation : Var → M, ∃ value : M, equation.eval valuation = some (value, value)

end Equation

/- The fixed argument order of the external vector view is numeric Fin
order, inherited from List.ofFn, rather than any Fintype numbering. -/
end KFOL.Circuit

namespace KFOL.Circuit

universe u v w

end KFOL.Circuit

namespace KFOL.Circuit

universe u v w w'

/- A structure homomorphism acts on the actual cache, preserving all refs. -/
end KFOL.Circuit
namespace KFOL.Circuit

universe u v w

structure BuildResult (σ : ℕ → Type u) (Var : Type v) where
  gates : List (Gate σ Var)
  output : ℕ

def emit {σ : ℕ → Type u} {Var : Type v} (gates : List (Gate σ Var)) (gate : Gate σ Var) : BuildResult σ Var :=
  ⟨gates ++ [gate], gates.length⟩

def Gate.reset {Var : Type v} (left right : ℕ) : Gate Reset.Symbol Var :=
  .func .reset (fun i => if i = 0 then left else right)

/- Right combs keep their accumulated continuation as a single reference. -/
def buildRightComb {Var : Type v} : List ℕ → ℕ → List (Gate Reset.Symbol Var) → BuildResult Reset.Symbol Var
  | [], base, gates => ⟨gates, base⟩
  | head :: refs, base, gates =>
      let tail := buildRightComb refs base gates
      emit tail.gates (Gate.reset head tail.output)

end KFOL.Circuit

namespace KFOL.Circuit

universe v w

/- Reset gate semantics uses safe optional cache reads; two successful
reads imply its independent strict-prefix check. -/
end KFOL.Circuit

namespace KFOL.Circuit

universe v w

/- One clause stage. Every retained-literal gate points to the same previous
CNF output index, rather than copying that output's subgraph. -/
def buildClause {Var : Type v} : List ℕ → ℕ → ℕ → List (Gate Reset.Symbol Var) → BuildResult Reset.Symbol Var
  | [], _, root, gates => ⟨gates, root⟩
  | head :: refs, previous, root, gates =>
      let retained := emit gates (Gate.reset previous head)
      let tail := buildClause refs previous root retained.gates
      emit tail.gates (Gate.reset retained.output tail.output)

end KFOL.Circuit

namespace KFOL.Circuit

universe v w

/- Successive clauses retain exactly one reference to each previous output.
An empty clause returns the original root reference without emitting gates. -/
def buildCNF {Var : Type v} : List (List ℕ) → ℕ → ℕ → List (Gate Reset.Symbol Var) → BuildResult Reset.Symbol Var
  | [], previous, _, gates => ⟨gates, previous⟩
  | clause :: clauses, previous, root, gates =>
      let head := buildClause clause previous root gates
      buildCNF clauses head.output root head.gates

end KFOL.Circuit

namespace KFOL.Circuit

universe v w

/- Right comb of the inconsistent-rail branches `(c reset p) reset n`.
The cached marker and both literal inputs are reused by index. -/
def buildConsistency {Var : Type v} : List (ℕ × ℕ) → ℕ → ℕ →
    List (Gate Reset.Symbol Var) → BuildResult Reset.Symbol Var
  | [], _, base, gates => ⟨gates, base⟩
  | pair :: pairs, marker, base, gates =>
      let positive := emit gates (Gate.reset marker pair.1)
      let negative := emit positive.gates (Gate.reset positive.output pair.2)
      let tail := buildConsistency pairs marker base negative.gates
      emit tail.gates (Gate.reset negative.output tail.output)

end KFOL.Circuit

namespace KFOL.Circuit

universe v

def operationCount {σ : ℕ → Type*} {Var : Type v} (gates : List (Gate σ Var)) : ℕ :=
  gates.countP (fun gate => match gate with | .input _ => false | .func _ _ => true)

end KFOL.Circuit
namespace KFOL.Circuit

universe u v w

/- Exponential unfolding is a proof construction, separate from the original
shared graph and its independent cache evaluator. -/
def Equation.unfold {σ : ℕ → Type u} {Var : Type v} (equation : Equation σ Var) :
    Option (Equational.Term σ Var × Equational.Term σ Var) :=
  let _ := Equational.termStructure σ Var
  equation.eval FirstOrder.Language.Term.var

end KFOL.Circuit
namespace KFOL.Circuit

universe u v w

/- H(root,left,left) uses the SAME left ref twice. It does not copy a
previously constructed subgraph or expand its shared continuation. -/
def Gate.liftReset {σ : ℕ → Type u} {Var : Type v} (operation : σ 3) : Gate Reset.Symbol Var → Gate σ Var
  | .input j => .input j
  | .func .reset refs => .func operation (fun i => if i = 0 then refs 1 else refs 0)

def Equation.liftReset {σ : ℕ → Type u} {Var : Type v} (operation : σ 3) (equation : Equation Reset.Symbol Var) :
    Equation σ Var := ⟨equation.gates.map (Gate.liftReset operation), equation.left, equation.right⟩

end KFOL.Circuit

namespace KFOL.Circuit

universe u v w

namespace ResetCNF

/- The original linear reset DAG becomes a pure single-H DAG by repeated
EDGES; its actual evaluation is still a complete CNF reduction. -/
end ResetCNF
end KFOL.Circuit

namespace KFOL.Circuit

universe u v

def edgeCount {σ : ℕ → Type u} {Var : Type v} (gates : List (Gate σ Var)) : ℕ :=
  (gates.map (fun gate => gate.references.length)).sum

end KFOL.Circuit
