module

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration

/-! # Imported machine complexity interface

The successor ComplexityLib uses `Turing.MultiTapeTM.ComputableInPolyTime`
with explicit injective input and output encodings. The predicate quantifies
over a deterministic multitape Turing machine and a polynomial clock. Its
typed composition and iteration theorems charge encoded state and output.
We reuse that definition without a project-specific notion of efficiency.

This facade is confined to the complexity branch. Mathematical word and
guard definitions live in the mathlib-only definition modules. The paper's
two-bit framing is independent of the native machine tuple encoding.
-/
