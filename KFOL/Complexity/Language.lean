module

public import Complexitylib.Classes.P.Cobham
public import Complexitylib.Classes.P.Cobham.Internal.StringOps

/-! # Imported machine complexity interface

`Complexity.Cobham.FPn` is ComplexityLib's fixed-arity word interface. It
requires a genuine unary `Complexity.FP` machine on its canonical tuple code;
`FP` quantifies over a deterministic Turing machine, a time bound and a
polynomial asymptotic bound. We reuse these definitions without redefining
polynomial time through our own checker or a supplied certificate.

This facade is confined to the complexity branch. Mathematical word and
guard definitions live in `KFOL.Definitions.Algorithms` and do not import it.
-/
