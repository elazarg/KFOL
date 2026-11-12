module

public import KFOL.Algebra.TestDomains
public import KFOL.Definitions.Views
public import Mathlib.Data.Fin.VecNotation

/-! # Three observer polynomials and their joint raw output

The output includes each role precisely when that role occurs in its own
observer polynomial. Its definition is independent of term evaluation.
-/

@[expose] public section
namespace KFOL.Core.AtomicAmalgamation

/-- The three explicit observer polynomials in an algebra with union and choices. -/
def observerPolynomials {A : Type*} (join : A → A → A)
    (choose : Fin 3 → A → A → A) (v : Fin 3 → A) : Fin 3 → A :=
  let X := v 0
  let Y := v 1
  let Z := v 2
  ![join (join (join Y Z) (choose 1 X Y)) (choose 2 X Z),
    join (join (join X Y) (choose 0 Z X)) (choose 2 Z Y),
    join (join (join X Z) (choose 1 Y X)) (choose 0 Y Z)]

/-- Joint membership prescribed independently by the three observer polynomials. -/
noncomputable def raw (v : Fin 3 → WinnerSet (Fin 3)) : Set (Fin 3) :=
  {r | r ∈ (observerPolynomials WinnerSet.union WinnerSet.choice v r).val}

/-- Actual core syntax for each observer polynomial, using derived core union. -/
def observerTerm (r : Fin 3) : Term (Fin 3) (Fin 3) :=
  observerPolynomials (Term.unionTerm (Function.Embedding.refl _)) Term.choice Term.var r

/-- Three atomic rows witnessing the incompatibility of the observer requirements. -/
def rows : Fin 3 → Fin 3 → Fin 3 := ![![0, 1, 2], ![0, 2, 1], ![1, 2, 0]]

/-- Singleton-valued input valuations at the three distinguishing rows. -/
def atomicInput (i : Fin 3) : Fin 3 → WinnerSet (Fin 3) :=
  fun j => WinnerSet.singleton (rows i j)

/-- The required output sets at the three distinguishing atomic rows. -/
def atomicOutput : Fin 3 → Set (Fin 3) := ![{1, 2}, {0, 2}, {0, 1}]

end KFOL.Core.AtomicAmalgamation
