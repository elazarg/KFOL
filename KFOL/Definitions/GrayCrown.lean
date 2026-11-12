module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Nodup
public import Mathlib.Logic.Equiv.Fin.Rotate

/-! # Paired transversals and cyclic binary Gray codes

The reflected list enumerates all Boolean words. A cyclic Gray code gives a
crown whose lower sets choose one element from every coordinate pair.
-/

@[expose] public section
namespace KFOL.Core.GrayCrown

abbrev Word (d : ℕ) := Fin d → Bool

/-- Two words differ at exactly one coordinate. -/
def Adjacent {d : ℕ} (x y : Word d) : Prop :=
  ∃ j, x j ≠ y j ∧ ∀ k, k ≠ j → x k = y k

/-- The transversal selecting the bit of each coordinate. -/
def lowerOf {d : ℕ} (x : Word d) : Finset (Fin d × Bool) :=
  Finset.univ.image (fun j => (j, x j))

/-- The union of the transversals at the ends of one Gray edge. -/
def upperOf {d : ℕ} (x y : Word d) : Finset (Fin d × Bool) :=
  lowerOf x ∪ lowerOf y

/-- Binary reflected Gray order, with a new leading coordinate at each stage. -/
def reflected : (d : ℕ) → List (Word d)
  | 0 => [Fin.elim0]
  | d + 1 => (reflected d).map (Fin.cons false) ++
      (reflected d).reverse.map (Fin.cons true)

/-- A complete cyclic Gray enumeration with the standard cyclic successor. -/
structure Code (d : ℕ) where
  word : Fin (2 ^ d) → Word d
  bijective : Function.Bijective word
  adjacent : ∀ i, Adjacent (word i) (word (finRotate _ i))

namespace Code
variable {d : ℕ}

/-- Lower endpoint indexed by a Gray cycle. -/
def lower (g : Code d) (i : Fin (2 ^ d)) : Finset (Fin d × Bool) :=
  lowerOf (g.word i)

/-- Upper endpoint indexed by a Gray cycle. -/
def upper (g : Code d) (i : Fin (2 ^ d)) : Finset (Fin d × Bool) :=
  upperOf (g.word i) (g.word (finRotate _ i))

end Code
end KFOL.Core.GrayCrown
