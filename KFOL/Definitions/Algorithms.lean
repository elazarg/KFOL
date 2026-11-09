module

public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.List.OfFn

/-! # Word representations and algorithms, independent of complexity classes -/

@[expose] public section

namespace KFOL.Algorithms

namespace Bitset

/-- Membership words list positions in increasing index order. -/
def encode {n : ℕ} (A : Finset (Fin n)) : List Bool :=
  List.ofFn (fun i => decide (i ∈ A))

/-- Decode exactly the declared width, rejecting other lengths. -/
def decode (n : ℕ) (word : List Bool) : Option (Finset (Fin n)) :=
  if word.length = n then some (Finset.univ.filter (fun i => word[i.val]?.getD false)) else none

end Bitset

namespace GuardWords

/-- Read an input position, with zero padding outside the word. -/
def readBit (word : List Bool) (i : ℕ) : Bool := word[i]?.getD false

/-- Fold state: remaining ruler, previous flag, left word, right word.
The current position is determined by the ruler's length, never by its value. -/
def subsetStep (r state a b : List Bool) : List Bool :=
  [state.headD false && (!readBit a r.length || readBit b r.length)]

/-- Check one coordinate per ruler bit. The input bit values do not control
the number of iterations. -/
def subsetScan : List Bool → List Bool → List Bool → List Bool
  | [], _, _ => [true]
  | _ :: r, a, b => subsetStep r (subsetScan r a b) a b

/-- The total word-level prerequisite test returns a one-bit flag. Unequal
widths are rejected instead of silently interpreting padding as valid input. -/
def subsetWord (a b : List Bool) : List Bool :=
  [decide (a.length = b.length) && (subsetScan a a b).headD false]

/-- Bundle the word test in the fixed-arity interface used by the machine library. -/
def subsetFn (v : Fin 2 → List Bool) : List Bool := subsetWord (v 0) (v 1)

end GuardWords
end KFOL.Algorithms
