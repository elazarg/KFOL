module

public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.NodupEquivFin
public import KFOL.Definitions.Reset

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

namespace SupportIndex

/-- A computable dictionary of actual variable labels, retaining no unused
ambient positions. Repetitions of a variable share one dictionary entry. -/
def labels {Var : Type*} [DecidableEq Var] (t : Reset.Term Var) : List Var :=
  (t.guardEntries.map Prod.fst).dedup

/-- Lookup rejects labels outside the dictionary; indices count positions,
independently of the numeric value of a label. -/
def locate {Var : Type*} [DecidableEq Var] (D : List Var) (j : Var) : Option (Fin D.length) :=
  if h : j ∈ D then some ⟨D.idxOf j, List.idxOf_lt_length_iff.mpr h⟩ else none

/-- Compress a set to its membership positions in a dictionary. -/
def compress {Var : Type*} [DecidableEq Var] (D : List Var) (A : Finset Var) :
    Finset (Fin D.length) := Finset.univ.filter (fun i => D.get i ∈ A)

/-- Recover the labels at a set of dictionary positions. -/
def expand {Var : Type*} [DecidableEq Var] (D : List Var) (A : Finset (Fin D.length)) :
    Finset Var := A.image D.get

/-- Compress an output label and its prerequisite set. Unknown output labels
are rejected; coverage of prerequisites is proved for actual extracted entries. -/
def compressEntry {Var : Type*} [DecidableEq Var] (D : List Var) (p : Var × Finset Var) :
    Option (Fin D.length × Finset (Fin D.length)) := do
  let j ← locate D p.1
  return (j, compress D p.2)

end SupportIndex
end KFOL.Algorithms
