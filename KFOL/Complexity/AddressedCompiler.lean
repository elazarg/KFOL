module

public import KFOL.Complexity.AddressedPoint
public import KFOL.Complexity.AddressedPreprocessing
public import KFOL.Complexity.AddressedIncidence
public import KFOL.Core.ExplicitTableReduction

/-! # The multitape compiler from quantified CNF to a listed operation table

The output gives the arity in unary followed by the winner list at each
tuple of nonempty menus in the ordering of `AddressTableOutput.tuple`.
-/

@[expose] public section
namespace KFOL.Complexity.AddressedCompiler

open Turing.MultiTapeTM ComputableInPolyTime Bichain.Quantified Recognition.Lists
open Core.AddressedQuantified AddressedIncidence AddressedPreprocessing

abbrev RawTable := ℕ × List (List ℕ)
abbrev rawEncoding := encPair encUnary (encList AddressedEnvelope.namesEncoding)

def layout (u : Input) : AddressedPoint.Layout :=
  let f := ThreeCNF.fromTQBFCNF u
  let old := (formulaOf u).n
  (addresses (ThreeCNF.translate (formulaOf u)).n f.n f.cls.length,
    rowData old f.n (numCls f) true, rowData old f.n (numCls f) false)

def labels (u : Input) : ℕ := labelBound (ThreeCNF.fromTQBFCNF u)

def output (k a b c : ℕ) (u : Input) : RawTable :=
  (AddressTableOutput.arity 14 (labels u),
    AddressTableOutput.table k 14 labels (fun x v => AddressedPoint.point k a b c (layout x) v) u)

theorem labels_poly : ComputableInPolyTime labels Cslib.Complexity.encPrenexCNF encUnary := by
  have stages := counts_poly.snd'.snd'
  have cls := clauses_poly
  unfold labels labelBound
  fun_prop

theorem layout_poly : ComputableInPolyTime layout Cslib.Complexity.encPrenexCNF AddressedPoint.layoutEncoding := by
  have old := counts_poly.fst'
  have split := counts_poly.snd'.fst'
  have final := counts_poly.snd'.snd'
  have rows := numeric_clauses_poly
  have m : ComputableInPolyTime (fun u : Input => (ThreeCNF.fromTQBFCNF u).cls.length)
      Cslib.Complexity.encPrenexCNF encUnary := by
    have := clauses_poly
    fun_prop
  exact (addresses_poly split final m).prod
    ((rowData_poly old final rows (const true)).prod (rowData_poly old final rows (const false)))

/-- Output all entries of the addressed operation in polynomial time
including the actual enumeration, for each fixed set of named owners. -/
theorem output_poly (k a b c : ℕ) : ComputableInPolyTime (output k a b c)
    Cslib.Complexity.encPrenexCNF rawEncoding :=
  (AddressTableOutput.arity_poly 14 labels_poly).prod
    (AddressedPoint.table_poly k a b c 14 labels_poly layout_poly)

end KFOL.Complexity.AddressedCompiler
