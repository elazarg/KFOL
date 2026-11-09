module

public import KFOL.Complexity.ResetUnionMachines

/-! # Certified sparse-CNF generation of the native reset/union equation -/

@[expose] public section

namespace KFOL.Complexity.ResetUnionReduction

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.Reductions
open KFOL.Complexity.ResetUnionMachines

abbrev literalEncoding := encPair encNat encBool
abbrev clauseEncoding := encList literalEncoding
abbrev cnfEncoding := encList clauseEncoding

@[fun_prop] theorem literalName_polyTime : ComputableInPolyTime ResetUnion.literalName
    literalEncoding encNat := by
  have hi := fst encNat encBool
  have htwice := binary_mul' (const 2) hi
  have hpositive := binary_add.comp (htwice.prod (const 3))
  have hnegative := binary_add.comp (htwice.prod (const 4))
  exact (snd encNat encBool).ite hpositive hnegative

@[fun_prop] theorem literalTerm_polyTime : ComputableInPolyTime ResetUnion.literalTerm
    literalEncoding termEncoding := var_polyTime.comp literalName_polyTime

/-- The support includes one dummy Boolean variable, retains exact mathlib
rightmost deduplication order, and never enumerates up to a numeric label. -/
@[fun_prop] theorem support_polyTime : ComputableInPolyTime ResetUnion.support cnfEncoding (encList encNat) := by
  have hflatten := flatMapWithInput (f := fun (_ : CNF) (clause : Clause) => clause)
    (id' (encIn := cnfEncoding)) (snd cnfEncoding clauseEncoding)
  have hname : ComputableInPolyTime (fun p : CNF × Literal => p.2.1)
      (encPair cnfEncoding literalEncoding) encNat := by fun_prop
  have hnames := mapWithInput (f := fun (_ : CNF) (literal : Literal) => literal.1) hflatten hname
  have h := TermSupport.dedup_polyTime.comp (cons' (const 0) hnames)
  convert h using 1
  funext formula
  simp only [ResetUnion.support, Function.comp_def, List.flatMap_id']

@[fun_prop] theorem baseline_polyTime : ComputableInPolyTime ResetUnion.baseline cnfEncoding termEncoding := by
  have hi := snd cnfEncoding encNat
  have hpositive := literalTerm_polyTime.comp (hi.prod (const true))
  have hnegative := literalTerm_polyTime.comp (hi.prod (const false))
  have hpair := cons' hpositive (cons' hnegative (const []))
  have hterms := flatMapWithInput
    (f := fun (_ : CNF) (j : ℕ) => [ResetUnion.literalTerm (j, true), ResetUnion.literalTerm (j, false)])
    support_polyTime hpair
  have hlist := listAppend' hterms (const [(.var 0 : KFOL.ResetUnion.Term ℕ)])
  exact rightComb_polyTime.comp (hlist.prod (const (.var 1)))

@[fun_prop] theorem branch_polyTime : ComputableInPolyTime ResetUnion.branch encNat termEncoding := by
  have hp := literalTerm_polyTime.comp ((id' (encIn := encNat)).prod (const true))
  have hn := literalTerm_polyTime.comp ((id' (encIn := encNat)).prod (const false))
  have hgp := union_polyTime.comp (hp.prod (const (.var 0)))
  have hgn := union_polyTime.comp (hn.prod (const (.var 0)))
  exact reset_polyTime.comp ((reset_polyTime.comp ((const (.var 2)).prod hgp)).prod hgn)

@[fun_prop] theorem right_polyTime : ComputableInPolyTime ResetUnion.right cnfEncoding termEncoding := by
  have hbranch := branch_polyTime.comp (snd cnfEncoding encNat)
  have hbranches := mapWithInput (f := fun (_ : CNF) j => ResetUnion.branch j) support_polyTime hbranch
  exact rightComb_polyTime.comp (hbranches.prod baseline_polyTime)

@[fun_prop] theorem clauseGuard_polyTime : ComputableInPolyTime ResetUnion.clauseGuard clauseEncoding termEncoding := by
  have hterm := literalTerm_polyTime.comp (snd clauseEncoding literalEncoding)
  have hterms := mapWithInput (f := fun (_ : Clause) literal => ResetUnion.literalTerm literal)
    (id' (encIn := clauseEncoding)) hterm
  exact unionFold_polyTime.comp ((const (.var 0)).prod hterms)

@[fun_prop] theorem left_polyTime : ComputableInPolyTime ResetUnion.left cnfEncoding termEncoding := by
  have hguard := clauseGuard_polyTime.comp (snd cnfEncoding clauseEncoding)
  have hguards := mapWithInput (f := fun (_ : CNF) clause => ResetUnion.clauseGuard clause)
    (id' (encIn := cnfEncoding)) hguard
  exact leftComb_polyTime.comp ((const (.var 2)).prod hguards)

/-- One complete native polynomial-time generator, including all copied syntax
and every binary literal name. Source and output are exact original encodings. -/
@[fun_prop] theorem reduction_polyTime : ComputableInPolyTime ResetUnion.equation cnfEncoding equationEncoding := by
  have hlhs := reset_polyTime.comp (left_polyTime.prod right_polyTime)
  exact equation_polyTime.comp (hlhs.prod right_polyTime)

@[fun_prop] theorem encoded_reduction_polyTime : ComputableInPolyTime
    (fun formula => KFOL.ResetUnion.Code.encodeEquation (ResetUnion.equation formula)) cnfEncoding encBits :=
  (ComputableInPolyTime.of_eq (fun _ => rfl) :
    ComputableInPolyTime KFOL.ResetUnion.Code.encodeEquation equationEncoding encBits).comp reduction_polyTime

end KFOL.Complexity.ResetUnionReduction
