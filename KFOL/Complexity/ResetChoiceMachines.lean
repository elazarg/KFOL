module
public import KFOL.Complexity.RawPairMachines
@[expose] public section
namespace KFOL.Complexity.ResetChoiceMachines
open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.Reductions KFOL.Complexity.RawPairMachines

private theorem translate_var (j : ℕ) : ResetChoice.translate (.var j) = (.var j : Tree) := rfl
private theorem translate_reset (s t : KFOL.ResetUnion.Term ℕ) :
    ResetChoice.translate (s.reset t) = KFOL.RawPair.Term.node true (ResetChoice.translate s) (ResetChoice.translate t) := rfl
private theorem translate_union (s t : KFOL.ResetUnion.Term ℕ) :
    ResetChoice.translate (s.union t) = KFOL.RawPair.Term.node false (ResetChoice.translate s) (ResetChoice.translate t) := rfl

private theorem foldl_polyTime (sign : Bool) : ComputableInPolyTime
    (fun p : Tree × List Tree => p.2.foldl (KFOL.RawPair.Term.node sign) p.1)
    (encPair termEncoding (encList termEncoding)) termEncoding := by
  let input := encPair termEncoding (encList termEncoding)
  have hs : ComputableInPolyTime (fun p : ((Tree × List Tree) × Tree) × Tree => p.1.2)
      (encPair (encPair input termEncoding) termEncoding) termEncoding := by fun_prop
  have ht := snd (encPair input termEncoding) termEncoding
  have hstep := node_polyTime.comp ((const sign).prod (hs.prod ht))
  have hl := snd termEncoding (encList termEncoding)
  exact foldlWithInput_of_bounded_growth (list := fun p : Tree × List Tree => p.2)
    (init := fun p => p.1) (step := fun _ state term => KFOL.RawPair.Term.node sign state term)
    (fst _ _) ⟨hl, hstep, inferInstance, inferInstance⟩
    (growth := fun p => (encList termEncoding p.2).length + header sign)
    ⟨hl.polyBounded_length.add (PolyBounded.const (header sign)), fun p state term hterm => by
      have ht := SizedListEncoding.length_elem_le (encA := termEncoding) (encL := encList termEncoding) p.2 term hterm
      have hn := node_length sign state term
      omega⟩

private theorem translate_rightComb (terms : List (KFOL.ResetUnion.Term ℕ)) (base : KFOL.ResetUnion.Term ℕ) :
    ResetChoice.translate (KFOL.ResetUnion.Term.rightComb terms base) =
      KFOL.RawPair.Term.fold true (terms.map ResetChoice.translate) (ResetChoice.translate base) := by
  induction terms with
  | nil => rfl
  | cons term rest ih => simpa only [KFOL.ResetUnion.Term.rightComb, List.foldr_cons,
      List.map_cons, KFOL.RawPair.Term.fold, translate_reset] using congrArg (KFOL.RawPair.Term.node true (ResetChoice.translate term)) ih

private theorem translate_leftComb (terms : List (KFOL.ResetUnion.Term ℕ)) (base : KFOL.ResetUnion.Term ℕ) :
    ResetChoice.translate (KFOL.ResetUnion.Term.leftComb base terms) =
      (terms.map ResetChoice.translate).foldl (KFOL.RawPair.Term.node true) (ResetChoice.translate base) := by
  induction terms generalizing base with
  | nil => rfl
  | cons term rest ih => exact ih (base.reset term)

private theorem translate_unionFold (terms : List (KFOL.ResetUnion.Term ℕ)) (base : KFOL.ResetUnion.Term ℕ) :
    ResetChoice.translate (KFOL.ResetUnion.Term.unionFold base terms) =
      (terms.map ResetChoice.translate).foldl (KFOL.RawPair.Term.node false) (ResetChoice.translate base) := by
  induction terms generalizing base with
  | nil => rfl
  | cons term rest ih => exact ih (base.union term)

private theorem literal_polyTime : ComputableInPolyTime (fun literal => ResetChoice.translate (ResetUnion.literalTerm literal)) literalEncoding termEncoding :=
  RawPairMachines.literalTerm_polyTime

private theorem baseline_polyTime : ComputableInPolyTime
    (fun formula => ResetChoice.translate (ResetUnion.baseline formula)) cnfEncoding termEncoding := by
  have h := (RawPairMachines.fold_polyTime true).comp
    ((listAppend' RawPairMachines.rails_polyTime (const [(.var 0 : Tree)])).prod (const (.var 1 : Tree)))
  convert h using 1
  funext formula
  rw [ResetUnion.baseline, translate_rightComb]
  simp only [List.map_append, List.map_cons, List.map_nil, translate_var]
  congr 2
  simp [RawPair.rails, ResetChoice.translate, ResetUnion.literalTerm, RawPair.literalTerm, List.map_flatMap]

private theorem branch_polyTime : ComputableInPolyTime
    (fun j => ResetChoice.translate (ResetUnion.branch j)) encNat termEncoding := by
  have hp := literal_polyTime.comp ((id' (encIn := encNat)).prod (const true))
  have hn := literal_polyTime.comp ((id' (encIn := encNat)).prod (const false))
  have hgp := node_polyTime.comp ((const false).prod (hp.prod (const (.var 0 : Tree))))
  have hgn := node_polyTime.comp ((const false).prod (hn.prod (const (.var 0 : Tree))))
  exact node_polyTime.comp ((const true).prod ((node_polyTime.comp ((const true).prod ((const (.var 2 : Tree)).prod hgp))).prod hgn))

private theorem right_polyTime : ComputableInPolyTime
    (fun formula => ResetChoice.translate (ResetUnion.right formula)) cnfEncoding termEncoding := by
  have hbranches := mapWithInput (f := fun (_ : CNF) j => ResetChoice.translate (ResetUnion.branch j))
    ResetUnionReduction.support_polyTime (branch_polyTime.comp (snd cnfEncoding encNat))
  have h := (RawPairMachines.fold_polyTime true).comp (hbranches.prod baseline_polyTime)
  convert h using 1
  funext formula
  simp only [ResetUnion.right, translate_rightComb, List.map_map, Function.comp_def]

private theorem clause_polyTime : ComputableInPolyTime
    (fun clause => ResetChoice.translate (ResetUnion.clauseGuard clause)) clauseEncoding termEncoding := by
  have hterms := mapWithInput (f := fun (_ : Clause) literal => ResetChoice.translate (ResetUnion.literalTerm literal))
    (id' (encIn := clauseEncoding)) (literal_polyTime.comp (snd clauseEncoding literalEncoding))
  have h := (foldl_polyTime false).comp ((const (.var 0 : Tree)).prod hterms)
  convert h using 1
  funext clause
  simp only [ResetUnion.clauseGuard, translate_unionFold, List.map_map, Function.comp_def, translate_var]

private theorem left_polyTime : ComputableInPolyTime
    (fun formula => ResetChoice.translate (ResetUnion.left formula)) cnfEncoding termEncoding := by
  have hguards := mapWithInput (f := fun (_ : CNF) clause => ResetChoice.translate (ResetUnion.clauseGuard clause))
    (id' (encIn := cnfEncoding)) (clause_polyTime.comp (snd cnfEncoding clauseEncoding))
  have h := (foldl_polyTime true).comp ((const (.var 2 : Tree)).prod hguards)
  convert h using 1
  funext formula
  simp only [ResetUnion.left, translate_leftComb, List.map_map, Function.comp_def, translate_var]

/-- The ungated original reset/union construction transported one node at a
time to the native two-binary-operation syntax. -/
theorem translated_reduction_polyTime : ComputableInPolyTime
    (fun formula => (ResetChoice.translate (ResetUnion.equation formula).1,
      ResetChoice.translate (ResetUnion.equation formula).2)) cnfEncoding equationEncoding := by
  have hl := node_polyTime.comp ((const true).prod (left_polyTime.prod right_polyTime))
  exact FiniteTermMachines.equationRecode_polyTime.comp (hl.prod right_polyTime)

theorem reduction_polyTime : ComputableInPolyTime ResetChoice.equation cnfEncoding equationEncoding := by
  have hl := node_polyTime.comp ((const true).prod (left_polyTime.prod right_polyTime))
  have hcore := FiniteTermMachines.equationRecode_polyTime.comp (hl.prod right_polyTime)
  exact RawPairMachines.hasEmpty_polyTime.ite (const ((.var 0, .var 0) : Tree × Tree)) hcore
end KFOL.Complexity.ResetChoiceMachines
