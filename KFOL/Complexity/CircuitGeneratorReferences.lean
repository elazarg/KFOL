module
public import KFOL.Complexity.CircuitGeneratorCNFMachine
public import KFOL.Complexity.ResetUnionReduction
/-! Sparse source dictionaries and original cache references, uniformly in the bit lengths of variable names. No loop enumerates through a maximum name. -/

@[expose] public section
namespace KFOL.Complexity.CircuitGenerator
open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.Reductions
open Circuit.ResetCNF
open CircuitMachine
open ResetUnionReduction (literalEncoding clauseEncoding cnfEncoding)

@[fun_prop] theorem inputNames_polyTime : ComputableInPolyTime inputNames cnfEncoding refsEncoding := by
  have hj := snd cnfEncoding encNat
  have hp := ResetUnionReduction.literalName_polyTime.comp (hj.prod (const true))
  have hn := ResetUnionReduction.literalName_polyTime.comp (hj.prod (const false))
  have hnames := flatMapWithInput (f := fun (_ : CNF) i =>
    [ResetUnion.literalName (i,true),ResetUnion.literalName (i,false)])
    ResetUnionReduction.support_polyTime (cons' hp (cons' hn (const [])))
  exact cons' (const 0) (cons' (const 1) hnames)

@[fun_prop] theorem literalRef_polyTime : ComputableInPolyTime
    (fun p : CNF × Literal => literalRef p.1 p.2)
    (encPair cnfEncoding literalEncoding) encNat := by
  have hnames := inputNames_polyTime.comp (fst cnfEncoding literalEncoding)
  have hname := ResetUnionReduction.literalName_polyTime.comp (snd cnfEncoding literalEncoding)
  exact unary_to_binary.comp ((idxOf encNat).comp (hnames.prod hname))

@[fun_prop] theorem pairs_polyTime : ComputableInPolyTime pairs cnfEncoding
    (encList (encPair encNat encNat)) := by
  have hf := fst cnfEncoding encNat
  have hj := snd cnfEncoding encNat
  have hp := literalRef_polyTime.comp (hf.prod (hj.prod (const true)))
  have hn := literalRef_polyTime.comp (hf.prod (hj.prod (const false)))
  exact mapWithInput (f := fun φ i => (literalRef φ (i,true),literalRef φ (i,false)))
    ResetUnionReduction.support_polyTime (hp.prod hn)

@[fun_prop] theorem railRefs_polyTime : ComputableInPolyTime railRefs cnfEncoding refsEncoding := by
  have hp : ComputableInPolyTime (fun p : CNF × (ℕ × ℕ) => p.2.1)
      (encPair cnfEncoding (encPair encNat encNat)) encNat := by fun_prop
  have hn : ComputableInPolyTime (fun p : CNF × (ℕ × ℕ) => p.2.2)
      (encPair cnfEncoding (encPair encNat encNat)) encNat := by fun_prop
  exact flatMapWithInput (f := fun (_ : CNF) p => [p.1,p.2]) pairs_polyTime
    (cons' hp (cons' hn (const [])))

@[fun_prop] theorem clauseRefs_polyTime : ComputableInPolyTime clauseRefs cnfEncoding clausesEncoding := by
  have hf : ComputableInPolyTime (fun p : (CNF × Clause) × Literal => p.1.1)
      (encPair (encPair cnfEncoding clauseEncoding) literalEncoding) cnfEncoding := by fun_prop
  have hnode := literalRef_polyTime.comp (hf.prod (snd _ _))
  have hclause := mapWithInput (f := fun (p : CNF × Clause) lit => literalRef p.1 lit)
    (snd cnfEncoding clauseEncoding) hnode
  exact mapWithInput (f := fun φ clause => clause.map (literalRef φ)) (id' (encIn := cnfEncoding)) hclause

@[fun_prop] theorem inputs_polyTime : ComputableInPolyTime
    (fun φ => (inputs φ).map viewGate) cnfEncoding gatesEncoding := by
  have h := mapWithInput (f := fun (_ : CNF) name => inputGate name)
    inputNames_polyTime (inputGate_polyTime.comp (snd _ _))
  simpa only [inputs, List.map_map, Function.comp_def, view_input] using h
end KFOL.Complexity.CircuitGenerator
