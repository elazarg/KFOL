module
public import KFOL.Complexity.CircuitGeneratorCNF
public import KFOL.Complexity.CircuitGeneratorBlocks
/-! Native prefix scans and clause chunk generation. Unary indices enumerate actual list positions, while cache references remain binary. -/

@[expose] public section
namespace KFOL.Complexity.CircuitGenerator
open Turing.MultiTapeTM ComputableInPolyTime

noncomputable abbrev refsEncoding := encList encNat
noncomputable abbrev clausesEncoding := encList refsEncoding
abbrev CNFInput := List (List ℕ) × (ℕ × (ℕ × ℕ))
noncomputable abbrev cnfInputEncoding := encPair clausesEncoding (encPair encNat (encPair encNat encNat))

@[fun_prop] theorem flattenNat_polyTime : ComputableInPolyTime
    (List.flatten (α := ℕ)) clausesEncoding refsEncoding := by
  have h := flatMapWithInput (f := fun (_ : List (List ℕ)) (clause : List ℕ) => clause)
    (id' (encIn := clausesEncoding)) (snd clausesEncoding refsEncoding)
  simpa only [List.flatMap_id'] using h

@[fun_prop] theorem lastClause_polyTime : ComputableInPolyTime
    lastClause clausesEncoding refsEncoding :=
  (headD []).comp (id' (encIn := clausesEncoding)).listReverseWithInput

@[fun_prop] theorem prefixOutput_polyTime : ComputableInPolyTime
    (fun p : CNFInput => prefixOutput p.1 p.2.1 p.2.2.1 p.2.2.2)
    cnfInputEncoding encNat := by
  have hc := fst clausesEncoding (encPair encNat (encPair encNat encNat))
  have hp : ComputableInPolyTime (fun p : CNFInput => p.2.1) cnfInputEncoding encNat := by fun_prop
  have hr : ComputableInPolyTime (fun p : CNFInput => p.2.2.1) cnfInputEncoding encNat := by fun_prop
  have ho : ComputableInPolyTime (fun p : CNFInput => p.2.2.2) cnfInputEncoding encNat := by fun_prop
  have hn := (lengthBinary_polyTime encNat).comp (flattenNat_polyTime.comp hc)
  have he := (listIsEmpty (encA := refsEncoding)).comp hc
  have hl := (listIsEmpty (encA := encNat)).comp (lastClause_polyTime.comp hc)
  exact he.ite hp (hl.ite hr (binary_sub' (binary_add.comp (ho.prod (binary_mul' (const 2) hn))) (const 1)))

@[fun_prop] theorem cnfNodes_polyTime : ComputableInPolyTime
    (fun p : CNFInput => cnfNodes p.1 p.2.1 p.2.2.1 p.2.2.2)
    cnfInputEncoding gatesEncoding := by
  let callbackEncoding := encPair cnfInputEncoding (encPair refsEncoding encUnary)
  have hall : ComputableInPolyTime
      (fun p : CNFInput × (List ℕ × ℕ) => p.1.1) callbackEncoding clausesEncoding := by fun_prop
  have hidx : ComputableInPolyTime
      (fun p : CNFInput × (List ℕ × ℕ) => p.2.2) callbackEncoding encUnary := by fun_prop
  have hclause : ComputableInPolyTime
      (fun p : CNFInput × (List ℕ × ℕ) => p.2.1) callbackEncoding refsEncoding := by fun_prop
  have hp : ComputableInPolyTime
      (fun p : CNFInput × (List ℕ × ℕ) => p.1.2.1) callbackEncoding encNat := by fun_prop
  have hr : ComputableInPolyTime
      (fun p : CNFInput × (List ℕ × ℕ) => p.1.2.2.1) callbackEncoding encNat := by fun_prop
  have ho : ComputableInPolyTime
      (fun p : CNFInput × (List ℕ × ℕ) => p.1.2.2.2) callbackEncoding encNat := by fun_prop
  have ht := ComputableInPolyTime.of_tidy
    ((ComputableTidilyInPolyTime.takeUnary refsEncoding).comp (hall.tidy.prod hidx.tidy))
  have hprevious := prefixOutput_polyTime.comp (ht.prod (hp.prod (hr.prod ho)))
  have hn := (lengthBinary_polyTime encNat).comp (flattenNat_polyTime.comp ht)
  have hoffset := binary_add.comp (ho.prod (binary_mul' (const 2) hn))
  have hnode := clauseNodes_polyTime.comp (hclause.prod (hprevious.prod (hr.prod hoffset)))
  have hz := (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.zipIdx refsEncoding)).comp
    (fst clausesEncoding (encPair encNat (encPair encNat encNat)))
  have h := flatMapWithInput (f := fun (p : CNFInput) (item : List ℕ × ℕ) =>
    clauseNodes item.1 (prefixOutput (p.1.take item.2) p.2.1 p.2.2.1 p.2.2.2) p.2.2.1
      (p.2.2.2 + 2 * (p.1.take item.2).flatten.length)) hz hnode
  exact h
end KFOL.Complexity.CircuitGenerator
