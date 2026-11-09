module

public import KFOL.Algorithms.FullTermCode.Actions
public import KFOL.Algorithms.FullTermCode.Validation
public import KFOL.Complexity.FullTermDecoding
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-! # Native polynomial-time sparse-array primitives, uniformly in binary K -/

@[expose] public section

namespace KFOL.Complexity.CoreExtraction

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FullTermCode

abbrev arrayEncoding := encList encNat
abbrev actionEncoding := encOption arrayEncoding

/-- Binary array indexing is capped against the actual list length by the
library machine. A binary role label is never expanded into a unary clock. -/
theorem arrayLookup_polyTime : ComputableInPolyTime
    (fun p : List ℕ × ℕ => p.1.getD p.2 0) (encPair arrayEncoding encNat) encNat :=
  .of_tidy (ComputableTidilyInPolyTime.listGetD_binary (encA := encNat) (encL := arrayEncoding) 0
    (ComputableTidilyInPolyTime.fst arrayEncoding encNat)
    (ComputableTidilyInPolyTime.snd arrayEncoding encNat))

/-- Composition traverses the actual stored right array and performs capped
binary lookups in the actual stored left array. -/
theorem compose_arrays_polyTime : ComputableInPolyTime
    (fun p : List ℕ × List ℕ => p.2.map (fun role => p.1.getD role 0))
    (encPair arrayEncoding arrayEncoding) arrayEncoding := by
  let input := encPair arrayEncoding arrayEncoding
  have hlist : ComputableInPolyTime (fun p : List ℕ × List ℕ => p.2) input arrayEncoding := snd _ _
  have hleft : ComputableInPolyTime (fun p : (List ℕ × List ℕ) × ℕ => p.1.1)
      (encPair input encNat) arrayEncoding := by fun_prop
  have hrole := snd input encNat
  exact mapWithInput hlist (arrayLookup_polyTime.comp (hleft.prod hrole))

/-- Both absent identity cases copy an existing representation and never
materialize a K-entry array from binary K. -/
theorem compose_polyTime : ComputableInPolyTime
    (fun p : Action × Action => Action.compose p.1 p.2)
    (encPair actionEncoding actionEncoding) actionEncoding := by
  let input := encPair actionEncoding actionEncoding
  let callback := encPair input arrayEncoding
  have hright : ComputableInPolyTime (fun p : (Action × Action) × List ℕ => p.1.2)
      callback actionEncoding := by fun_prop
  have hleft : ComputableInPolyTime (fun p : (Action × Action) × List ℕ => p.2)
      callback arrayEncoding := snd _ _
  have hl : ComputableInPolyTime (fun p : ((Action × Action) × List ℕ) × List ℕ => p.1.2)
      (encPair callback arrayEncoding) arrayEncoding := by fun_prop
  have hr := snd callback arrayEncoding
  have hsome : ComputableInPolyTime
      (fun p : ((Action × Action) × List ℕ) × List ℕ =>
        some (p.2.map (fun role => p.1.2.getD role 0)))
      (encPair callback arrayEncoding) actionEncoding :=
    (optionSome arrayEncoding).comp (compose_arrays_polyTime.comp (hl.prod hr))
  have hbody := hright.optionElimWithInput
    (body := fun (p : (Action × Action) × List ℕ) right =>
      some (right.map (fun role => p.2.getD role 0)))
    ((optionSome arrayEncoding).comp hleft) hsome
  have h := (fst actionEncoding actionEncoding).optionElimWithInput
    (body := fun (p : Action × Action) left =>
      p.2.elim (some left) (fun right => some (right.map (fun role => left.getD role 0))))
    (snd actionEncoding actionEncoding) hbody
  convert h using 1
  funext p
  rcases p with ⟨left,right⟩
  cases left <;> cases right <;> rfl

/-- The actual array's positions are numbered in unary, charged to its length;
comparison converts those bounded indices to binary rather than expanding K. -/
theorem arrayIdentity_polyTime : ComputableInPolyTime
    (fun forward : List ℕ => forward.zipIdx.all (fun entry => entry.1 == entry.2))
    arrayEncoding encBool := by
  let entryEncoding := encPair encNat encUnary
  let callback := encPair arrayEncoding entryEncoding
  have hzip : ComputableInPolyTime (fun forward : List ℕ => forward.zipIdx)
      arrayEncoding (encList entryEncoding) :=
    .of_tidy (ComputableTidilyInPolyTime.zipIdx encNat)
  have hv : ComputableInPolyTime (fun p : List ℕ × (ℕ × ℕ) => p.2.1) callback encNat := by fun_prop
  have hi : ComputableInPolyTime (fun p : List ℕ × (ℕ × ℕ) => p.2.2) callback encUnary := by fun_prop
  have htest := decide_eq' hv (unary_to_binary.comp hi)
  have h := allWithInput
    (test := fun (_ : List ℕ) (entry : ℕ × ℕ) => decide (entry.1 = entry.2)) hzip
    (by simpa only [Function.comp_def] using htest)
  exact h

/-- Sparse identity checking is a native polynomial machine, including the
constant-time physically absent identity representation. -/
theorem isIdentity_polyTime : ComputableInPolyTime Action.isIdentity actionEncoding encBool := by
  have h := (id' (encIn := actionEncoding)).optionElimWithInput
    (body := fun (_ : Action) forward => forward.zipIdx.all (fun entry => entry.1 == entry.2))
    (const true) (arrayIdentity_polyTime.comp (snd actionEncoding arrayEncoding))
  convert h using 1
  funext action
  cases action <;> rfl

/-- The complete physical permutation-array validation is polynomial in its
stored array and binary K. The length check precedes range and Nodup scans. -/
theorem validArray_polyTime : ComputableInPolyTime
    (fun p : ℕ × List ℕ => validArray p.1 p.2) (encPair encNat arrayEncoding) encBool := by
  let input := encPair encNat arrayEncoding
  have hK := fst encNat arrayEncoding
  have harray := snd encNat arrayEncoding
  have hlength := unary_to_binary.comp ((length_list encNat).comp harray)
  have hsame := decide_eq' hlength hK
  have hrole : ComputableInPolyTime (fun p : (ℕ × List ℕ) × ℕ => p.2)
      (encPair input encNat) encNat := snd _ _
  have hcount : ComputableInPolyTime (fun p : (ℕ × List ℕ) × ℕ => p.1.1)
      (encPair input encNat) encNat := by fun_prop
  have hbound := binary_lt' hrole hcount
  have hall := allWithInput (test := fun (p : ℕ × List ℕ) role => decide (role < p.1)) harray hbound
  have hnd := Dictionary.dictionary_nodup_polyTime.comp harray
  have h := hsame.ite (bool_and' hall hnd) (const false)
  convert h using 1
  funext p
  simp only [validArray,beq_iff_eq,Function.comp_def,decide_eq_true_eq]

end KFOL.Complexity.CoreExtraction
