module

public import KFOL.Algorithms.ResetUnionCode
public import KFOL.Complexity.TermSupport
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-! # Native machine constructors for reset/union prefix trees -/

@[expose] public section

namespace KFOL.Complexity.ResetUnionMachines

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.ResetUnion

/-- The exact original reset/union prefix codec. -/
def termEncoding : KFOL.ResetUnion.Term ℕ ↪ List Bool := ⟨Code.encode, Code.encode_injective⟩

def equationEncoding : Equation ↪ List Bool := ⟨Code.encodeEquation, Code.encodeEquation_injective⟩

@[fun_prop] theorem var_polyTime : ComputableInPolyTime
    (fun j : ℕ => (.var j : KFOL.ResetUnion.Term ℕ)) encNat termEncoding := by
  have h := bitsCons (const false) (Framing.delimit_polyTime.comp Dictionary.encode_polyTime)
  exact h.of_enc_eq (fun _ => rfl)

private theorem syntax_polyTime : ComputableInPolyTime Code.encode termEncoding encBits := .of_eq (fun _ => rfl)

@[fun_prop] theorem reset_polyTime : ComputableInPolyTime
    (fun p : KFOL.ResetUnion.Term ℕ × KFOL.ResetUnion.Term ℕ => p.1.reset p.2)
    (encPair termEncoding termEncoding) termEncoding := by
  have h := bitsCons (const true) (bitsCons (const false)
    (bitsAppend (syntax_polyTime.comp (fst _ _)) (syntax_polyTime.comp (snd _ _))))
  exact h.of_enc_eq (fun _ => rfl)

@[fun_prop] theorem union_polyTime : ComputableInPolyTime
    (fun p : KFOL.ResetUnion.Term ℕ × KFOL.ResetUnion.Term ℕ => p.1.union p.2)
    (encPair termEncoding termEncoding) termEncoding := by
  have h := bitsCons (const true) (bitsCons (const true)
    (bitsAppend (syntax_polyTime.comp (fst _ _)) (syntax_polyTime.comp (snd _ _))))
  exact h.of_enc_eq (fun _ => rfl)

private theorem foldl_polyTime
    (op : KFOL.ResetUnion.Term ℕ → KFOL.ResetUnion.Term ℕ → KFOL.ResetUnion.Term ℕ)
    (hop : ComputableInPolyTime (fun p : KFOL.ResetUnion.Term ℕ × KFOL.ResetUnion.Term ℕ => op p.1 p.2)
      (encPair termEncoding termEncoding) termEncoding)
    (hgrowth : ∀ s t, (Code.encode (op s t)).length ≤ (Code.encode s).length + (Code.encode t).length + 2) :
    ComputableInPolyTime
      (fun p : KFOL.ResetUnion.Term ℕ × List (KFOL.ResetUnion.Term ℕ) => p.2.foldl op p.1)
      (encPair termEncoding (encList termEncoding)) termEncoding := by
  let input := encPair termEncoding (encList termEncoding)
  have hs : ComputableInPolyTime
      (fun p : ((KFOL.ResetUnion.Term ℕ × List (KFOL.ResetUnion.Term ℕ)) × KFOL.ResetUnion.Term ℕ) × KFOL.ResetUnion.Term ℕ => p.1.2)
      (encPair (encPair input termEncoding) termEncoding) termEncoding := by fun_prop
  have ht := snd (encPair input termEncoding) termEncoding
  have hstep := hop.comp (hs.prod ht)
  have hlist := snd termEncoding (encList termEncoding)
  have hsize := ((hlist.polyBounded_length).add (PolyBounded.const 2))
  exact foldlWithInput_of_bounded_growth
    (encIn := input) (encA := termEncoding) (encB := termEncoding)
    (list := fun p => p.2) (init := fun p => p.1) (step := fun _ state term => op state term)
    (fst _ _) ⟨hlist, hstep, inferInstance, inferInstance⟩
    (growth := fun p => (encList termEncoding p.2).length + 2)
    ⟨hsize, fun p state term hterm => by
      have ht := SizedListEncoding.length_elem_le (encA := termEncoding)
        (encL := encList termEncoding) p.2 term hterm
      have hg := hgrowth state term
      change (Code.encode term).length ≤ _ at ht
      change (Code.encode (op state term)).length ≤ (Code.encode state).length + _
      omega⟩

@[fun_prop] theorem leftComb_polyTime : ComputableInPolyTime
    (fun p : KFOL.ResetUnion.Term ℕ × List (KFOL.ResetUnion.Term ℕ) => Term.leftComb p.1 p.2)
    (encPair termEncoding (encList termEncoding)) termEncoding := by
  exact foldl_polyTime Term.reset reset_polyTime (fun s t => by
    simp only [Code.encode_reset, List.length_cons, List.length_append]; omega)

@[fun_prop] theorem unionFold_polyTime : ComputableInPolyTime
    (fun p : KFOL.ResetUnion.Term ℕ × List (KFOL.ResetUnion.Term ℕ) => Term.unionFold p.1 p.2)
    (encPair termEncoding (encList termEncoding)) termEncoding := by
  exact foldl_polyTime Term.union union_polyTime (fun s t => by
    simp only [Code.encode_union, List.length_cons, List.length_append]; omega)

@[fun_prop] theorem rightComb_polyTime : ComputableInPolyTime
    (fun p : List (KFOL.ResetUnion.Term ℕ) × KFOL.ResetUnion.Term ℕ => Term.rightComb p.1 p.2)
    (encPair (encList termEncoding) termEncoding) termEncoding := by
  have hswap : ComputableInPolyTime
      (fun p : KFOL.ResetUnion.Term ℕ × KFOL.ResetUnion.Term ℕ => p.2.reset p.1)
      (encPair termEncoding termEncoding) termEncoding := reset_polyTime.comp ((snd _ _).prod (fst _ _))
  have hfold := foldl_polyTime (fun s t => t.reset s) hswap (fun s t => by
    simp only [Code.encode_reset, List.length_cons, List.length_append]; omega)
  have hreverse := (fst (encList termEncoding) termEncoding).listReverseWithInput
  have h := hfold.comp ((snd _ _).prod hreverse)
  convert h using 1
  funext p
  exact List.foldr_eq_foldl_reverse

@[fun_prop] theorem encodeEquation_polyTime : ComputableInPolyTime Code.encodeEquation
    (encPair termEncoding termEncoding) encBits :=
  Framing.pair_polyTime.comp ((syntax_polyTime.comp (fst _ _)).prod (syntax_polyTime.comp (snd _ _)))

/-- Convert the native argument tuple representation to the exact original
one-word equation serialization; the two framing conventions remain distinct. -/
@[fun_prop] theorem equation_polyTime : ComputableInPolyTime
    (fun p : Equation => p) (encPair termEncoding termEncoding) equationEncoding :=
  encodeEquation_polyTime.of_enc_eq (fun _ => rfl)


/-- Read the two original tree encodings from the paper's one-word equation
framing, converting to the native argument tuple without reparsing either tree. -/
@[fun_prop] theorem arguments_polyTime : ComputableInPolyTime
    (fun equation : Equation => equation) equationEncoding (encPair termEncoding termEncoding) := by
  have hword : ComputableInPolyTime Code.encodeEquation equationEncoding encBits := .of_eq (fun _ => rfl)
  have h := (Framing.unpair_polyTime.comp hword).optionGetDWithInput (const ([], []))
  apply h.of_enc_eq
  intro equation
  simp only [Function.comp_def, Code.encodeEquation, Words.unpair?_pair, Option.getD_some]
  rfl

end KFOL.Complexity.ResetUnionMachines
