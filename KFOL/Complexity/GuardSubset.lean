module

public import KFOL.Algorithms.GuardWords
public import KFOL.Complexity.SuffixFold
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi

/-! # A native machine-certified prerequisite subset test on membership words -/

@[expose] public section

namespace KFOL.Complexity.GuardSubset

open Algorithms.GuardWords
open Turing.MultiTapeTM ComputableInPolyTime

private abbrev Context := List Bool × List Bool
private abbrev contextEncoding := encPair encBits encBits
private abbrev CallbackInput := (Context × (List Bool × List Bool)) × Bool
private abbrev callbackEncoding := encPair (encPair contextEncoding (encPair encBits encBits)) encBool

private def step (context : Context) (suffix state : List Bool) (_ : Bool) : List Bool :=
  subsetStep suffix state context.1 context.2

private theorem fold_eq (r a b : List Bool) :
    suffixFold step (a, b) [true] r = subsetScan r a b := by
  induction r with
  | nil => rfl
  | cons bit r ih => rw [suffixFold_cons, ih]; rfl

private theorem step_polyTime : ComputableInPolyTime
    (fun p : CallbackInput => step p.1.1 p.1.2.1 p.1.2.2 p.2)
      callbackEncoding encBits := by
  have hleft : ComputableInPolyTime (fun p : CallbackInput => p.1.1.1) callbackEncoding encBits := by fun_prop
  have hright : ComputableInPolyTime (fun p : CallbackInput => p.1.1.2) callbackEncoding encBits := by fun_prop
  have hsuffix : ComputableInPolyTime (fun p : CallbackInput => p.1.2.1) callbackEncoding encBits := by fun_prop
  have hstate : ComputableInPolyTime (fun p : CallbackInput => p.1.2.2) callbackEncoding encBits := by fun_prop
  have hindex := length_bits.comp hsuffix
  have ha := bitsGetDWithInput hleft hindex false
  have hb := bitsGetDWithInput hright hindex false
  have htest := bool_or.comp ((bool_not.comp ha).prod hb)
  have h := bitsCons (bool_and' ((headD false).comp hstate) htest) (const [])
  simpa only [step, subsetStep, readBit, List.getD_eq_getElem?_getD, Function.comp_def] using h

/-- A single native scan implements the independently defined prerequisite
scan. Its accumulator has one bit for every suffix and every word width. -/
@[fun_prop] theorem subsetScan_polyTime : ComputableInPolyTime
    (fun v : Fin 2 → List Bool => subsetScan (v 0) (v 0) (v 1))
      (encPi encBits) encBits := by
  have h0 : ComputableInPolyTime (fun v : Fin 2 → List Bool => v 0) (encPi encBits) encBits :=
    pi_apply encBits 0
  have h1 : ComputableInPolyTime (fun v : Fin 2 → List Bool => v 1) (encPi encBits) encBits :=
    pi_apply encBits 1
  have h := suffixFold_polyTime (context := fun v : Fin 2 → List Bool => (v 0, v 1))
    (word := fun v => v 0) (initial := fun _ => [true]) (step := step)
    (h0.prod h1) h0 (const [true]) step_polyTime (PolyBounded.const 1)
    (fun v suffix _ => by rw [fold_eq, encBits_apply, subsetScan_length])
  simpa only [fold_eq] using h

/-- The actual total subset-word test has a deterministic polynomial-time
machine, including rejection of unequal widths. The index cost is unary in
the ruler length and independent of the word bits and numeric role names. -/
@[fun_prop] theorem subsetFn_polyTime :
    ComputableInPolyTime subsetFn (encPi encBits) encBits := by
  have h0 : ComputableInPolyTime (fun v : Fin 2 → List Bool => v 0) (encPi encBits) encBits :=
    pi_apply encBits 0
  have h1 : ComputableInPolyTime (fun v : Fin 2 → List Bool => v 1) (encPi encBits) encBits :=
    pi_apply encBits 1
  have hlen := decide_eq' (length_bits.comp h0) (length_bits.comp h1)
  have hscan := (headD (encA := encBool) (encL := encBits) false).comp subsetScan_polyTime
  exact bitsCons (bool_and' hlen hscan) (const [])

end KFOL.Complexity.GuardSubset
