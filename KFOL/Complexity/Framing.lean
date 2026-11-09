module

public import KFOL.Algorithms.Words
public import KFOL.Complexity.SuffixFold
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option

/-! # Complete machine-certified parsing of the paper's binary framing

The mathematical framing uses two-bit doubled payloads and a two-bit separator.
The native machine's typed input/output encodings are separate embeddings.
-/

@[expose] public section

namespace KFOL.Complexity.Framing

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.Words

private abbrev Result := Option (List Bool × List Bool)
private abbrev resultEncoding : Result ↪ List Bool := encOption (encPair encBits encBits)
private abbrev stateEncoding := encPair resultEncoding resultEncoding
private abbrev Input := (Bool × (List Bool × (Result × Result))) × Bool
private abbrev inputEncoding := encPair (encPair encBool (encPair encBits stateEncoding)) encBool

private def step (_ : Bool) (suffix : List Bool) (state : Result × Result) (bit : Bool) : Result × Result :=
  (if suffix.isEmpty then none
   else if bit == suffix.headD false then state.2.map (fun p => (bit :: p.1, p.2))
   else if bit then none else some ([], suffix.tail), state.1)

private theorem suffixFold_step (word : List Bool) :
    suffixFold step false (none, none) word = (unpair? word, unpair? word.tail) := by
  induction word with
  | nil => rfl
  | cons bit word ih =>
    rw [suffixFold_cons, ih]
    cases word with
    | nil => cases bit <;> rfl
    | cons head tail => cases bit <;> cases head <;> rfl

private theorem step_polyTime : ComputableInPolyTime
    (fun p : Input => step p.1.1 p.1.2.1 p.1.2.2 p.2) inputEncoding stateEncoding := by
  have hword : ComputableInPolyTime (fun p : Input => p.1.2.1) inputEncoding encBits := by fun_prop
  have hbit : ComputableInPolyTime (fun p : Input => p.2) inputEncoding encBool := by fun_prop
  have hprev : ComputableInPolyTime (fun p : Input => p.1.2.2.2) inputEncoding resultEncoding := by fun_prop
  have hkeep : ComputableInPolyTime (fun p : Input => p.1.2.2.1) inputEncoding resultEncoding := by fun_prop
  have hmapbody : ComputableInPolyTime
      (fun p : Input × (List Bool × List Bool) => (p.1.2 :: p.2.1, p.2.2))
      (encPair inputEncoding (encPair encBits encBits)) (encPair encBits encBits) := by
    apply ComputableInPolyTime.pair (enc₁ := encBits) (enc₂ := encBits)
    · exact bitsCons (by fun_prop) (by fun_prop)
    · fun_prop
  have hmap := hprev.optionMapWithInput (f := fun p q => (p.2 :: q.1, q.2)) hmapbody
  have hsep : ComputableInPolyTime (fun p : Input => some ([], p.1.2.1.tail)) inputEncoding resultEncoding :=
    (optionSome (encPair encBits encBits)).comp ((const []).prod (bitsTail.comp hword))
  have hbool : ComputableInPolyTime (fun p : Bool × Bool => p.1 == p.2)
      (encPair encBool encBool) encBool := .of_finite _
  have heq := hbool.comp (hbit.prod ((headD false).comp hword))
  exact ((bitsIsEmpty.comp hword).ite (const none)
    (heq.ite hmap (hbit.ite (const none) hsep))).prod hkeep

private theorem result_length (word : List Bool) :
    (resultEncoding (unpair? word)).length ≤ word.length := by
  cases h : unpair? word with
  | none => simp
  | some p =>
    obtain ⟨block, rest⟩ := p
    have he := congrArg List.length (eq_delimit_append_of_unpair?_eq_some h)
    simp only [List.length_append, delimit_length] at he
    simp only [encOption_some, List.length_cons, length_encPair, encBits_apply]
    omega

/-- The complete existing prefix parser has a native deterministic
polynomial-time machine, including malformed inputs and both returned fields. -/
@[fun_prop] theorem unpair_polyTime :
    ComputableInPolyTime unpair? encBits (encOption (encPair encBits encBits)) := by
  have hbound : PolyBounded (fun word : List Bool => word.length) (fun word => 3 * word.length + 1) :=
    ((PolyBounded.const 3).mul PolyBounded.self).add (.const 1)
  have hscan := suffixFold_polyTime (context := fun _ : List Bool => false)
    (word := id) (initial := fun _ : List Bool => (none, none)) (step := step)
    (input := encBits) (contextEncoding := encBool) (stateEncoding := stateEncoding)
    (const false) id' (const (none, none)) step_polyTime hbound
    (fun word suffix hs => by
      rw [suffixFold_step, length_encPair]
      have h1 := result_length suffix
      have h2 := result_length suffix.tail
      have htail : suffix.tail.length ≤ suffix.length := by simp only [List.length_tail]; omega
      have hlen : suffix.length ≤ word.length := hs.length_le
      dsimp only [Prod.fst, Prod.snd]
      omega)
  have h := (ComputableInPolyTime.fst resultEncoding resultEncoding).comp hscan
  simpa only [suffixFold_step, Function.comp_def, id] using h

/-- Framing validity is certified through the exact prefix parser. -/
@[fun_prop] theorem prefix_isSome_polyTime :
    ComputableInPolyTime (fun word => (unpair? word).isSome) encBits encBool :=
  unpair_polyTime.optionIsSome

/-- Framing a whole payload charges every doubled bit and the delimiter. -/
@[fun_prop] theorem delimit_polyTime : ComputableInPolyTime delimit encBits encBits := by
  have hbit : ComputableInPolyTime (fun bit : Bool => [bit, bit]) encBool encBits := .of_finite _
  have hdouble : ComputableInPolyTime (fun word : List Bool => word.flatMap fun bit => [bit, bit])
      encBits encBits :=
    flatMapToBitsWithInput (bits_encList_polyTime encBool).1 (hbit.comp (.snd encBits encBool))
  exact hdouble.bitsAppend (const [false, true])

/-- The paper's complete word pairing is a polynomial-time operation,
distinct from the native typed input pairing embedding. -/
@[fun_prop] theorem pair_polyTime :
    ComputableInPolyTime (fun p : List Bool × List Bool => pair p.1 p.2)
      (encPair encBits encBits) encBits :=
  (delimit_polyTime.comp (.fst encBits encBits)).bitsAppend (.snd encBits encBits)

/-- The total payload projection agrees with the original parser on both
successful and malformed inputs. -/
@[fun_prop] theorem payload_polyTime :
    ComputableInPolyTime (fun word => ((unpair? word).getD ([], [])).1) encBits encBits := by
  have h := unpair_polyTime.optionGetDWithInput (const ([], []))
  have hfirst := (ComputableInPolyTime.fst encBits encBits).comp h
  exact hfirst

end KFOL.Complexity.Framing
