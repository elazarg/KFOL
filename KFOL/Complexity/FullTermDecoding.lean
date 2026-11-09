module

public import KFOL.Complexity.FullTermFoldRuntime
public import KFOL.Complexity.OptionTraversal

/-! # Complete original-word decoding for a fixed finite signature

The cached-AST evaluator supplies a candidate. Re-encoding checks that candidate
against the whole input, which connects accepted output to the independent pure
prefix decoder and rejects every malformed or trailing word.
-/

@[expose] public section

namespace KFOL.Complexity.FullTermMachines

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FullTermCode


private def leaf (_ : Unit) (_ : ℕ) : Unit := ()
private def node (_ : Unit) (_ : Operation) (_ : List Unit) : Unit := ()

private noncomputable def candidate (word : List Bool) : Option (Raw) :=
  (FullTermFold.result (FullTermFold.evaluateState leaf node ((), word))).map Prod.fst

private theorem candidate_polyTime : ComputableInPolyTime candidate encBits (encOption termEncoding) := by
  have he := FullTermFold.evaluateState_polyTime (contextEncoding := encUnit) (valueEncoding := encUnit)
    leaf (node ) (const ()) (const ()) 0 0 (by intros; exact le_rfl)
  have hp : ComputableInPolyTime (fun word : List Bool => ((), word)) encBits (encPair encUnit encBits) :=
    (const ()).prod id'
  have hr := FullTermFold.result_polyTime.comp (he.comp hp)
  have hf : ComputableInPolyTime
      (fun p : List Bool × FullTermFold.Cached Unit => p.2.1)
      (encPair encBits (FullTermFold.cachedEncoding encUnit)) termEncoding := by fun_prop
  exact hr.optionMapWithInput (f := fun (_ : List Bool) cache => cache.1) hf

private theorem candidate_encode (term : Raw) : candidate (encode term) = some term := by
  simp only [candidate, FullTermFold.evaluateState_encode, FullTermFold.result,
    Option.elim_some, List.isEmpty_nil, Bool.true_and, ite_true, Option.map_some,
    FullTermFold.sourceCache]

private noncomputable def checkedDecode (word : List Bool) : Option (Raw) :=
  (candidate word).elim none (fun term => if encode term = word then some term else none)

private theorem checkedDecode_polyTime : ComputableInPolyTime checkedDecode encBits (encOption termEncoding) := by
  have hterm := snd encBits (termEncoding )
  have hword := fst encBits (termEncoding )
  have heq := decide_eq' (encode_polyTime.comp hterm) hword
  have hbody := heq.ite ((optionSome termEncoding).comp hterm) (const none)
  have hb : ComputableInPolyTime
      (fun p : List Bool × Raw => if encode p.2 = p.1 then some p.2 else none)
      (encPair encBits termEncoding) (encOption termEncoding) := by
    convert hbody using 1
    funext p
    simp only [Function.comp_def, decide_eq_true_eq]
  exact (candidate_polyTime ).optionElimWithInput (body := fun word term =>
    if encode term = word then some term else none) (const none) hb

private theorem checkedDecode_eq (word : List Bool) : checkedDecode word = decode word := by
  cases hd : decode word with
  | none =>
    cases hc : candidate  word with
    | none => simp only [checkedDecode, hc, Option.elim_none]
    | some term =>
      have hn : encode term ≠ word := by
        intro he
        have hp := decode_encode term
        rw [he, hd] at hp
        contradiction
      simp only [checkedDecode, hc, Option.elim_some, hn, ite_false]
  | some term =>
    have he := encode_of_decode hd
    rw [← he]
    simp only [checkedDecode, candidate_encode, Option.elim_some, ite_true]

/-- The actual independent original decoder, including malformed-word rejection,
is polynomial-time with binary labels and explicit stored arrays, without
any finite-operation enumeration. -/
theorem decode_polyTime : ComputableInPolyTime (decode) encBits (encOption termEncoding) := by
  convert (checkedDecode_polyTime ) using 1
  funext word
  exact (checkedDecode_eq word).symm

end KFOL.Complexity.FullTermMachines
