module

public import KFOL.Complexity.ResetUnionEvaluation

/-! # Complete native parsing of original reset/union equation words -/

@[expose] public section

namespace KFOL.Complexity.ResetUnionDecoding

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.ResetUnion

private def decodePair (p : List Bool × List Bool) : Option Equation :=
  ([p.1, p.2].mapM Code.decode).map (fun terms =>
    (terms.getD 0 (.var 0), terms.getD 1 (.var 0)))

private theorem decodePair_polyTime : ComputableInPolyTime decodePair
    (encPair encBits encBits) (encOption ResetUnionMachines.equationEncoding) := by
  let input := encPair encBits encBits
  have hlist := cons' (fst encBits encBits) (cons' (snd encBits encBits) (const []))
  have hdecode := mapMWithInput_polyTime (f := fun (_ : List Bool × List Bool) word => Code.decode word)
    hlist (ResetUnionEvaluation.Syntax.decode_polyTime.comp (snd input encBits)) (.var 0)
  have hterms := snd input (encList ResetUnionMachines.termEncoding)
  have hleft := listGetDWithInput hterms (const 0) (.var 0)
  have hright := listGetDWithInput hterms (const 1) (.var 0)
  have hpair := ResetUnionMachines.equation_polyTime.comp (hleft.prod hright)
  exact hdecode.optionMapWithInput
    (f := fun (_ : List Bool × List Bool) (terms : List (KFOL.ResetUnion.Term ℕ)) =>
      (terms.getD 0 (.var 0), terms.getD 1 (.var 0))) hpair

/-- The actual complete equation parser, including outer framing, both
original prefix trees and malformed-input rejection, is polynomial-time. -/
@[fun_prop] theorem decodeEquation_polyTime : ComputableInPolyTime Code.decodeEquation encBits
    (encOption ResetUnionMachines.equationEncoding) := by
  have h := Framing.unpair_polyTime.optionElimWithInput
    (body := fun (_ : List Bool) p => decodePair p) (const none)
    (decodePair_polyTime.comp (snd encBits (encPair encBits encBits)))
  convert h using 1
  funext word
  unfold Code.decodeEquation
  cases hp : KFOL.Words.unpair? word with
  | none => rfl
  | some pair =>
    rcases pair with ⟨left, right⟩
    change (do
      let s ← Code.decode left
      let t ← Code.decode right
      pure (s, t)) = decodePair (left, right)
    unfold decodePair
    cases hl : Code.decode left <;> cases hr : Code.decode right <;> simp [List.mapM_cons, hl, hr]

/-- Every accepted external equation is its exact complete original code. -/
theorem encodeEquation_of_decodeEquation {word : List Bool} {equation : Equation}
    (h : Code.decodeEquation word = some equation) : Code.encodeEquation equation = word := by
  unfold Code.decodeEquation at h
  obtain ⟨⟨left, right⟩, hp, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨s, hs, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨t, ht, he⟩ := Option.bind_eq_some_iff.mp h
  cases Option.some.inj he
  simp only [Code.encodeEquation, Code.encode_of_decode hs, Code.encode_of_decode ht]
  exact (KFOL.Words.eq_delimit_append_of_unpair?_eq_some hp).symm

end KFOL.Complexity.ResetUnionDecoding
