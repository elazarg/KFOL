module

public import KFOL.Complexity.Framing

/-! # A complete polynomial-time scan of independently framed blocks -/

@[expose] public section

namespace KFOL.Complexity.BlockScan

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.Words

private abbrev Value := List (List Bool) × List Bool
private abbrev valueEncoding := encPair (encList encBits) encBits
private abbrev State := Option Value
private abbrev stateEncoding := encOption valueEncoding

private def step (state : State) : State :=
  state.elim none fun p =>
    if p.2.isEmpty then some p
    else (unpair? p.2).map (fun q => (q.1 :: p.1, q.2))

private def finish (state : State) : Option (List (List Bool)) :=
  state.elim none fun p => if p.2.isEmpty then some p.1.reverse else none

private theorem iterate_none (fuel : ℕ) : step^[fuel] none = none := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => rw [Function.iterate_succ_apply]; exact ih

private theorem iterate_empty (fuel : ℕ) (acc : List (List Bool)) :
    step^[fuel] (some (acc, [])) = some (acc, []) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => rw [Function.iterate_succ_apply]; exact ih

private theorem finish_iterate (fuel : ℕ) (acc : List (List Bool)) (word : List Bool) :
    finish (step^[fuel] (some (acc, word))) =
      (undelimitBlocksAux fuel word).map (fun blocks => acc.reverse ++ blocks) := by
  induction fuel generalizing acc word with
  | zero => cases word <;> simp [finish, undelimitBlocksAux]
  | succ fuel ih =>
    cases word with
    | nil => simp [iterate_empty, finish, undelimitBlocksAux]
    | cons b word =>
      rw [Function.iterate_succ_apply]
      change finish (step^[fuel] ((unpair? (b :: word)).map
        (fun q => (q.1 :: acc, q.2)))) = _
      cases hp : unpair? (b :: word) with
      | none => simp [iterate_none, finish, undelimitBlocksAux, hp]
      | some p =>
        rw [Option.map_some, ih]
        simp only [undelimitBlocksAux, hp]
        cases hb : undelimitBlocksAux fuel p.2 <;>
          simp [hb, List.reverse_cons, List.append_assoc]

private theorem decode_eq (word : List Bool) :
    finish (step^[word.length] (some ([], word))) = undelimitBlocks word := by
  rw [finish_iterate]
  simp [undelimitBlocks]

private theorem step_polyTime : ComputableInPolyTime step stateEncoding stateEncoding := by
  let callbackEncoding := encPair stateEncoding valueEncoding
  have hrest : ComputableInPolyTime (fun p : State × Value => p.2.2)
      callbackEncoding encBits := by fun_prop
  have hp := Framing.unpair_polyTime.comp hrest
  have hmapbody : ComputableInPolyTime
      (fun p : (State × Value) × (List Bool × List Bool) => (p.2.1 :: p.1.2.1, p.2.2))
      (encPair callbackEncoding (encPair encBits encBits)) valueEncoding := by
    apply ComputableInPolyTime.pair (enc₁ := encList encBits) (enc₂ := encBits)
    · exact cons' (by fun_prop) (by fun_prop)
    · fun_prop
  have hparse := hp.optionMapWithInput (f := fun p q => (q.1 :: p.2.1, q.2)) hmapbody
  have hkeep : ComputableInPolyTime (fun p : State × Value => some p.2)
      callbackEncoding stateEncoding := (optionSome valueEncoding).comp (snd _ _)
  have hbody := (bitsIsEmpty.comp hrest).ite hkeep hparse
  exact (id' (encIn := stateEncoding)).optionElimWithInput (const none) hbody

private theorem finish_polyTime : ComputableInPolyTime finish stateEncoding (encOption (encList encBits)) := by
  let callbackEncoding := encPair stateEncoding valueEncoding
  have hrest : ComputableInPolyTime (fun p : State × Value => p.2.2)
      callbackEncoding encBits := by fun_prop
  have hacc : ComputableInPolyTime (fun p : State × Value => p.2.1)
      callbackEncoding (encList encBits) := by fun_prop
  have hreverse := hacc.listReverseWithInput
  have hsome := (optionSome (encList encBits)).comp hreverse
  have hbody := (bitsIsEmpty.comp hrest).ite hsome (const none)
  exact (id' (encIn := stateEncoding)).optionElimWithInput (const none) hbody

private theorem native_list_length_le (blocks : List (List Bool)) :
    (encList encBits blocks).length ≤ (blocks.map delimit).flatten.length := by
  induction blocks with
  | nil => rfl
  | cons block blocks ih =>
    simp only [encList_cons, List.length_append, length_frame, encBits_apply,
      List.map_cons, List.flatten_cons, delimit_length]
    omega

private def invariant (word : List Bool) (_ : ℕ) (state : State) : Prop :=
  ∀ acc rest, state = some (acc, rest) →
    (acc.map delimit).flatten.length + rest.length = word.length

private theorem invariant_step (word : List Bool) (i : ℕ) (state : State)
    (h : invariant word i state) : invariant word (i + 1) (step state) := by
  intro acc rest he
  cases hs : state with
  | none => simp [step, hs] at he
  | some p =>
    have hold := h p.1 p.2 hs
    simp only [step, hs, Option.elim_some] at he
    split at he
    next =>
      have hp := Option.some.inj he
      cases hp
      exact hold
    next =>
      obtain ⟨⟨block, tail⟩, hp, he⟩ := Option.map_eq_some_iff.mp he
      cases he
      have hlen := congrArg List.length (eq_delimit_append_of_unpair?_eq_some hp)
      simp only [List.length_append] at hlen
      simp only [List.map_cons, List.flatten_cons, List.length_append]
      omega

/-- The existing complete block-list parser has a native deterministic
polynomial-time machine. The bound charges every parsed block, the current
suffix and the input-length clock, including malformed words. -/
@[fun_prop] theorem undelimitBlocks_polyTime :
    ComputableInPolyTime undelimitBlocks encBits (encOption (encList encBits)) := by
  have hsize : PolyBounded (fun word : List Bool => word.length)
      (fun word => 2 * word.length + 2) :=
    ((PolyBounded.const 2).mul PolyBounded.self).add (.const 2)
  have hstart : ComputableInPolyTime (fun word : List Bool => some ([], word)) encBits stateEncoding :=
    (optionSome valueEncoding).comp ((const []).prod id')
  have hloop := ComputableInPolyTime.iterate_spec (count := List.length) (step := step)
    length_bits hstart step_polyTime invariant
    (fun word => by intro acc rest he; cases Option.some.inj he; simp)
    (fun word i state _ h => invariant_step word i state h) hsize
    (fun word i state _ h => by
      cases hs : state with
      | none => simp
      | some p =>
        have he := h p.1 p.2 hs
        have hb := native_list_length_le p.1
        simp only [encOption_some, List.length_cons, length_encPair, encBits_apply]
        omega)
  have h := finish_polyTime.comp hloop.1
  simpa only [Function.comp_def, decode_eq] using h

end KFOL.Complexity.BlockScan
