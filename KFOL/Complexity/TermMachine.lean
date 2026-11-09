module

public import KFOL.Complexity.RawRecords

/-! # Native machine parser for the original prefix binary term language -/

@[expose] public section

namespace KFOL.Complexity.TermMachine

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.Algorithms KFOL.Words

/-- Original prefix codes, with no recursively duplicated subtree framing. -/
def termEncoding : Reset.Term ℕ ↪ List Bool := ⟨TermCode.encode, TermCode.encode_injective⟩

private abbrev Frame := Option (Reset.Term ℕ)
private abbrev Data := List Frame × (Frame × List Bool)
private abbrev frameEncoding (encoding : Reset.Term ℕ ↪ List Bool := termEncoding) := encOption encoding
private abbrev dataEncoding (encoding : Reset.Term ℕ ↪ List Bool := termEncoding) :=
  encPair (encList (frameEncoding encoding)) (encPair (frameEncoding encoding) encBits)
private abbrev stateEncoding (encoding : Reset.Term ℕ ↪ List Bool := termEncoding) :=
  encOption (dataEncoding encoding)

private def next : Data → Option Data
  | ([], (some t, word)) => some ([], (some t, word))
  | (none :: stack, (some t, word)) => some (some t :: stack, (none, word))
  | (some left :: stack, (some right, word)) =>
      some (stack, (some (Reset.Term.step left right), word))
  | (_, (none, [])) => none
  | (stack, (none, true :: word)) => some (none :: stack, (none, word))
  | (stack, (none, false :: word)) => do
      let (name, rest) ← unpair? word
      let j ← BinaryNatCode.decode? name
      return (stack, (some (.var j), rest))

private def step (state : Option Data) : Option Data := state.bind next

private def contextWord : List Frame → List Bool → List Bool
  | [], word => word
  | none :: stack, word => contextWord stack (true :: word)
  | some left :: stack, word => contextWord stack (true :: (TermCode.encode left ++ word))

private def focusWord (focus : Frame) : List Bool := focus.elim [] TermCode.encode

private def reconstruct (data : Data) : List Bool :=
  contextWord data.1 (focusWord data.2.1 ++ data.2.2)

private theorem next_reconstruct {data result : Data} (h : next data = some result) :
    reconstruct result = reconstruct data := by
  rcases data with ⟨stack, focus, word⟩
  cases focus with
  | some t =>
    cases stack with
    | nil => cases Option.some.inj h; rfl
    | cons f stack =>
      cases f with
      | none => cases Option.some.inj h; simp [reconstruct, contextWord, focusWord]
      | some left =>
        cases Option.some.inj h
        simp [reconstruct, contextWord, focusWord, TermCode.encode_step, List.append_assoc]
  | none =>
    cases word with
    | nil => simp only [next] at h; cases h
    | cons b word =>
      cases b with
      | true =>
        simp only [next] at h
        cases Option.some.inj h
        rfl
      | false =>
        simp only [next] at h
        obtain ⟨⟨name, rest⟩, hp, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨j, hj, he⟩ := Option.bind_eq_some_iff.mp h
        cases Option.some.inj he
        have hn := (BinaryNatCode.decode?_eq_some_iff name j).mp hj
        have hw := eq_delimit_append_of_unpair?_eq_some hp
        simp only [reconstruct, focusWord, Option.elim_some, Option.elim_none, List.nil_append,
          TermCode.encode_var, List.cons_append, ← hn, ← hw]

private def cost : Reset.Term ℕ → ℕ
  | .var _ => 1
  | .func .reset args => 3 + cost (args 0) + cost (args 1)

private theorem cost_step (s t : Reset.Term ℕ) :
    cost (Reset.Term.step s t) = 3 + cost s + cost t := by
  simp [cost, Reset.Term.step]

private theorem cost_le (t : Reset.Term ℕ) : cost t ≤ 3 * (TermCode.encode t).length := by
  induction t using Reset.Term.induction_reset with
  | var j => simp [cost, TermCode.encode_var]; omega
  | step s t hs ht =>
    simp only [cost_step, TermCode.encode_step, List.length_cons, List.length_append]
    omega

private theorem run_encode (t : Reset.Term ℕ) (stack : List Frame) (rest : List Bool) :
    step^[cost t] (some (stack, (none, TermCode.encode t ++ rest))) =
      some (stack, (some t, rest)) := by
  induction t using Reset.Term.induction_reset generalizing stack rest with
  | var j => simp [cost, step, next, TermCode.encode_var]
  | step s t hs ht =>
    have he : cost (Reset.Term.step s t) = 1 + cost t + 1 + cost s + 1 := by
      rw [cost_step]
      omega
    rw [he]
    simp only [Function.iterate_add_apply, Function.iterate_one]
    change step (step^[cost t] (step (step^[cost s]
      (step (some (stack, (none, TermCode.encode (Reset.Term.step s t) ++ rest))))))) = _
    simp only [TermCode.encode_step, List.cons_append, List.append_assoc, step, Option.bind_some, next]
    rw [hs]
    change step (step^[cost t] (some (some s :: stack, (none, TermCode.encode t ++ rest)))) = _
    rw [ht]
    rfl

private def finish (state : Option Data) : Option (Reset.Term ℕ) := do
  let data ← state
  if data.1.isEmpty && data.2.2.isEmpty then data.2.1 else none

private def parse (word : List Bool) : Option (Reset.Term ℕ) :=
  finish (step^[3 * word.length] (some ([], (none, word))))

private theorem step_done (t : Reset.Term ℕ) (rest : List Bool) (k : ℕ) :
    step^[k] (some ([], (some t, rest))) = some ([], (some t, rest)) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih]; rfl

private theorem parse_encode (t : Reset.Term ℕ) : parse (TermCode.encode t) = some t := by
  have he : 3 * (TermCode.encode t).length = (3 * (TermCode.encode t).length - cost t) + cost t :=
    (Nat.sub_add_cancel (cost_le t)).symm
  unfold parse
  rw [he, Function.iterate_add_apply]
  have hr := run_encode t [] []
  simp only [List.append_nil] at hr
  rw [hr, step_done]
  rfl

private theorem reconstruct_run (word : List Bool) (fuel : ℕ) (data : Data)
    (h : step^[fuel] (some ([], (none, word))) = some data) : reconstruct data = word := by
  induction fuel generalizing data with
  | zero => cases Option.some.inj h; rfl
  | succ fuel ih =>
    rw [Function.iterate_succ_apply'] at h
    cases hs : step^[fuel] (some ([], (none, word))) with
    | none => simp [hs, step] at h
    | some previous =>
      have hp := ih previous hs
      rw [hs] at h
      exact (next_reconstruct h).trans hp

private theorem encode_of_parse {word : List Bool} {t : Reset.Term ℕ} (h : parse word = some t) :
    TermCode.encode t = word := by
  unfold parse finish at h
  obtain ⟨data, hd, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  next hg =>
    obtain ⟨hs, hw⟩ := Bool.and_eq_true_iff.mp hg
    have hs := List.isEmpty_iff.mp hs
    have hw := List.isEmpty_iff.mp hw
    have hr := reconstruct_run word _ data hd
    simp only [reconstruct, hs, hw, contextWord, focusWord, h, Option.elim_some,
      List.append_nil] at hr
    exact hr
  next => cases h

private theorem parse_eq_decode (word : List Bool) : parse word = TermCode.decode word := by
  cases hp : parse word with
  | some t => rw [← encode_of_parse hp, TermCode.decode_encode]
  | none =>
    cases hd : TermCode.decode word with
    | none => rfl
    | some t =>
      have hw := TermCode.encode_of_decode hd
      rw [← hw, parse_encode] at hp
      cases hp


private theorem var_polyTime : ComputableInPolyTime (fun j : ℕ => (FirstOrder.Language.var j : Reset.Term ℕ))
    encNat termEncoding := by
  have h := bitsCons (const false) (Framing.delimit_polyTime.comp Dictionary.encode_polyTime)
  exact h.of_enc_eq (fun _ => rfl)

private theorem node_polyTime : ComputableInPolyTime
    (fun p : Reset.Term ℕ × Reset.Term ℕ => Reset.Term.step p.1 p.2)
    (encPair termEncoding termEncoding) termEncoding := by
  have hencode : ComputableInPolyTime TermCode.encode termEncoding encBits := .of_eq (fun _ => rfl)
  have h := bitsCons (const true)
    (bitsAppend (hencode.comp (fst _ _)) (hencode.comp (snd _ _)))
  exact h.of_enc_eq (fun _ => rfl)

private def leaf (data : Data) : Option Data :=
  (unpair? data.2.2.tail).elim none fun p =>
    (BinaryNatCode.decode? p.1).map fun j => (data.1, (some (.var j), p.2))

private theorem leaf_polyTime {encoding : Reset.Term ℕ ↪ List Bool}
    (hvar : ComputableInPolyTime (fun j : ℕ => (.var j : Reset.Term ℕ)) encNat encoding) : ComputableInPolyTime leaf (dataEncoding encoding) (stateEncoding encoding) := by
  have hstack : ComputableInPolyTime (fun p : Data × (List Bool × List Bool) => p.1.1)
      (encPair (dataEncoding encoding) (encPair encBits encBits)) (encList (frameEncoding encoding)) := by fun_prop
  have hrest : ComputableInPolyTime (fun p : Data × (List Bool × List Bool) => p.2.2)
      (encPair (dataEncoding encoding) (encPair encBits encBits)) encBits := by fun_prop
  have hname : ComputableInPolyTime (fun p : Data × (List Bool × List Bool) => p.2.1)
      (encPair (dataEncoding encoding) (encPair encBits encBits)) encBits := by fun_prop
  have hout : ComputableInPolyTime
      (fun p : (Data × (List Bool × List Bool)) × ℕ => (p.1.1.1, (some (.var p.2), p.1.2.2)))
      (encPair (encPair (dataEncoding encoding) (encPair encBits encBits)) encNat) (dataEncoding encoding) := by
    have hs : ComputableInPolyTime
        (fun p : (Data × (List Bool × List Bool)) × ℕ => p.1.1.1)
        (encPair (encPair (dataEncoding encoding) (encPair encBits encBits)) encNat) (encList (frameEncoding encoding)) := by fun_prop
    have hw : ComputableInPolyTime
        (fun p : (Data × (List Bool × List Bool)) × ℕ => p.1.2.2)
        (encPair (encPair (dataEncoding encoding) (encPair encBits encBits)) encNat) encBits := by fun_prop
    exact hs.prod (((optionSome encoding).comp (hvar.comp (snd _ _))).prod hw)
  have hinner := (Dictionary.decode_polyTime.comp hname).optionMapWithInput
    (f := fun (p : Data × (List Bool × List Bool)) (j : ℕ) =>
      ((p.1.1, (some (.var j), p.2.2)) : Data)) hout
  have hword : ComputableInPolyTime (fun data : Data => data.2.2) (dataEncoding encoding) encBits := by fun_prop
  have hp := Framing.unpair_polyTime.comp ((tail (encA := encBool) (encL := encBits)).comp hword)
  exact hp.optionElimWithInput (const none) hinner

private def nextFast (data : Data) : Option Data :=
  if data.2.1.isSome then
    if data.1.isEmpty then some data
    else if (data.1.headD none).isSome then
      some (data.1.tail,
        (some (Reset.Term.step ((data.1.headD none).getD (.var 0))
          (data.2.1.getD (.var 0))), data.2.2))
    else some (some (data.2.1.getD (.var 0)) :: data.1.tail, (none, data.2.2))
  else if data.2.2.isEmpty then none
  else if data.2.2.headD false then some (none :: data.1, (none, data.2.2.tail))
  else leaf data

private theorem nextFast_eq_next (data : Data) : nextFast data = next data := by
  rcases data with ⟨stack, focus, word⟩
  cases focus with
  | some t => cases stack with
    | nil => rfl
    | cons f stack => cases f <;> rfl
  | none => cases word with
    | nil => simp [nextFast, next]
    | cons b word =>
      cases b with
      | true => simp [nextFast, next]
      | false =>
        unfold nextFast leaf
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, List.isEmpty_cons,
          List.headD_cons, List.tail_cons]
        simp only [next]
        cases hp : unpair? word with
        | none => rfl
        | some p =>
          rcases p with ⟨name, rest⟩
          simp only [Option.elim_some]
          cases hj : BinaryNatCode.decode? name <;> simp [hj]

private theorem next_polyTime {encoding : Reset.Term ℕ ↪ List Bool}
    (hvar : ComputableInPolyTime (fun j : ℕ => (.var j : Reset.Term ℕ)) encNat encoding)
    (hnode : ComputableInPolyTime (fun p : Reset.Term ℕ × Reset.Term ℕ => Reset.Term.step p.1 p.2)
      (encPair encoding encoding) encoding) : ComputableInPolyTime next (dataEncoding encoding) (stateEncoding encoding) := by
  have hs := fst (encList (frameEncoding encoding)) (encPair (frameEncoding encoding) encBits)
  have hf : ComputableInPolyTime (fun data : Data => data.2.1) (dataEncoding encoding) (frameEncoding encoding) := by fun_prop
  have hw : ComputableInPolyTime (fun data : Data => data.2.2) (dataEncoding encoding) encBits := by fun_prop
  have htop := (headD (encA := (frameEncoding encoding)) none).comp hs
  have hleft := htop.optionGetDWithInput (const (.var 0))
  have hcurrent := hf.optionGetDWithInput (const (.var 0))
  have htail := (tail (encA := (frameEncoding encoding))).comp hs
  have hnew := (optionSome encoding).comp (hnode.comp (hleft.prod hcurrent))
  have hmerge := (optionSome (dataEncoding encoding)).comp (htail.prod (hnew.prod hw))
  have hpush := (optionSome (dataEncoding encoding)).comp
    ((cons' ((optionSome encoding).comp hcurrent) htail).prod ((const none).prod hw))
  have hreturn := htop.optionIsSome.ite hmerge hpush
  have hsempty := (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.listIsEmpty' (frameEncoding encoding))).comp hs
  have hsome := hsempty.ite (optionSome (dataEncoding encoding)) hreturn
  have hwempty := (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.bitsIsEmpty).comp hw
  have hwtail := (tail (encA := encBool) (encL := encBits)).comp hw
  have hbranch := (optionSome (dataEncoding encoding)).comp
    ((cons' (const none) hs).prod ((const none).prod hwtail))
  have hhead := (headD (encA := encBool) (encL := encBits) false).comp hw
  have hnone := hwempty.ite (const none) (hhead.ite hbranch (leaf_polyTime hvar))
  have h := hf.optionIsSome.ite hsome hnone
  convert h using 1
  funext data
  exact (nextFast_eq_next data).symm

private theorem step_polyTime {encoding : Reset.Term ℕ ↪ List Bool}
    (hvar : ComputableInPolyTime (fun j : ℕ => (.var j : Reset.Term ℕ)) encNat encoding)
    (hnode : ComputableInPolyTime (fun p : Reset.Term ℕ × Reset.Term ℕ => Reset.Term.step p.1 p.2)
      (encPair encoding encoding) encoding) : ComputableInPolyTime step (stateEncoding encoding) (stateEncoding encoding) := by
  have h := (id' (encIn := (stateEncoding encoding))).optionElimWithInput
    (body := fun (_ : Option Data) (data : Data) => next data) (const none)
    ((next_polyTime hvar hnode).comp (snd (stateEncoding encoding) (dataEncoding encoding)))
  convert h using 1
  funext state
  cases state <;> rfl


private theorem contextWord_length (stack : List Frame) (word : List Bool) :
    (contextWord stack word).length = (contextWord stack []).length + word.length := by
  induction stack generalizing word with
  | nil => simp [contextWord]
  | cons frame stack ih =>
    cases frame with
    | none =>
      simp only [contextWord]
      rw [ih (true :: word), ih [true]]
      simp only [List.length_cons, List.length_nil]
      omega
    | some t =>
      simp only [contextWord]
      rw [ih (true :: (TermCode.encode t ++ word)), ih (true :: (TermCode.encode t ++ []))]
      simp only [List.length_cons, List.length_append, List.length_nil]
      omega

private theorem stack_length_le (stack : List Frame) :
    (encList frameEncoding stack).length ≤ 3 * (contextWord stack []).length := by
  induction stack with
  | nil => rfl
  | cons frame stack ih =>
    cases frame with
    | none =>
      rw [contextWord, contextWord_length stack [true]]
      simp only [encList_cons, List.length_append, length_frame, frameEncoding, encOption_none,
        List.length_nil, List.length_cons]
      change (encList (encOption termEncoding) stack).length ≤ _ at ih
      omega
    | some t =>
      rw [contextWord, contextWord_length stack (true :: (TermCode.encode t ++ []))]
      simp only [encList_cons, List.length_append, length_frame, frameEncoding, encOption_some,
        List.length_cons, List.length_nil]
      change (encList (encOption termEncoding) stack).length ≤ _ at ih
      change 2 * ((TermCode.encode t).length + 1) + 1 +
        (encList (encOption termEncoding) stack).length ≤ _
      omega

private theorem data_length_le (data : Data) :
    (stateEncoding termEncoding (some data)).length ≤ 6 * (reconstruct data).length + 5 := by
  rcases data with ⟨stack, focus, word⟩
  have hs := stack_length_le stack
  change (encList (encOption termEncoding) stack).length ≤ _ at hs
  have hr := contextWord_length stack (focusWord focus ++ word)
  simp only [List.length_append] at hr
  simp only [stateEncoding, encOption_some, List.length_cons, dataEncoding, length_encPair,
    encBits_apply]
  cases focus with
  | none =>
    simp only [frameEncoding, encOption_none, List.length_nil, focusWord, Option.elim_none] at hr ⊢
    change _ ≤ 6 * (contextWord stack ([] ++ word)).length + 5
    omega
  | some t =>
    simp only [frameEncoding, encOption_some, List.length_cons, focusWord, Option.elim_some] at hr ⊢
    change _ ≤ 6 * (contextWord stack (TermCode.encode t ++ word)).length + 5
    change _ + (2 * ((TermCode.encode t).length + 1) + 1 + word.length) + 1 ≤ _
    omega

private def invariant (word : List Bool) (_ : ℕ) (state : Option Data) : Prop :=
  ∀ data, state = some data → reconstruct data = word

private theorem invariant_step (word : List Bool) (i : ℕ) (state : Option Data)
    (h : invariant word i state) : invariant word (i + 1) (step state) := by
  intro data he
  cases hs : state with
  | none => simp [hs, step] at he
  | some previous =>
    have hp := h previous hs
    rw [hs] at he
    exact (next_reconstruct he).trans hp

private theorem finish_polyTime (encoding : Reset.Term ℕ ↪ List Bool) : ComputableInPolyTime finish (stateEncoding encoding) (encOption encoding) := by
  let input := encPair (stateEncoding encoding) (dataEncoding encoding)
  have hs : ComputableInPolyTime (fun p : Option Data × Data => p.2.1) input (encList (frameEncoding encoding)) := by fun_prop
  have hw : ComputableInPolyTime (fun p : Option Data × Data => p.2.2.2) input encBits := by fun_prop
  have hf : ComputableInPolyTime (fun p : Option Data × Data => p.2.2.1) input (frameEncoding encoding) := by fun_prop
  have hsEmpty := (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.listIsEmpty' (frameEncoding encoding))).comp hs
  have hcondition := bool_and' hsEmpty (bitsIsEmpty.comp hw)
  have hbody := hcondition.ite hf (const none)
  have h := (id' (encIn := (stateEncoding encoding))).optionElimWithInput
    (body := fun (_ : Option Data) data =>
      if data.1.isEmpty && data.2.2.isEmpty then data.2.1 else none) (const none) hbody
  convert h using 1
  funext state
  cases state <;> rfl

/-- The actual original binary tree decoder has a polynomial-time machine.
The stack parser preserves the whole original code, uses a bit-length clock,
and rejects malformed names, unfinished trees and trailing bits. -/
@[fun_prop] theorem decode_polyTime : ComputableInPolyTime TermCode.decode encBits
    (encOption termEncoding) := by
  have hcount : ComputableInPolyTime (fun word : List Bool => 3 * word.length) encBits encUnary := by
    have h := length_bits.comp (bitsAppend (bitsAppend id' id') id')
    convert h using 1
    funext word
    simp only [Function.comp_def, List.length_append]
    omega
  have hstart : ComputableInPolyTime (fun word : List Bool => some ([], (none, word)))
      encBits stateEncoding :=
    (optionSome dataEncoding).comp ((const []).prod ((const none).prod id'))
  have hsize : PolyBounded (fun word : List Bool => word.length) (fun word => 6 * word.length + 5) :=
    ((PolyBounded.const 6).mul PolyBounded.self).add (.const 5)
  have hloop := ComputableInPolyTime.iterate_spec (count := fun word : List Bool => 3 * word.length)
    (step := step) hcount hstart (step_polyTime var_polyTime node_polyTime) invariant
    (fun word data he => by cases Option.some.inj he; rfl)
    (fun word i state _ h => invariant_step word i state h) hsize
    (fun word i state _ h => by
      cases hs : state with
      | none => simp
      | some data =>
        have he := h data hs
        exact he ▸ data_length_le data)
  have h := (finish_polyTime termEncoding).comp hloop.1
  convert h using 1
  funext word
  exact (parse_eq_decode word).symm


private theorem stack_storage_le (encoding : Reset.Term ℕ ↪ List Bool) (C degree : ℕ)
    (hstorage : ∀ t, (encoding t).length ≤ C * ((TermCode.encode t).length + 1) ^ degree)
    (stack : List Frame) (N : ℕ) (hN : (contextWord stack []).length ≤ N) :
    (encList (frameEncoding encoding) stack).length ≤
      (3 + 2 * (C * (N + 1) ^ degree)) * (contextWord stack []).length := by
  induction stack with
  | nil => simp [contextWord]
  | cons frame stack ih =>
    cases frame with
    | none =>
      have hlen : (contextWord (none :: stack) []).length = (contextWord stack []).length + 1 := by
        rw [contextWord, contextWord_length]
        simp
      have hi := ih (by omega)
      change (encList (encOption encoding) stack).length ≤ _ at hi
      simp only [encList_cons, List.length_append, length_frame, frameEncoding, encOption_none,
        List.length_nil]
      rw [hlen]
      simp only [Nat.mul_add, Nat.mul_one]
      omega
    | some t =>
      have hlen : (contextWord (some t :: stack) []).length =
          (contextWord stack []).length + 1 + (TermCode.encode t).length := by
        rw [contextWord, contextWord_length]
        simp
        omega
      have hi := ih (by omega)
      have he : (encoding t).length ≤ C * (N + 1) ^ degree :=
        (hstorage t).trans (by gcongr; omega)
      simp only [encList_cons, List.length_append, length_frame, frameEncoding, encOption_some,
        List.length_cons]
      rw [hlen]
      nlinarith

private theorem data_storage_le (encoding : Reset.Term ℕ ↪ List Bool) (C degree : ℕ)
    (hstorage : ∀ t, (encoding t).length ≤ C * ((TermCode.encode t).length + 1) ^ degree)
    (data : Data) :
    (stateEncoding encoding (some data)).length ≤
      2 * (3 + 2 * (C * ((reconstruct data).length + 1) ^ degree)) * (reconstruct data).length +
      2 * (C * ((reconstruct data).length + 1) ^ degree + 1) + (reconstruct data).length + 3 := by
  rcases data with ⟨stack, focus, word⟩
  let N := (reconstruct (stack, focus, word)).length
  have htotal : N = (contextWord stack []).length + (focusWord focus).length + word.length := by
    change (contextWord stack (focusWord focus ++ word)).length = _
    rw [contextWord_length, List.length_append]
    omega
  have hs := stack_storage_le encoding C degree hstorage stack N (by omega)
  have hs' : (encList (frameEncoding encoding) stack).length ≤ (3 + 2 * (C * (N + 1) ^ degree)) * N :=
    hs.trans (Nat.mul_le_mul_left _ (by omega))
  have hf : (frameEncoding encoding focus).length ≤ C * (N + 1) ^ degree + 1 := by
    cases focus with
    | none => simp [frameEncoding]
    | some t =>
      have ht : (TermCode.encode t).length ≤ N := by
        simp only [focusWord, Option.elim_some] at htotal
        omega
      have he := (hstorage t).trans (show C * ((TermCode.encode t).length + 1) ^ degree ≤
          C * (N + 1) ^ degree by gcongr)
      simpa only [frameEncoding, encOption_some, List.length_cons] using Nat.add_le_add_right he 1
  change _ ≤ 2 * (3 + 2 * (C * (N + 1) ^ degree)) * N + 2 * (C * (N + 1) ^ degree + 1) + N + 3
  simp only [stateEncoding, encOption_some, List.length_cons, dataEncoding, length_encPair, encBits_apply]
  simp only [Nat.mul_assoc]
  omega

/-- A charged bottom-up evaluation rule for the original prefix language.
One may store a term together with computed annotations. Uniform leaf and
binary-node machines construct that representation, and the polynomial bound
charges all annotations, captured data and intermediate parser stack values.
The result remains the actual original decoder on every bit word. -/
theorem decode_polyTime_of_storage (encoding : Reset.Term ℕ ↪ List Bool)
    (hvar : ComputableInPolyTime (fun j : ℕ => (.var j : Reset.Term ℕ)) encNat encoding)
    (hnode : ComputableInPolyTime (fun p : Reset.Term ℕ × Reset.Term ℕ => Reset.Term.step p.1 p.2)
      (encPair encoding encoding) encoding)
    (C degree : ℕ)
    (hstorage : ∀ t, (encoding t).length ≤ C * ((TermCode.encode t).length + 1) ^ degree) :
    ComputableInPolyTime TermCode.decode encBits (encOption encoding) := by
  have hcount : ComputableInPolyTime (fun word : List Bool => 3 * word.length) encBits encUnary := by
    have h := length_bits.comp (bitsAppend (bitsAppend id' id') id')
    convert h using 1
    funext word
    simp only [Function.comp_def, List.length_append]
    omega
  have hstart : ComputableInPolyTime (fun word : List Bool => some ([], (none, word)))
      encBits (stateEncoding encoding) :=
    (optionSome (dataEncoding encoding)).comp ((const []).prod ((const none).prod id'))
  have hq : PolyBounded (fun word : List Bool => word.length)
      (fun word => C * (word.length + 1) ^ degree) :=
    (PolyBounded.const C).mul ((PolyBounded.self.add (.const 1)).pow degree)
  have hsize := ((PolyBounded.const 2).mul ((PolyBounded.const 3).add ((PolyBounded.const 2).mul hq))).mul
    PolyBounded.self |>.add (((PolyBounded.const 2).mul (hq.add (.const 1))).add PolyBounded.self |>.add (.const 3))
  have hloop := ComputableInPolyTime.iterate_spec (count := fun word : List Bool => 3 * word.length)
    (step := step) hcount hstart (step_polyTime hvar hnode) invariant
    (fun word data he => by cases Option.some.inj he; rfl)
    (fun word i state _ h => invariant_step word i state h) hsize
    (fun word i state _ h => by
      cases hs : state with
      | none => simp
      | some data =>
        have he := h data hs
        have hb := data_storage_le encoding C degree hstorage data
        simpa only [he, Nat.add_assoc] using hb)
  have h := (finish_polyTime encoding).comp hloop.1
  convert h using 1
  funext word
  exact (parse_eq_decode word).symm


/-- Bottom-up evaluation of reset syntax is polynomial-time whenever its
uniform leaf and binary algebra operations are certified and its complete
result storage has a proved polynomial bound in the original binary code.
The parser charges every intermediate annotated subtree and stack frame. -/
theorem fold_polyTime {Value : Type} (valueEncoding : Value ↪ List Bool)
    (fold : Reset.Term ℕ → Value) (leaf : ℕ → Value) (node : Value × Value → Value)
    (hvar : ∀ j, fold (.var j) = leaf j)
    (hstep : ∀ s t, fold (Reset.Term.step s t) = node (fold s, fold t))
    (hleaf : ComputableInPolyTime leaf encNat valueEncoding)
    (hnode : ComputableInPolyTime node (encPair valueEncoding valueEncoding) valueEncoding)
    (C degree : ℕ)
    (hstorage : ∀ t, (valueEncoding (fold t)).length ≤ C * ((TermCode.encode t).length + 1) ^ degree) :
    ComputableInPolyTime fold termEncoding valueEncoding := by
  let pairEncoding := encPair termEncoding valueEncoding
  let encoding : Reset.Term ℕ ↪ List Bool :=
    ⟨fun t => pairEncoding (t, fold t), fun s t he =>
      congrArg Prod.fst (pairEncoding.injective he)⟩
  have hread : ComputableInPolyTime (fun t => (t, fold t)) encoding pairEncoding := .of_eq (fun _ => rfl)
  have hsyntax : ComputableInPolyTime (fun t : Reset.Term ℕ => t) encoding termEncoding :=
    (fst _ _).comp hread
  have hvalue : ComputableInPolyTime fold encoding valueEncoding := (snd _ _).comp hread
  have hleafCache : ComputableInPolyTime (fun j : ℕ => (.var j : Reset.Term ℕ)) encNat encoding := by
    have h := var_polyTime.prod hleaf
    apply h.of_enc_eq
    intro j
    change pairEncoding (.var j, fold (.var j)) = _
    rw [hvar]
  have hnodeCache : ComputableInPolyTime
      (fun p : Reset.Term ℕ × Reset.Term ℕ => Reset.Term.step p.1 p.2)
      (encPair encoding encoding) encoding := by
    have hleft := fst encoding encoding
    have hright := snd encoding encoding
    have hs := node_polyTime.comp ((hsyntax.comp hleft).prod (hsyntax.comp hright))
    have hv := hnode.comp ((hvalue.comp hleft).prod (hvalue.comp hright))
    have h := hs.prod hv
    apply h.of_enc_eq
    intro p
    change pairEncoding (Reset.Term.step p.1 p.2, fold (Reset.Term.step p.1 p.2)) = _
    rw [hstep]
    rfl
  have hbound (t : Reset.Term ℕ) :
      (encoding t).length ≤ (C + 3) * ((TermCode.encode t).length + 1) ^ (degree + 1) := by
    let N := (TermCode.encode t).length
    let q := (N + 1) ^ degree
    have hq : 1 ≤ q := Nat.one_le_pow degree _ (by omega)
    have hNq : N + 1 ≤ q * (N + 1) := by nlinarith
    have hqq : q ≤ q * (N + 1) := by nlinarith
    have hb := hstorage t
    change (valueEncoding (fold t)).length ≤ C * q at hb
    change (pairEncoding (t, fold t)).length ≤ _
    simp only [pairEncoding, length_encPair]
    change 2 * N + 1 + (valueEncoding (fold t)).length ≤ (C + 3) * (N + 1) ^ (degree + 1)
    rw [pow_succ]
    change _ ≤ (C + 3) * (q * (N + 1))
    have hh := Nat.mul_le_mul_left C hqq
    have hn := Nat.mul_le_mul_left 3 hNq
    nlinarith
  have hdecode := decode_polyTime_of_storage encoding hleafCache hnodeCache (C + 3) (degree + 1) hbound
  have hencode : ComputableInPolyTime TermCode.encode termEncoding encBits := .of_eq (fun _ => rfl)
  have hcache := (hdecode.comp hencode).optionGetDWithInput (const (.var 0))
  have hid : ComputableInPolyTime (fun t : Reset.Term ℕ => t) termEncoding encoding := by
    convert hcache using 1
    funext t
    simp only [Function.comp_def, TermCode.decode_encode, Option.getD_some]
  exact hvalue.comp hid

end KFOL.Complexity.TermMachine
