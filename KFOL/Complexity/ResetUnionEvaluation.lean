module

public import KFOL.Complexity.ResetUnionMachines

/-! # Uniform native evaluation of reset/union trees in bounded algebras -/

@[expose] public section

namespace KFOL.Complexity.ResetUnionEvaluation

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.ResetUnion KFOL.Words

section Algebra

variable {Context Value : Type}

/-- Ordinary algebraic tree evaluation, independent of the machine stack. -/
def fold (leaf : Context → ℕ → Value) (reset union : Value → Value → Value)
    (context : Context) : KFOL.ResetUnion.Term ℕ → Value
  | .var j => leaf context j
  | .func .reset args => reset (fold leaf reset union context (args 0)) (fold leaf reset union context (args 1))
  | .func .union args => union (fold leaf reset union context (args 0)) (fold leaf reset union context (args 1))


@[simp] theorem fold_var (leaf : Context → ℕ → Value) (reset union : Value → Value → Value)
    (context : Context) (j : ℕ) : fold leaf reset union context (.var j) = leaf context j := rfl

@[simp] theorem fold_reset (leaf : Context → ℕ → Value) (reset union : Value → Value → Value)
    (context : Context) (s t : KFOL.ResetUnion.Term ℕ) :
    fold leaf reset union context (s.reset t) = reset (fold leaf reset union context s) (fold leaf reset union context t) := by
  simp [fold, Term.reset]

@[simp] theorem fold_union (leaf : Context → ℕ → Value) (reset union : Value → Value → Value)
    (context : Context) (s t : KFOL.ResetUnion.Term ℕ) :
    fold leaf reset union context (s.union t) = union (fold leaf reset union context s) (fold leaf reset union context t) := by
  simp [fold, Term.union]


/-- The captured-context evaluator is the ordinary algebraic valuation fold. -/
theorem fold_function (leaf : Context → ℕ → Value) (reset union : Value → Value → Value)
    (context : Context) (t : KFOL.ResetUnion.Term ℕ) :
    fold leaf reset union context t =
      fold (fun (valuation : ℕ → Value) j => valuation j) reset union (leaf context) t := by
  induction t using Term.induction_binary with
  | var j => rfl
  | reset s t hs ht => rw [fold_reset, fold_reset, hs, ht]
  | union s t hs ht => rw [fold_union, fold_union, hs, ht]

private abbrev Frame := Bool × Option Value
private abbrev Data := List (Frame (Value := Value)) × (Option Value × List Bool)
private abbrev frameEncoding (valueEncoding : Value ↪ List Bool) := encPair encBool (encOption valueEncoding)
private abbrev dataEncoding (valueEncoding : Value ↪ List Bool) :=
  encPair (encList (frameEncoding valueEncoding)) (encPair (encOption valueEncoding) encBits)
private abbrev stateEncoding (valueEncoding : Value ↪ List Bool) := encOption (dataEncoding valueEncoding)

private def next (leaf : Context → ℕ → Value) (reset union : Value → Value → Value)
    (context : Context) : Data (Value := Value) → Option (Data (Value := Value))
  | ([], (some value, word)) => some ([], (some value, word))
  | ((operation, none) :: stack, (some value, word)) => some ((operation, some value) :: stack, (none, word))
  | ((operation, some left) :: stack, (some right, word)) =>
      some (stack, (some (if operation then union left right else reset left right), word))
  | (_, (none, [])) => none
  | (stack, (none, false :: word)) => do
      let (name, rest) ← unpair? word
      let j ← BinaryNatCode.decode? name
      return (stack, (some (leaf context j), rest))
  | (_, (none, true :: [])) => none
  | (stack, (none, true :: operation :: word)) => some ((operation, none) :: stack, (none, word))

private def step (leaf : Context → ℕ → Value) (reset union : Value → Value → Value)
    (context : Context) (state : Option (Data (Value := Value))) : Option (Data (Value := Value)) :=
  state.bind (next leaf reset union context)

private def cost : KFOL.ResetUnion.Term ℕ → ℕ
  | .var _ => 1
  | .func .reset args => 3 + cost (args 0) + cost (args 1)
  | .func .union args => 3 + cost (args 0) + cost (args 1)

private theorem cost_reset (s t : KFOL.ResetUnion.Term ℕ) : cost (s.reset t) = 3 + cost s + cost t := by
  simp [cost, Term.reset]

private theorem cost_union (s t : KFOL.ResetUnion.Term ℕ) : cost (s.union t) = 3 + cost s + cost t := by
  simp [cost, Term.union]

private theorem cost_le (t : KFOL.ResetUnion.Term ℕ) : cost t ≤ 3 * (Code.encode t).length := by
  induction t using Term.induction_binary with
  | var j => simp [cost, Code.encode_var]; omega
  | reset s t hs ht => simp only [cost_reset, Code.encode_reset, List.length_cons, List.length_append]; omega
  | union s t hs ht => simp only [cost_union, Code.encode_union, List.length_cons, List.length_append]; omega

private theorem run_encode (leaf : Context → ℕ → Value) (reset union : Value → Value → Value)
    (context : Context) (t : KFOL.ResetUnion.Term ℕ) (stack : List (Frame (Value := Value))) (rest : List Bool) :
    (step leaf reset union context)^[cost t] (some (stack, (none, Code.encode t ++ rest))) =
      some (stack, (some (fold leaf reset union context t), rest)) := by
  induction t using Term.induction_binary generalizing stack rest with
  | var j => simp [cost, step, next, Code.encode_var, fold]
  | reset s t hs ht =>
    have he : cost (s.reset t) = 1 + cost t + 1 + cost s + 1 := by rw [cost_reset]; omega
    rw [he]
    simp only [Function.iterate_add_apply, Function.iterate_one]
    change step leaf reset union context ((step leaf reset union context)^[cost t]
      (step leaf reset union context ((step leaf reset union context)^[cost s]
        (step leaf reset union context (some (stack, (none, Code.encode (s.reset t) ++ rest))))))) = _
    simp only [Code.encode_reset, List.cons_append, List.append_assoc, step, Option.bind_some, next]
    rw [hs]
    change step leaf reset union context ((step leaf reset union context)^[cost t]
      (some ((false, some (fold leaf reset union context s)) :: stack, (none, Code.encode t ++ rest)))) = _
    rw [ht]
    simp [step, next, fold, Term.reset]
  | union s t hs ht =>
    have he : cost (s.union t) = 1 + cost t + 1 + cost s + 1 := by rw [cost_union]; omega
    rw [he]
    simp only [Function.iterate_add_apply, Function.iterate_one]
    change step leaf reset union context ((step leaf reset union context)^[cost t]
      (step leaf reset union context ((step leaf reset union context)^[cost s]
        (step leaf reset union context (some (stack, (none, Code.encode (s.union t) ++ rest))))))) = _
    simp only [Code.encode_union, List.cons_append, List.append_assoc, step, Option.bind_some, next]
    rw [hs]
    change step leaf reset union context ((step leaf reset union context)^[cost t]
      (some ((true, some (fold leaf reset union context s)) :: stack, (none, Code.encode t ++ rest)))) = _
    rw [ht]
    simp [step, next, fold, Term.union]

private theorem step_done (leaf : Context → ℕ → Value) (reset union : Value → Value → Value)
    (context : Context) (value : Value) (rest : List Bool) (k : ℕ) :
    (step leaf reset union context)^[k] (some ([], (some value, rest))) = some ([], (some value, rest)) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih]; rfl

private def evaluateWord (leaf : Context → ℕ → Value) (reset union : Value → Value → Value)
    (fallback : Value) (p : Context × List Bool) : Value :=
  (((step leaf reset union p.1)^[3 * p.2.length] (some ([], (none, p.2)))).getD ([], (none, []))).2.1.getD fallback

private theorem evaluateWord_encode (leaf : Context → ℕ → Value) (reset union : Value → Value → Value)
    (fallback : Value) (context : Context) (t : KFOL.ResetUnion.Term ℕ) :
    evaluateWord leaf reset union fallback (context, Code.encode t) = fold leaf reset union context t := by
  have he : 3 * (Code.encode t).length = (3 * (Code.encode t).length - cost t) + cost t :=
    (Nat.sub_add_cancel (cost_le t)).symm
  unfold evaluateWord
  rw [he, Function.iterate_add_apply]
  have hr := run_encode leaf reset union context t [] []
  simp only [List.append_nil] at hr
  rw [hr, step_done]
  rfl


private def leafData (leaf : Context → ℕ → Value) (p : Context × Data (Value := Value)) :
    Option (Data (Value := Value)) :=
  (unpair? p.2.2.2.tail).elim none fun pair =>
    (BinaryNatCode.decode? pair.1).map fun j => (p.2.1, (some (leaf p.1 j), pair.2))

private theorem leafData_polyTime (contextEncoding : Context ↪ List Bool) (valueEncoding : Value ↪ List Bool)
    (leaf : Context → ℕ → Value)
    (hleaf : ComputableInPolyTime (fun p : Context × ℕ => leaf p.1 p.2)
      (encPair contextEncoding encNat) valueEncoding) :
    ComputableInPolyTime (leafData leaf) (encPair contextEncoding (dataEncoding valueEncoding))
      (stateEncoding valueEncoding) := by
  let input := encPair contextEncoding (dataEncoding valueEncoding)
  let pairEncoding := encPair encBits encBits
  have hword : ComputableInPolyTime (fun p : Context × Data (Value := Value) => p.2.2.2) input encBits := by fun_prop
  have hp := Framing.unpair_polyTime.comp ((tail (encA := encBool) (encL := encBits)).comp hword)
  have hname : ComputableInPolyTime
      (fun p : (Context × Data (Value := Value)) × (List Bool × List Bool) => p.2.1)
      (encPair input pairEncoding) encBits := by fun_prop
  have hc : ComputableInPolyTime
      (fun p : ((Context × Data (Value := Value)) × (List Bool × List Bool)) × ℕ => p.1.1.1)
      (encPair (encPair input pairEncoding) encNat) contextEncoding := by fun_prop
  have hs : ComputableInPolyTime
      (fun p : ((Context × Data (Value := Value)) × (List Bool × List Bool)) × ℕ => p.1.1.2.1)
      (encPair (encPair input pairEncoding) encNat) (encList (frameEncoding valueEncoding)) := by fun_prop
  have hr : ComputableInPolyTime
      (fun p : ((Context × Data (Value := Value)) × (List Bool × List Bool)) × ℕ => p.1.2.2)
      (encPair (encPair input pairEncoding) encNat) encBits := by fun_prop
  have hv := hleaf.comp (hc.prod (snd _ _))
  have hout := hs.prod (((optionSome valueEncoding).comp hv).prod hr)
  have hinner := (Dictionary.decode_polyTime.comp hname).optionMapWithInput
    (f := fun (p : (Context × Data (Value := Value)) × (List Bool × List Bool)) (j : ℕ) =>
      ((p.1.2.1, (some (leaf p.1.1 j), p.2.2)) : Data (Value := Value))) hout
  exact hp.optionElimWithInput (const none) hinner

private def nextFast (leaf : Context → ℕ → Value) (reset union : Value → Value → Value)
    (fallback : Value) (p : Context × Data (Value := Value)) : Option (Data (Value := Value)) :=
  let data := p.2
  if data.2.1.isSome then
    if data.1.isEmpty then some data
    else if (data.1.headD (false, none)).2.isSome then
      let left := (data.1.headD (false, none)).2.getD fallback
      let right := data.2.1.getD fallback
      some (data.1.tail,
        (some (if (data.1.headD (false, none)).1 then union left right else reset left right), data.2.2))
    else some (((data.1.headD (false, none)).1, some (data.2.1.getD fallback)) :: data.1.tail, (none, data.2.2))
  else if data.2.2.isEmpty then none
  else if data.2.2.headD false then
    if data.2.2.tail.isEmpty then none
    else some ((data.2.2.tail.headD false, none) :: data.1, (none, data.2.2.tail.tail))
  else leafData leaf p

private theorem nextFast_eq_next (leaf : Context → ℕ → Value) (reset union : Value → Value → Value)
    (fallback : Value) (p : Context × Data (Value := Value)) :
    nextFast leaf reset union fallback p = next leaf reset union p.1 p.2 := by
  rcases p with ⟨context, stack, focus, word⟩
  cases focus with
  | some value =>
    cases stack with
    | nil => rfl
    | cons frame stack =>
      rcases frame with ⟨operation, left⟩
      cases left <;> rfl
  | none =>
    cases word with
    | nil => simp [nextFast, next]
    | cons b word =>
      cases b with
      | true => cases word <;> simp [nextFast, next]
      | false =>
        unfold nextFast leafData
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, List.isEmpty_cons,
          List.headD_cons, List.tail_cons]
        simp only [next]
        cases hp : unpair? word with
        | none => rfl
        | some pair =>
          rcases pair with ⟨name, rest⟩
          simp only [Option.elim_some]
          cases hn : BinaryNatCode.decode? name <;> simp [hn]

private theorem next_polyTime (contextEncoding : Context ↪ List Bool) (valueEncoding : Value ↪ List Bool)
    (leaf : Context → ℕ → Value) (reset union : Value → Value → Value) (fallback : Value)
    (hleaf : ComputableInPolyTime (fun p : Context × ℕ => leaf p.1 p.2)
      (encPair contextEncoding encNat) valueEncoding)
    (hreset : ComputableInPolyTime (fun p : Value × Value => reset p.1 p.2)
      (encPair valueEncoding valueEncoding) valueEncoding)
    (hunion : ComputableInPolyTime (fun p : Value × Value => union p.1 p.2)
      (encPair valueEncoding valueEncoding) valueEncoding) :
    ComputableInPolyTime (fun p : Context × Data (Value := Value) => next leaf reset union p.1 p.2)
      (encPair contextEncoding (dataEncoding valueEncoding)) (stateEncoding valueEncoding) := by
  let input := encPair contextEncoding (dataEncoding valueEncoding)
  have hs : ComputableInPolyTime (fun p : Context × Data (Value := Value) => p.2.1)
      input (encList (frameEncoding valueEncoding)) := by fun_prop
  have hf : ComputableInPolyTime (fun p : Context × Data (Value := Value) => p.2.2.1)
      input (encOption valueEncoding) := by fun_prop
  have hw : ComputableInPolyTime (fun p : Context × Data (Value := Value) => p.2.2.2) input encBits := by fun_prop
  have htop := (headD (encA := frameEncoding valueEncoding) (false, none)).comp hs
  have hop := (fst encBool (encOption valueEncoding)).comp htop
  have hleftOption := (snd encBool (encOption valueEncoding)).comp htop
  have hleft := hleftOption.optionGetDWithInput (const fallback)
  have hright := hf.optionGetDWithInput (const fallback)
  have hresult := hop.ite (hunion.comp (hleft.prod hright)) (hreset.comp (hleft.prod hright))
  have htail := (tail (encA := frameEncoding valueEncoding)).comp hs
  have hmerge := (optionSome (dataEncoding valueEncoding)).comp
    (htail.prod (((optionSome valueEncoding).comp hresult).prod hw))
  have hpush := (optionSome (dataEncoding valueEncoding)).comp
    ((cons' (hop.prod ((optionSome valueEncoding).comp hright)) htail).prod ((const none).prod hw))
  have hsome := ((ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.listIsEmpty' (frameEncoding valueEncoding))).comp hs).ite
    ((optionSome (dataEncoding valueEncoding)).comp (snd contextEncoding _))
    (hleftOption.optionIsSome.ite hmerge hpush)
  have hwtail := (tail (encA := encBool) (encL := encBits)).comp hw
  have hoperator := (headD (encA := encBool) (encL := encBits) false).comp hwtail
  have hrest := (tail (encA := encBool) (encL := encBits)).comp hwtail
  have hbranch := (optionSome (dataEncoding valueEncoding)).comp
    ((cons' (hoperator.prod (const none)) hs).prod ((const none).prod hrest))
  have hnode := (bitsIsEmpty.comp hwtail).ite (const none) hbranch
  have hnone := (bitsIsEmpty.comp hw).ite (const none)
    (((headD (encA := encBool) (encL := encBits) false).comp hw).ite hnode
      (leafData_polyTime contextEncoding valueEncoding leaf hleaf))
  have h := hf.optionIsSome.ite hsome hnone
  convert h using 1
  funext p
  exact (nextFast_eq_next leaf reset union fallback p).symm

private theorem step_polyTime (contextEncoding : Context ↪ List Bool) (valueEncoding : Value ↪ List Bool)
    (leaf : Context → ℕ → Value) (reset union : Value → Value → Value) (fallback : Value)
    (hleaf : ComputableInPolyTime (fun p : Context × ℕ => leaf p.1 p.2)
      (encPair contextEncoding encNat) valueEncoding)
    (hreset : ComputableInPolyTime (fun p : Value × Value => reset p.1 p.2)
      (encPair valueEncoding valueEncoding) valueEncoding)
    (hunion : ComputableInPolyTime (fun p : Value × Value => union p.1 p.2)
      (encPair valueEncoding valueEncoding) valueEncoding) :
    ComputableInPolyTime (fun p : Context × Option (Data (Value := Value)) => step leaf reset union p.1 p.2)
      (encPair contextEncoding (stateEncoding valueEncoding)) (stateEncoding valueEncoding) := by
  let input := encPair contextEncoding (stateEncoding valueEncoding)
  have hc : ComputableInPolyTime (fun p : (Context × Option (Data (Value := Value))) × Data (Value := Value) => p.1.1)
      (encPair input (dataEncoding valueEncoding)) contextEncoding := by fun_prop
  have hd := snd input (dataEncoding valueEncoding)
  have hbody := (next_polyTime contextEncoding valueEncoding leaf reset union fallback hleaf hreset hunion).comp
    (hc.prod hd)
  have h := (snd contextEncoding (stateEncoding valueEncoding)).optionElimWithInput
    (body := fun (p : Context × Option (Data (Value := Value))) data => next leaf reset union p.1 data)
    (const none) hbody
  convert h using 1
  funext p
  cases p.2 <;> rfl


private def weight (data : Data (Value := Value)) : ℕ := data.1.length + data.2.2.length

private theorem next_weight (leaf : Context → ℕ → Value) (reset union : Value → Value → Value)
    (context : Context) {data result : Data (Value := Value)}
    (h : next leaf reset union context data = some result) : weight result ≤ weight data := by
  rcases data with ⟨stack, focus, word⟩
  cases focus with
  | some value =>
    cases stack with
    | nil => cases Option.some.inj h; rfl
    | cons frame stack =>
      rcases frame with ⟨operation, left⟩
      cases left <;> cases Option.some.inj h <;> simp [weight]
  | none =>
    cases word with
    | nil => simp only [next] at h; cases h
    | cons b word =>
      cases b with
      | false =>
        simp only [next] at h
        obtain ⟨⟨name, rest⟩, hp, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨j, hj, he⟩ := Option.bind_eq_some_iff.mp h
        cases Option.some.inj he
        have hw := eq_delimit_append_of_unpair?_eq_some hp
        have hrest : rest.length ≤ word.length := by rw [hw]; simp
        simp only [weight, List.length_cons]
        omega
      | true =>
        cases word with
        | nil => simp only [next] at h; cases h
        | cons operation word =>
          simp only [next] at h
          cases Option.some.inj h
          simp [weight]
          omega

private def invariant (word : List Bool) (_ : ℕ) (state : Option (Data (Value := Value))) : Prop :=
  ∀ data, state = some data → weight data ≤ word.length

private theorem invariant_step (leaf : Context → ℕ → Value) (reset union : Value → Value → Value)
    (context : Context) (word : List Bool) (i : ℕ) (state : Option (Data (Value := Value)))
    (h : invariant word i state) : invariant word (i + 1) (step leaf reset union context state) := by
  intro data he
  cases hs : state with
  | none => simp [hs, step] at he
  | some previous =>
    have hp := h previous hs
    rw [hs] at he
    exact (next_weight leaf reset union context he).trans hp

private theorem option_length_le (valueEncoding : Value ↪ List Bool) (c : ℕ)
    (hbounded : ∀ value, (valueEncoding value).length ≤ c) (value : Option Value) :
    (encOption valueEncoding value).length ≤ c + 1 := by
  cases value with
  | none => simp
  | some value => simpa only [encOption_some, List.length_cons] using Nat.add_le_add_right (hbounded value) 1

private theorem frame_length_le (valueEncoding : Value ↪ List Bool) (c : ℕ)
    (hbounded : ∀ value, (valueEncoding value).length ≤ c) (frame : Frame (Value := Value)) :
    (frameEncoding valueEncoding frame).length ≤ c + 4 := by
  have h := option_length_le valueEncoding c hbounded frame.2
  simp only [frameEncoding, length_encPair, encBool_apply, List.length_cons, List.length_nil]
  omega

private theorem stack_length_le (valueEncoding : Value ↪ List Bool) (c : ℕ)
    (hbounded : ∀ value, (valueEncoding value).length ≤ c) (stack : List (Frame (Value := Value))) :
    (encList (frameEncoding valueEncoding) stack).length ≤ stack.length * (2 * c + 9) := by
  induction stack with
  | nil => simp
  | cons frame stack ih =>
    have hframe := frame_length_le valueEncoding c hbounded frame
    simp only [encList_cons, List.length_append, length_frame, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

private theorem data_length_le (valueEncoding : Value ↪ List Bool) (c : ℕ)
    (hbounded : ∀ value, (valueEncoding value).length ≤ c) (data : Data (Value := Value)) :
    (stateEncoding valueEncoding (some data)).length ≤ (4 * c + 20) * (weight data + 1) + 10 := by
  have hs := stack_length_le valueEncoding c hbounded data.1
  have hf := option_length_le valueEncoding c hbounded data.2.1
  simp only [stateEncoding, dataEncoding, encOption_some, List.length_cons, length_encPair, encBits_apply, weight]
  nlinarith

private theorem evaluateWord_polyTime (contextEncoding : Context ↪ List Bool) (valueEncoding : Value ↪ List Bool)
    (leaf : Context → ℕ → Value) (reset union : Value → Value → Value) (fallback : Value)
    (hleaf : ComputableInPolyTime (fun p : Context × ℕ => leaf p.1 p.2)
      (encPair contextEncoding encNat) valueEncoding)
    (hreset : ComputableInPolyTime (fun p : Value × Value => reset p.1 p.2)
      (encPair valueEncoding valueEncoding) valueEncoding)
    (hunion : ComputableInPolyTime (fun p : Value × Value => union p.1 p.2)
      (encPair valueEncoding valueEncoding) valueEncoding)
    (c : ℕ) (hbounded : ∀ value, (valueEncoding value).length ≤ c) :
    ComputableInPolyTime (evaluateWord leaf reset union fallback) (encPair contextEncoding encBits) valueEncoding := by
  let input := encPair contextEncoding encBits
  have hw := snd contextEncoding encBits
  have hcount : ComputableInPolyTime (fun p : Context × List Bool => 3 * p.2.length) input encUnary := by
    have h := length_bits.comp (bitsAppend (bitsAppend hw hw) hw)
    convert h using 1
    funext p
    simp only [Function.comp_def, List.length_append]
    omega
  have hstart : ComputableInPolyTime
      (fun p : Context × List Bool => some (([], (none, p.2)) : Data (Value := Value))) input (stateEncoding valueEncoding) :=
    (optionSome (dataEncoding valueEncoding)).comp ((const []).prod ((const none).prod hw))
  have hsize := ((PolyBounded.const (4 * c + 20)).mul (hw.polyBounded_length.add (.const 1))).add (.const 10)
  have hloop := ComputableInPolyTime.iterateWith_spec (par := Prod.fst)
    (count := fun p : Context × List Bool => 3 * p.2.length)
    (step := step leaf reset union) (fst contextEncoding encBits) hcount hstart
    (step_polyTime contextEncoding valueEncoding leaf reset union fallback hleaf hreset hunion)
    (fun p i state => invariant p.2 i state)
    (fun p data he => by cases Option.some.inj he; simp [weight])
    (fun p i state _ h => invariant_step leaf reset union p.1 p.2 i state h) hsize
    (fun p i state _ h => by
      cases hs : state with
      | none => simp
      | some data =>
        have hi := h data hs
        exact (data_length_le valueEncoding c hbounded data).trans (by
          gcongr
          simpa only [encBits_apply] using hi))
  have hdata := hloop.1.optionGetDWithInput (const (([], (none, [])) : Data (Value := Value)))
  have hfocus := (fst (encOption valueEncoding) encBits).comp
    ((snd (encList (frameEncoding valueEncoding)) _).comp hdata)
  exact hfocus.optionGetDWithInput (const fallback)

/-- Uniform whole-tree evaluation in a bounded encoded algebra. The context
and every variable lookup are charged on each parser transition. No maximum
numeric variable name controls the stack or clock. -/
theorem fold_polyTime (contextEncoding : Context ↪ List Bool) (valueEncoding : Value ↪ List Bool)
    (leaf : Context → ℕ → Value) (reset union : Value → Value → Value) (fallback : Value)
    (hleaf : ComputableInPolyTime (fun p : Context × ℕ => leaf p.1 p.2)
      (encPair contextEncoding encNat) valueEncoding)
    (hreset : ComputableInPolyTime (fun p : Value × Value => reset p.1 p.2)
      (encPair valueEncoding valueEncoding) valueEncoding)
    (hunion : ComputableInPolyTime (fun p : Value × Value => union p.1 p.2)
      (encPair valueEncoding valueEncoding) valueEncoding)
    (c : ℕ) (hbounded : ∀ value, (valueEncoding value).length ≤ c) :
    ComputableInPolyTime (fun p : Context × KFOL.ResetUnion.Term ℕ => fold leaf reset union p.1 p.2)
      (encPair contextEncoding ResetUnionMachines.termEncoding) valueEncoding := by
  have hcode : ComputableInPolyTime Code.encode ResetUnionMachines.termEncoding encBits := .of_eq (fun _ => rfl)
  have h := (evaluateWord_polyTime contextEncoding valueEncoding leaf reset union fallback hleaf hreset hunion c hbounded).comp
    ((fst contextEncoding ResetUnionMachines.termEncoding).prod (hcode.comp (snd contextEncoding ResetUnionMachines.termEncoding)))
  convert h using 1
  funext p
  exact (evaluateWord_encode leaf reset union fallback p.1 p.2).symm


private def finishValid (state : Option (Data (Value := Value))) : Option Value := do
  let data ← state
  if data.1.isEmpty && data.2.2.isEmpty then data.2.1 else none

private theorem finishValid_polyTime (valueEncoding : Value ↪ List Bool) :
    ComputableInPolyTime (finishValid (Value := Value)) (stateEncoding valueEncoding) (encOption valueEncoding) := by
  let input := encPair (stateEncoding valueEncoding) (dataEncoding valueEncoding)
  have hs : ComputableInPolyTime (fun p : Option (Data (Value := Value)) × Data (Value := Value) => p.2.1)
      input (encList (frameEncoding valueEncoding)) := by fun_prop
  have hw : ComputableInPolyTime (fun p : Option (Data (Value := Value)) × Data (Value := Value) => p.2.2.2)
      input encBits := by fun_prop
  have hf : ComputableInPolyTime (fun p : Option (Data (Value := Value)) × Data (Value := Value) => p.2.2.1)
      input (encOption valueEncoding) := by fun_prop
  have hstack := (ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.listIsEmpty' (frameEncoding valueEncoding))).comp hs
  have hbody := (bool_and' hstack (bitsIsEmpty.comp hw)).ite hf (const none)
  have h := (id' (encIn := stateEncoding valueEncoding)).optionElimWithInput
    (body := fun (_ : Option (Data (Value := Value))) data =>
      if data.1.isEmpty && data.2.2.isEmpty then data.2.1 else none) (const none) hbody
  convert h using 1
  funext state
  cases state <;> rfl

end Algebra

namespace Syntax

private abbrev AST := KFOL.ResetUnion.Term ℕ
private abbrev SyntaxData := Data (Value := AST)
private def leaf (_ : Bool) (j : ℕ) : AST := .var j
private def syntaxStep := step leaf Term.reset Term.union false

private def contextWord : List (Frame (Value := AST)) → List Bool → List Bool
  | [], word => word
  | (operation, none) :: stack, word => contextWord stack (true :: operation :: word)
  | (operation, some left) :: stack, word => contextWord stack (true :: operation :: (Code.encode left ++ word))

private def focusWord (focus : Option AST) : List Bool := focus.elim [] Code.encode
private def reconstruct (data : SyntaxData) : List Bool := contextWord data.1 (focusWord data.2.1 ++ data.2.2)

private theorem next_reconstruct {data result : SyntaxData}
    (h : next leaf Term.reset Term.union false data = some result) : reconstruct result = reconstruct data := by
  rcases data with ⟨stack, focus, word⟩
  cases focus with
  | some term =>
    cases stack with
    | nil => cases Option.some.inj h; rfl
    | cons frame stack =>
      rcases frame with ⟨operation, left⟩
      cases left with
      | none => cases Option.some.inj h; simp [reconstruct, contextWord, focusWord]
      | some left =>
        cases Option.some.inj h
        cases operation <;>
          simp [reconstruct, contextWord, focusWord, Code.encode_reset, Code.encode_union, List.append_assoc]
  | none =>
    cases word with
    | nil => simp only [next] at h; cases h
    | cons b word =>
      cases b with
      | true =>
        cases word with
        | nil => simp only [next] at h; cases h
        | cons operation word =>
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
        simp only [reconstruct, focusWord, Option.elim_some, Option.elim_none, leaf, List.nil_append,
          Code.encode_var, List.cons_append, ← hn, ← hw]

private theorem contextWord_length (stack : List (Frame (Value := AST))) (word : List Bool) :
    (contextWord stack word).length = (contextWord stack []).length + word.length := by
  induction stack generalizing word with
  | nil => simp [contextWord]
  | cons frame stack ih =>
    rcases frame with ⟨operation, left⟩
    cases left with
    | none =>
      simp only [contextWord]
      rw [ih (true :: operation :: word), ih [true, operation]]
      simp only [List.length_cons, List.length_nil]
      omega
    | some term =>
      simp only [contextWord]
      rw [ih (true :: operation :: (Code.encode term ++ word)), ih (true :: operation :: (Code.encode term ++ []))]
      simp only [List.length_cons, List.length_append, List.length_nil]
      omega

private theorem stack_length (stack : List (Frame (Value := AST))) :
    (encList (frameEncoding ResetUnionMachines.termEncoding) stack).length ≤ 5 * (contextWord stack []).length := by
  induction stack with
  | nil => rfl
  | cons frame stack ih =>
    rcases frame with ⟨operation, left⟩
    cases left with
    | none =>
      rw [contextWord, contextWord_length stack [true, operation]]
      simp only [encList_cons, List.length_append, length_frame, frameEncoding, length_encPair,
        encBool_apply, encOption_none, List.length_cons, List.length_nil]
      change (encList (encPair encBool (encOption ResetUnionMachines.termEncoding)) stack).length ≤ _ at ih
      omega
    | some term =>
      rw [contextWord, contextWord_length stack (true :: operation :: (Code.encode term ++ []))]
      simp only [encList_cons, List.length_append, length_frame, frameEncoding, length_encPair,
        encBool_apply, encOption_some, List.length_cons, List.length_nil]
      change 2 * (3 + ((Code.encode term).length + 1)) + 1 +
        (encList (frameEncoding ResetUnionMachines.termEncoding) stack).length ≤ _
      omega

private theorem state_length (data : SyntaxData) :
    (stateEncoding ResetUnionMachines.termEncoding (some data)).length ≤ 10 * (reconstruct data).length + 5 := by
  rcases data with ⟨stack, focus, word⟩
  have hs := stack_length stack
  have hr := contextWord_length stack (focusWord focus ++ word)
  simp only [List.length_append] at hr
  simp only [stateEncoding, encOption_some, List.length_cons, dataEncoding, length_encPair, encBits_apply]
  cases focus with
  | none =>
    simp only [encOption_none, List.length_nil, focusWord, Option.elim_none] at hr ⊢
    change _ ≤ 10 * (contextWord stack ([] ++ word)).length + 5
    omega
  | some term =>
    simp only [encOption_some, List.length_cons, focusWord, Option.elim_some] at hr ⊢
    change _ ≤ 10 * (contextWord stack (Code.encode term ++ word)).length + 5
    change _ + (2 * ((Code.encode term).length + 1) + 1 + word.length) + 1 ≤ _
    omega

private def syntaxInvariant (word : List Bool) (_ : ℕ) (state : Option SyntaxData) : Prop :=
  ∀ data, state = some data → reconstruct data = word

private theorem invariant_step (word : List Bool) (i : ℕ) (state : Option SyntaxData)
    (h : syntaxInvariant word i state) : syntaxInvariant word (i + 1) (syntaxStep state) := by
  intro data he
  cases hs : state with
  | none => simp [hs, syntaxStep, step] at he
  | some previous =>
    have hp := h previous hs
    rw [hs] at he
    exact (next_reconstruct he).trans hp

private theorem fold_identity (term : AST) : fold leaf Term.reset Term.union false term = term := by
  induction term using Term.induction_binary with
  | var j => rfl
  | reset s t hs ht => rw [fold_reset, hs, ht]
  | union s t hs ht => rw [fold_union, hs, ht]

private def decodeWord (word : List Bool) : Option AST :=
  finishValid (syntaxStep^[3 * word.length] (some ([], (none, word))))

private theorem decodeWord_encode (term : AST) : decodeWord (Code.encode term) = some term := by
  have he : 3 * (Code.encode term).length = (3 * (Code.encode term).length - cost term) + cost term :=
    (Nat.sub_add_cancel (cost_le term)).symm
  unfold decodeWord syntaxStep
  rw [he, Function.iterate_add_apply]
  have hr := run_encode leaf Term.reset Term.union false term [] []
  simp only [List.append_nil, fold_identity] at hr
  rw [hr, step_done]
  rfl

private theorem reconstruct_run (word : List Bool) (fuel : ℕ) (data : SyntaxData)
    (h : syntaxStep^[fuel] (some ([], (none, word))) = some data) : reconstruct data = word := by
  induction fuel generalizing data with
  | zero => cases Option.some.inj h; rfl
  | succ fuel ih =>
    rw [Function.iterate_succ_apply'] at h
    cases hs : syntaxStep^[fuel] (some ([], (none, word))) with
    | none =>
      change (syntaxStep^[fuel] (some ([], (none, word)))).bind
        (next leaf Term.reset Term.union false) = some data at h
      rw [hs] at h
      cases h
    | some previous =>
      have hp := ih previous hs
      rw [hs] at h
      exact (next_reconstruct h).trans hp

private theorem encode_of_decodeWord {word : List Bool} {term : AST} (h : decodeWord word = some term) :
    Code.encode term = word := by
  unfold decodeWord finishValid at h
  obtain ⟨data, hd, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  next hg =>
    obtain ⟨hs, hw⟩ := Bool.and_eq_true_iff.mp hg
    have hs := List.isEmpty_iff.mp hs
    have hw := List.isEmpty_iff.mp hw
    have hr := reconstruct_run word _ data hd
    simp only [reconstruct, hs, hw, contextWord, focusWord, h, Option.elim_some, List.append_nil] at hr
    exact hr
  next => cases h

private theorem decodeWord_eq (word : List Bool) : decodeWord word = Code.decode word := by
  cases hp : decodeWord word with
  | some term => rw [← encode_of_decodeWord hp, Code.decode_encode]
  | none =>
    cases hd : Code.decode word with
    | none => rfl
    | some term =>
      rw [← Code.encode_of_decode hd, decodeWord_encode] at hp
      cases hp

/-- The complete original prefix-tree decoder is polynomial-time, including
all malformed input cases. It reuses the certified algebra evaluator's parser. -/
@[fun_prop] theorem decode_polyTime : ComputableInPolyTime Code.decode encBits
    (encOption ResetUnionMachines.termEncoding) := by
  have hleaf : ComputableInPolyTime (fun p : Bool × ℕ => leaf p.1 p.2)
      (encPair encBool encNat) ResetUnionMachines.termEncoding := ResetUnionMachines.var_polyTime.comp (snd _ _)
  have hstep := (step_polyTime encBool ResetUnionMachines.termEncoding leaf Term.reset Term.union (.var 0)
    hleaf ResetUnionMachines.reset_polyTime ResetUnionMachines.union_polyTime).comp
      ((const false).prod (id' (encIn := stateEncoding ResetUnionMachines.termEncoding)))
  have hcount : ComputableInPolyTime (fun word : List Bool => 3 * word.length) encBits encUnary := by
    have h := length_bits.comp (bitsAppend (bitsAppend id' id') id')
    convert h using 1
    funext word
    simp only [Function.comp_def, List.length_append]
    omega
  have hstart : ComputableInPolyTime (fun word : List Bool => some (([], (none, word)) : SyntaxData))
      encBits (stateEncoding ResetUnionMachines.termEncoding) :=
    (optionSome (dataEncoding ResetUnionMachines.termEncoding)).comp ((const []).prod ((const none).prod id'))
  have hsize : PolyBounded (fun word : List Bool => word.length) (fun word => 10 * word.length + 5) :=
    ((PolyBounded.const 10).mul PolyBounded.self).add (.const 5)
  have hloop := ComputableInPolyTime.iterate_spec (count := fun word : List Bool => 3 * word.length)
    (step := syntaxStep) hcount hstart hstep syntaxInvariant
    (fun word data he => by cases Option.some.inj he; rfl)
    (fun word i state _ h => invariant_step word i state h) hsize
    (fun word i state _ h => by
      cases hs : state with
      | none => simp
      | some data =>
        have he := h data hs
        exact he ▸ state_length data)
  have h := (finishValid_polyTime ResetUnionMachines.termEncoding).comp hloop.1
  convert h using 1
  funext word
  exact (decodeWord_eq word).symm

end Syntax

end KFOL.Complexity.ResetUnionEvaluation
