module

public import KFOL.Complexity.ResetUnionEvaluation

/-! # Native collection of every original variable occurrence -/

@[expose] public section

namespace KFOL.Complexity.ResetUnionVariables

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.ResetUnion KFOL.Words

/-- A simple left-to-right occurrence list. Repeated leaves remain independent
syntax occurrences; certificate lookup uses their first common-name position. -/
def names : KFOL.ResetUnion.Term ℕ → List ℕ
  | .var j => [j]
  | .func .reset args => names (args 0) ++ names (args 1)
  | .func .union args => names (args 0) ++ names (args 1)

@[simp] theorem names_var (j : ℕ) : names (.var j) = [j] := rfl
@[simp] theorem names_reset (s t : KFOL.ResetUnion.Term ℕ) : names (s.reset t) = names s ++ names t := rfl
@[simp] theorem names_union (s t : KFOL.ResetUnion.Term ℕ) : names (s.union t) = names s ++ names t := rfl

theorem length_names_le (t : KFOL.ResetUnion.Term ℕ) : (names t).length ≤ (Code.encode t).length := by
  induction t using Term.induction_binary with
  | var j => simp [Code.encode_var]
  | reset s t hs ht => simp only [names_reset, Code.encode_reset, List.length_append, List.length_cons]; omega
  | union s t hs ht => simp only [names_union, Code.encode_union, List.length_append, List.length_cons]; omega

private abbrev Data := List ℕ × List Bool
private abbrev dataEncoding := encPair (encList encNat) encBits
private abbrev stateEncoding := encOption dataEncoding

private def next : Data → Option Data
  | (labels, []) => some (labels, [])
  | (labels, true :: _ :: word) => some (labels, word)
  | (_, true :: []) => none
  | (labels, false :: word) => do
      let (name, rest) ← unpair? word
      let j ← BinaryNatCode.decode? name
      return (labels ++ [j], rest)

private def step (state : Option Data) : Option Data := state.bind next

private theorem run_encode (t : KFOL.ResetUnion.Term ℕ) (labels : List ℕ) (rest : List Bool) :
    step^[t.size] (some (labels, Code.encode t ++ rest)) = some (labels ++ names t, rest) := by
  induction t using Term.induction_binary generalizing labels rest with
  | var j => simp [step, next, Code.encode_var]
  | reset s t hs ht =>
    have he : (s.reset t).size = t.size + s.size + 1 := by rw [Term.size_reset]; omega
    rw [he]
    simp only [Function.iterate_add_apply, Function.iterate_one]
    change step^[t.size] (step^[s.size] (step (some (labels, Code.encode (s.reset t) ++ rest)))) = _
    simp only [Code.encode_reset, List.cons_append, List.append_assoc, step, Option.bind_some, next]
    rw [hs, ht]
    simp only [names_reset, List.append_assoc]
  | union s t hs ht =>
    have he : (s.union t).size = t.size + s.size + 1 := by rw [Term.size_union]; omega
    rw [he]
    simp only [Function.iterate_add_apply, Function.iterate_one]
    change step^[t.size] (step^[s.size] (step (some (labels, Code.encode (s.union t) ++ rest)))) = _
    simp only [Code.encode_union, List.cons_append, List.append_assoc, step, Option.bind_some, next]
    rw [hs, ht]
    simp only [names_union, List.append_assoc]

private theorem step_done (labels : List ℕ) (k : ℕ) : step^[k] (some (labels, [])) = some (labels, []) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih]; rfl

private def collectWord (word : List Bool) : List ℕ :=
  ((step^[word.length] (some ([], word))).getD ([], [])).1

private theorem collectWord_encode (t : KFOL.ResetUnion.Term ℕ) : collectWord (Code.encode t) = names t := by
  have he : (Code.encode t).length = ((Code.encode t).length - t.size) + t.size :=
    (Nat.sub_add_cancel (Code.size_le_length_encode t)).symm
  unfold collectWord
  rw [he, Function.iterate_add_apply]
  have hr := run_encode t [] []
  simp only [List.append_nil, List.nil_append] at hr
  rw [hr, step_done]
  rfl

private def leafData (data : Data) : Option Data :=
  (unpair? data.2.tail).elim none fun p =>
    (BinaryNatCode.decode? p.1).map (fun j => (data.1 ++ [j], p.2))

private theorem leafData_polyTime : ComputableInPolyTime leafData dataEncoding stateEncoding := by
  let pairEncoding := encPair encBits encBits
  have hname : ComputableInPolyTime (fun p : Data × (List Bool × List Bool) => p.2.1)
      (encPair dataEncoding pairEncoding) encBits := by fun_prop
  have hs : ComputableInPolyTime (fun p : (Data × (List Bool × List Bool)) × ℕ => p.1.1.1)
      (encPair (encPair dataEncoding pairEncoding) encNat) (encList encNat) := by fun_prop
  have hr : ComputableInPolyTime (fun p : (Data × (List Bool × List Bool)) × ℕ => p.1.2.2)
      (encPair (encPair dataEncoding pairEncoding) encNat) encBits := by fun_prop
  have hout := (listAppend' hs (cons' (snd _ _) (const []))).prod hr
  have hinner := (Dictionary.decode_polyTime.comp hname).optionMapWithInput
    (f := fun (p : Data × (List Bool × List Bool)) (j : ℕ) => ((p.1.1 ++ [j], p.2.2) : Data)) hout
  have hp := Framing.unpair_polyTime.comp ((tail (encA := encBool) (encL := encBits)).comp (snd (encList encNat) encBits))
  exact hp.optionElimWithInput (const none) hinner

private def nextFast (data : Data) : Option Data :=
  if data.2.isEmpty then some data
  else if data.2.headD false then
    if data.2.tail.isEmpty then none else some (data.1, data.2.tail.tail)
  else leafData data

private theorem nextFast_eq (data : Data) : nextFast data = next data := by
  rcases data with ⟨labels, word⟩
  cases word with
  | nil => rfl
  | cons b word =>
    cases b with
    | true => cases word <;> rfl
    | false =>
      unfold nextFast leafData
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.headD_cons, List.tail_cons]
      simp only [next]
      cases hp : unpair? word with
      | none => rfl
      | some pair =>
        rcases pair with ⟨name, rest⟩
        simp only [Option.elim_some]
        cases hn : BinaryNatCode.decode? name <;> simp [hn]

private theorem next_polyTime : ComputableInPolyTime next dataEncoding stateEncoding := by
  have hl := fst (encList encNat) encBits
  have hw := snd (encList encNat) encBits
  have htail := (tail (encA := encBool) (encL := encBits)).comp hw
  have hrest := (tail (encA := encBool) (encL := encBits)).comp htail
  have hnode := (bitsIsEmpty.comp htail).ite (const none)
    ((optionSome dataEncoding).comp (hl.prod hrest))
  have h := (bitsIsEmpty.comp hw).ite (optionSome dataEncoding)
    (((headD (encA := encBool) (encL := encBits) false).comp hw).ite hnode leafData_polyTime)
  convert h using 1
  funext data
  exact (nextFast_eq data).symm

private theorem step_polyTime : ComputableInPolyTime step stateEncoding stateEncoding := by
  have h := (id' (encIn := stateEncoding)).optionElimWithInput
    (body := fun (_ : Option Data) data => next data) (const none) (next_polyTime.comp (snd _ _))
  convert h using 1
  funext state
  cases state <;> rfl

private def weight (data : Data) : ℕ := (encList encNat data.1).length + data.2.length

private theorem next_weight {data result : Data} (h : next data = some result) : weight result ≤ weight data := by
  rcases data with ⟨labels, word⟩
  cases word with
  | nil => cases Option.some.inj h; rfl
  | cons b word =>
    cases b with
    | true =>
      cases word with
      | nil => cases h
      | cons operation word =>
        cases Option.some.inj h
        simp only [weight, List.length_cons]
        omega
    | false =>
      simp only [next] at h
      obtain ⟨⟨name, rest⟩, hp, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨j, hj, he⟩ := Option.bind_eq_some_iff.mp h
      cases Option.some.inj he
      have hw := eq_delimit_append_of_unpair?_eq_some hp
      have hn := (BinaryNatCode.decode?_eq_some_iff name j).mp hj
      simp only [weight, encList_append, encList_cons, encList_nil, List.append_nil,
        List.length_append, length_frame, List.length_cons]
      have hlen := congrArg List.length hw
      simp only [List.length_append, delimit_length, hn, BinaryNatCode.length_encode] at hlen
      simp only [encNat_apply]
      have hbits := Nat.size_eq_bits_len j
      omega

private def invariant (word : List Bool) (_ : ℕ) (state : Option Data) : Prop :=
  ∀ data, state = some data → weight data ≤ word.length

private theorem invariant_step (word : List Bool) (i : ℕ) (state : Option Data)
    (h : invariant word i state) : invariant word (i + 1) (step state) := by
  intro data he
  cases hs : state with
  | none => simp [hs, step] at he
  | some previous =>
    have hp := h previous hs
    rw [hs] at he
    exact (next_weight he).trans hp

private theorem collectWord_polyTime : ComputableInPolyTime collectWord encBits (encList encNat) := by
  have hstart : ComputableInPolyTime (fun word : List Bool => some (([], word) : Data)) encBits stateEncoding :=
    (optionSome dataEncoding).comp ((const []).prod id')
  have hsize : PolyBounded (fun word : List Bool => word.length) (fun word => 2 * word.length + 2) :=
    ((PolyBounded.const 2).mul PolyBounded.self).add (.const 2)
  have hloop := ComputableInPolyTime.iterate_spec length_bits hstart step_polyTime invariant
    (fun word data he => by cases Option.some.inj he; simp [weight])
    (fun word i state _ h => invariant_step word i state h) hsize
    (fun word i state _ h => by
      cases hs : state with
      | none => simp
      | some data =>
        have hi := h data hs
        simp only [stateEncoding, dataEncoding, encOption_some, List.length_cons, length_encPair, encBits_apply]
        unfold weight at hi
        omega)
  exact (fst (encList encNat) encBits).comp (hloop.1.optionGetDWithInput (const ([], [])))

@[fun_prop] theorem names_polyTime : ComputableInPolyTime names ResetUnionMachines.termEncoding (encList encNat) := by
  have hcode : ComputableInPolyTime Code.encode ResetUnionMachines.termEncoding encBits := .of_eq (fun _ => rfl)
  have h := collectWord_polyTime.comp hcode
  convert h using 1
  funext t
  exact (collectWord_encode t).symm


/-- One occurrence list for both sides of an equation. -/
def equationNames (equation : Equation) : List ℕ := names equation.1 ++ names equation.2

@[fun_prop] theorem equationNames_polyTime : ComputableInPolyTime equationNames
    ResetUnionMachines.equationEncoding (encList encNat) :=
  (listAppend' (names_polyTime.comp (fst _ _)) (names_polyTime.comp (snd _ _))).comp
    ResetUnionMachines.arguments_polyTime

theorem length_equationNames_le (equation : Equation) :
    (equationNames equation).length ≤ (Code.encodeEquation equation).length := by
  have hs := length_names_le equation.1
  have ht := length_names_le equation.2
  simp only [equationNames, List.length_append, Code.encodeEquation, Words.pair_length]
  omega

/-- Evaluation only depends on the names actually occurring in the syntax. -/
theorem fold_congr {Context Value : Type} (leaf other : Context → ℕ → Value)
    (reset union : Value → Value → Value) (context : Context) (t : KFOL.ResetUnion.Term ℕ)
    (h : ∀ j ∈ names t, leaf context j = other context j) :
    ResetUnionEvaluation.fold leaf reset union context t = ResetUnionEvaluation.fold other reset union context t := by
  induction t using Term.induction_binary with
  | var j => exact h j (by simp)
  | reset s t hs ht =>
    rw [ResetUnionEvaluation.fold_reset, ResetUnionEvaluation.fold_reset]
    rw [hs (fun j hj => h j (List.mem_append_left _ hj)), ht (fun j hj => h j (List.mem_append_right _ hj))]
  | union s t hs ht =>
    rw [ResetUnionEvaluation.fold_union, ResetUnionEvaluation.fold_union]
    rw [hs (fun j hj => h j (List.mem_append_left _ hj)), ht (fun j hj => h j (List.mem_append_right _ hj))]

end KFOL.Complexity.ResetUnionVariables
