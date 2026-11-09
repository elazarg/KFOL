module

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration

/-! # Native machine certificates for typed right-to-left word scans

The fold retains the processed suffix beside its typed accumulator. Its
callback is certified uniformly in all captured context and intermediate data.
This generalizes the word-valued fold in GameTheory's complexity backend.
-/

@[expose] public section

namespace KFOL.Complexity

open Turing.MultiTapeTM

/-- Process a word from its right end, exposing the actual processed suffix
to the callback. The accumulator may have any independently encoded type. -/
def suffixFold {Context State : Type}
    (step : Context → List Bool → State → Bool → State)
    (context : Context) (initial : State) (word : List Bool) : State :=
  (word.reverse.foldl
    (fun state bit => (bit :: state.1, step context state.1 state.2 bit)) ([], initial)).2

private theorem suffixFold_state_fst {Context State : Type}
    (step : Context → List Bool → State → Bool → State)
    (context : Context) (initial : State) (word : List Bool) :
    (word.reverse.foldl
      (fun state bit => (bit :: state.1, step context state.1 state.2 bit)) ([], initial)).1 = word := by
  induction word with
  | nil => rfl
  | cons bit word ih =>
    rw [List.reverse_cons, List.foldl_append]
    change bit :: (word.reverse.foldl _ ([], initial)).1 = bit :: word
    exact congrArg (List.cons bit) ih

@[simp] theorem suffixFold_nil {Context State : Type}
    (step : Context → List Bool → State → Bool → State)
    (context : Context) (initial : State) : suffixFold step context initial [] = initial := rfl

@[simp] theorem suffixFold_cons {Context State : Type}
    (step : Context → List Bool → State → Bool → State)
    (context : Context) (initial : State) (bit : Bool) (word : List Bool) :
    suffixFold step context initial (bit :: word) =
      step context word (suffixFold step context initial word) bit := by
  simp only [suffixFold, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [suffixFold_state_fst]

/-- Polynomial encoded state bounds and one uniform callback machine certify
the complete scan, including the captured context and suffix bookkeeping. -/
theorem suffixFold_polyTime
    {Input Context State : Type} {input : Input ↪ List Bool}
    {contextEncoding : Context ↪ List Bool} {stateEncoding : State ↪ List Bool}
    {context : Input → Context} {word : Input → List Bool} {initial : Input → State}
    {step : Context → List Bool → State → Bool → State}
    (hcontext : ComputableInPolyTime context input contextEncoding)
    (hword : ComputableInPolyTime word input encBits)
    (hinitial : ComputableInPolyTime initial input stateEncoding)
    (hstep : ComputableInPolyTime
      (fun p : (Context × (List Bool × State)) × Bool =>
        step p.1.1 p.1.2.1 p.1.2.2 p.2)
      (encPair (encPair contextEncoding (encPair encBits stateEncoding)) encBool) stateEncoding)
    {bound : Input → ℕ}
    (hbound : PolyBounded (fun x => (input x).length) bound)
    (hstates : ∀ x suffix, suffix <:+ word x →
      (stateEncoding (suffixFold step (context x) (initial x) suffix)).length ≤ bound x) :
    ComputableInPolyTime
      (fun x => suffixFold step (context x) (initial x) (word x)) input stateEncoding := by
  have hreverse : ComputableInPolyTime (fun x => (word x).reverse) input encBits :=
    ComputableInPolyTime.bitsReverse.comp hword
  have hstart : ComputableInPolyTime (fun x => (([] : List Bool), initial x)) input
      (encPair encBits stateEncoding) :=
    (ComputableInPolyTime.const []).prod hinitial
  have hadvance : ComputableInPolyTime
      (fun p : (Context × (List Bool × State)) × Bool =>
        (p.2 :: p.1.2.1, step p.1.1 p.1.2.1 p.1.2.2 p.2))
      (encPair (encPair contextEncoding (encPair encBits stateEncoding)) encBool)
      (encPair encBits stateEncoding) := by
    apply ComputableInPolyTime.pair (enc₁ := encBits) (enc₂ := stateEncoding)
    · exact ComputableInPolyTime.bitsCons (by fun_prop) (by fun_prop)
    · exact hstep
  have hlength := hword.polyBounded_length
  have hsize : PolyBounded (fun x => (input x).length)
      (fun x => 2 * (word x).length + 1 + bound x) :=
    (((PolyBounded.const 2).mul hlength).add (.const 1)).add hbound
  let invariant (x : Input) (consumed : List Bool) (state : List Bool × State) : Prop :=
    state.1 = consumed.reverse ∧
      state.2 = suffixFold step (context x) (initial x) consumed.reverse
  have hfold := ComputableInPolyTime.foldlWith_spec
    (encA := encBool)
    (step := fun context (state : List Bool × State) bit =>
      (bit :: state.1, step context state.1 state.2 bit)) hcontext hreverse hstart hadvance
    invariant (fun _ => ⟨rfl, rfl⟩)
    (fun x consumed state bit _ hstate => by
      change bit :: state.1 = (consumed ++ [bit]).reverse ∧
        step (context x) state.1 state.2 bit =
          suffixFold step (context x) (initial x) (consumed ++ [bit]).reverse
      rw [List.reverse_append, List.reverse_singleton, List.singleton_append, suffixFold_cons]
      constructor
      · exact congrArg (List.cons bit) hstate.1
      · rw [hstate.1, hstate.2])
    hsize
    (fun x consumed state hprefix hstate => by
      have hsuffix : consumed.reverse <:+ word x := by simpa using hprefix.reverse
      have hlength' : consumed.length ≤ (word x).length := by
        simpa only [List.length_reverse] using hprefix.length_le
      have hvalue := hstates x consumed.reverse hsuffix
      rw [length_encPair]
      change 2 * state.1.length + 1 + (stateEncoding state.2).length ≤ _
      rw [hstate.1, hstate.2, List.length_reverse]
      omega)
  exact (ComputableInPolyTime.snd encBits stateEncoding).comp hfold.1

end KFOL.Complexity
