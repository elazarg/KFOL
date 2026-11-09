module
public import KFOL.Complexity.FiniteFoldStorage
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
/-! # Native polynomial-time folds with captured context and polynomial annotations -/

@[expose] public section
namespace KFOL.Complexity.FiniteFoldMachine
open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FiniteTermCode
variable {σ : ℕ → Type} [Fintype (Operation σ)]
variable {Context Value : Type}
variable {contextEncoding : Context ↪ List Bool} {valueEncoding : Value ↪ List Bool}

noncomputable def evaluateState (leaf : Context → ℕ → Value)
    (node : Context → Operation σ → List Value → Value) (input : Context × List Bool) : State σ Value :=
  (step leaf node input.1)^[2 * input.2.length + 1] (some ([], none, input.2))

theorem evaluateState_polyTime (leaf : Context → ℕ → Value)
    (node : Context → Operation σ → List Value → Value)
    (hleaf : ComputableInPolyTime (fun p : Context × ℕ => leaf p.1 p.2)
      (encPair contextEncoding encNat) valueEncoding)
    (hnode : ComputableInPolyTime (fun p : Context × (Operation σ × List Value) => node p.1 p.2.1 p.2.2)
      (encPair contextEncoding (encPair FiniteTermMachines.operationEncoding (encList valueEncoding))) valueEncoding)
    (c degree : ℕ)
    (hfold : ∀ context (term : Equational.Term σ ℕ),
      (valueEncoding (fold leaf node context term)).length ≤
        c * ((contextEncoding context).length + (encode σ term).length + 1)^degree) :
    ComputableInPolyTime (evaluateState leaf node) (encPair contextEncoding encBits)
      (stateEncoding valueEncoding) := by
  let input := encPair contextEncoding encBits
  have hc := fst contextEncoding encBits
  have hw := snd contextEncoding encBits
  have hn := length_bits.comp hw
  have hcount := unary_add.comp ((unary_mul.comp ((const 2).prod hn)).prod (const 1))
  have hinit := (optionSome (dataEncoding (σ := σ) valueEncoding)).comp
    ((const []).prod ((const none).prod hw))
  let invariant (p : Context × List Bool) (_ : ℕ) (state : State σ Value) : Prop :=
    stateValid leaf node p.1 state ∧
      (contextEncoding p.1).length + stateWeight state ≤ (input p).length
  have hbase : ∀ p : Context × List Bool, invariant p 0 (some ([], none, p.2)) := by
    intro p
    constructor
    · constructor
      · intro frame h
        cases h
      · intro cache h
        cases h
    · simp only [stateWeight, dataWeight, Option.elim_some, Option.elim_none,
        List.map_nil, List.sum_nil, Nat.zero_add, input, length_encPair, encBits_apply]
      omega
  have hpreserve : ∀ p i state, i < 2 * p.2.length + 1 → invariant p i state →
      invariant p (i + 1) (step leaf node p.1 state) := by
    intro p i state _ hi
    constructor
    · exact step_valid leaf node p.1 state hi.1
    · have hw := step_weight leaf node p.1 state
      exact (Nat.add_le_add_left hw _).trans hi.2
  have hp : PolyBounded (fun p : Context × List Bool => (input p).length)
      (fun p => (input p).length + 1) := PolyBounded.self.add (PolyBounded.const 1)
  have hsize := ((PolyBounded.const 32).mul (hp.pow 3)).mul
    (((PolyBounded.const c).mul (hp.pow degree)).add (PolyBounded.const 1))
  have h := ComputableInPolyTime.iterateWith_spec hc hcount hinit (step_polyTime leaf node hleaf hnode)
    invariant hbase hpreserve hsize (fun p _ state _ hi =>
      encoded_state_bound leaf node p.1 state c degree (input p).length (hfold p.1) hi.1 hi.2)
  exact h.1

noncomputable def result (state : State σ Value) : Option (Cached σ Value) :=
  state.elim none (fun data => if data.1.isEmpty && data.2.2.isEmpty then data.2.1 else none)

theorem result_polyTime : ComputableInPolyTime (@result σ Value)
    (stateEncoding valueEncoding) (encOption (cachedEncoding valueEncoding)) := by
  have hs : ComputableInPolyTime (fun data : Data σ Value => data.1)
      (dataEncoding valueEncoding) (encList (frameEncoding valueEncoding)) := fst _ _
  have hr : ComputableInPolyTime (fun data : Data σ Value => data.2.2)
      (dataEncoding valueEncoding) encBits := by fun_prop
  have hf : ComputableInPolyTime (fun data : Data σ Value => data.2.1)
      (dataEncoding valueEncoding) (encOption (cachedEncoding valueEncoding)) := by fun_prop
  have hempty := (ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.listIsEmpty (encA := frameEncoding (σ := σ) valueEncoding))).comp hs
  have htest := bool_and' hempty (bitsIsEmpty.comp hr)
  have hbody := htest.ite hf (const none)
  have h := (id' (encIn := stateEncoding (σ := σ) valueEncoding)).optionElimWithInput
    (body := fun (_ : State σ Value) (data : Data σ Value) => if data.1.isEmpty && data.2.2.isEmpty then data.2.1 else none)
    (const none) (hbody.comp (snd (stateEncoding (σ := σ) valueEncoding) (dataEncoding (σ := σ) valueEncoding)))
  convert h using 1
  funext state
  rfl

private theorem step_done (leaf : Context → ℕ → Value)
    (node : Context → Operation σ → List Value → Value) (context : Context)
    (cache : Cached σ Value) (rest : List Bool) (clock : ℕ) :
    (step leaf node context)^[clock] (some ([], some cache, rest)) = some ([], some cache, rest) := by
  induction clock with
  | zero => rfl
  | succ clock ih => rw [Function.iterate_succ_apply', ih]; rfl

theorem evaluateState_encode (leaf : Context → ℕ → Value)
    (node : Context → Operation σ → List Value → Value) (context : Context)
    (term : Equational.Term σ ℕ) :
    evaluateState leaf node (context, encode σ term) =
      some ([], some (sourceCache leaf node context term), []) := by
  have hc : cost term ≤ 2 * (encode σ term).length + 1 := by have := cost_le_code term; omega
  have he : 2 * (encode σ term).length + 1 =
      (2 * (encode σ term).length + 1 - cost term) + cost term := (Nat.sub_add_cancel hc).symm
  unfold evaluateState
  rw [he, Function.iterate_add_apply]
  have ht := trace_term leaf node context term [] []
  simp only [List.append_nil] at ht
  rw [ht, step_done]

/-- Native polynomial-time evaluation of the original mathematical fold. The
annotation bound is measured against captured context plus original syntax. -/
theorem fold_polyTime (leaf : Context → ℕ → Value)
    (node : Context → Operation σ → List Value → Value)
    (hleaf : ComputableInPolyTime (fun p : Context × ℕ => leaf p.1 p.2)
      (encPair contextEncoding encNat) valueEncoding)
    (hnode : ComputableInPolyTime (fun p : Context × (Operation σ × List Value) => node p.1 p.2.1 p.2.2)
      (encPair contextEncoding (encPair FiniteTermMachines.operationEncoding (encList valueEncoding))) valueEncoding)
    (c degree : ℕ)
    (hfold : ∀ context (term : Equational.Term σ ℕ),
      (valueEncoding (fold leaf node context term)).length ≤
        c * ((contextEncoding context).length + (encode σ term).length + 1)^degree)
    (fallback : Value) :
    ComputableInPolyTime (fun p : Context × Equational.Term σ ℕ => fold leaf node p.1 p.2)
      (encPair contextEncoding FiniteTermMachines.termEncoding) valueEncoding := by
  have he := evaluateState_polyTime leaf node hleaf hnode c degree hfold
  have hc := fst contextEncoding (FiniteTermMachines.termEncoding (σ := σ))
  have ht := FiniteTermMachines.encode_polyTime.comp (snd contextEncoding (FiniteTermMachines.termEncoding (σ := σ)))
  have hresult := result_polyTime.comp (he.comp (hc.prod ht))
  have hcache := hresult.optionGetDWithInput (const ((.var 0 : Equational.Term σ ℕ), fallback))
  have h := (snd (FiniteTermMachines.termEncoding (σ := σ)) valueEncoding).comp hcache
  convert h using 1
  funext p
  simp only [Function.comp_def, evaluateState_encode]
  rfl

end KFOL.Complexity.FiniteFoldMachine
