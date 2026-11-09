module

public import KFOL.Complexity.CircuitRecords
public import KFOL.Complexity.FiniteSignatureVerifier
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-! Native cached evaluation of original shared graphs in a fixed finite
algebra. Values are constant-width; graph references remain binary names. -/

@[expose] public section

namespace KFOL.Complexity.CircuitMachine

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FiniteTermCode KFOL.Complexity.FiniteAlgebraVerifier

variable {σ : ℕ → Type} [Fintype (Operation σ)]
variable {Value : Type} [Fintype Value] [Nonempty Value]
variable [(Equational.language σ).Structure Value]

abbrev Cache (Value : Type) := List Value
noncomputable abbrev cacheEncoding := encList (valueEncoding (Value := Value))

private theorem binaryLookup_polyTime : ComputableInPolyTime
    (fun p : Cache Value × ℕ => p.1.getD p.2 fallback)
    (encPair cacheEncoding encNat) valueEncoding :=
  .of_tidy (ComputableTidilyInPolyTime.listGetD_binary fallback
    (ComputableTidilyInPolyTime.fst cacheEncoding encNat)
    (ComputableTidilyInPolyTime.snd cacheEncoding encNat))

private abbrev NodeInput (σ : ℕ → Type) (Value : Type) := (Context × Cache Value) × (Operation σ × List ℕ)
private noncomputable abbrev nodeInputEncoding :=
  encPair (encPair contextEncoding (cacheEncoding (Value := Value)))
    (encPair (FiniteTermMachines.operationEncoding (σ := σ)) (encList encNat))

noncomputable def evalOperation (cache : Cache Value) (operation : Operation σ) (refs : List ℕ) : Value :=
  FirstOrder.Language.Structure.funMap (L := Equational.language σ) operation.2
    (fun i => cache.getD (refs.getD i.val 0) fallback)

private theorem evalOperation_polyTime : ComputableInPolyTime
    (fun p : NodeInput σ Value => evalOperation p.1.2 p.2.1 p.2.2)
    nodeInputEncoding valueEncoding := by
  have hop : ComputableInPolyTime (fun p : NodeInput σ Value => p.2.1)
      nodeInputEncoding FiniteTermMachines.operationEncoding := by fun_prop
  have hcache : ComputableInPolyTime (fun p : NodeInput σ Value => p.1.2)
      nodeInputEncoding cacheEncoding := by fun_prop
  have hrefs : ComputableInPolyTime (fun p : NodeInput σ Value => p.2.2)
      nodeInputEncoding (encList encNat) := by fun_prop
  apply hop.finite_cases (branch := fun operation p => evalOperation p.1.2 operation p.2.2)
  rintro ⟨n, function⟩
  have hargs : ComputableInPolyTime
      (fun p : NodeInput σ Value => fun i : Fin n => p.1.2.getD (p.2.2.getD i.val 0) fallback)
      nodeInputEncoding (encPi valueEncoding) := by
    apply ComputableInPolyTime.pi
    intro i
    have href := (listGetD (encA := encNat) (encL := encList encNat) 0).comp (hrefs.prod (const i.val))
    exact binaryLookup_polyTime.comp (hcache.prod href)
  have hf : ComputableInPolyTime
      (fun args : Fin n → Value => FirstOrder.Language.Structure.funMap (L := Equational.language σ) function args)
      (encPi valueEncoding) valueEncoding := .of_finite _
  exact hf.comp hargs

noncomputable def evalNode (cache : Cache Value) (operation : Operation σ) (refs : List ℕ) : Option Value :=
  if refs.length = operation.1 ∧ ∀ ref ∈ refs, ref < cache.length then
    some (evalOperation cache operation refs)
  else none

private theorem evalNode_polyTime : ComputableInPolyTime
    (fun p : NodeInput σ Value => evalNode p.1.2 p.2.1 p.2.2)
    nodeInputEncoding (encOption valueEncoding) := by
  classical
  have hcache : ComputableInPolyTime (fun p : NodeInput σ Value => p.1.2)
      nodeInputEncoding cacheEncoding := by fun_prop
  have hrefs : ComputableInPolyTime (fun p : NodeInput σ Value => p.2.2)
      nodeInputEncoding (encList encNat) := by fun_prop
  have hcount := (length_list valueEncoding).comp hcache
  have hop : ComputableInPolyTime (fun p : NodeInput σ Value => p.2.1)
      nodeInputEncoding FiniteTermMachines.operationEncoding := by fun_prop
  have harity : ComputableInPolyTime (fun op : Operation σ => op.1)
      FiniteTermMachines.operationEncoding encUnary := .of_finite _
  have heq := decide_eq' ((length_list encNat).comp hrefs) (harity.comp hop)
  have hbound := binary_lt' (snd nodeInputEncoding encNat)
    ((unary_to_binary.comp hcount).comp (fst nodeInputEncoding encNat))
  have hall := allWithInput (test := fun (p : NodeInput σ Value) ref => decide (ref < p.1.2.length)) hrefs hbound
  have h := (bool_and' heq hall).ite ((optionSome (valueEncoding (Value := Value))).comp evalOperation_polyTime) (const none)
  convert h using 1
  funext p
  simp only [evalNode, List.all_eq_true, decide_eq_true_eq, Bool.and_eq_true, Function.comp_def]

private abbrev GateInput (σ : ℕ → Type) (Value : Type) := (Context × Cache Value) × RawGate σ
private noncomputable abbrev gateInputEncoding :=
  encPair (encPair contextEncoding (cacheEncoding (Value := Value))) (gateEncoding (σ := σ))

noncomputable def evalGate (context : Context) (cache : Cache Value) (gate : RawGate σ) : Option Value :=
  gate.1.elim (some (lookup context gate.2.1)) (fun operation => evalNode cache operation gate.2.2)

private theorem evalGate_polyTime : ComputableInPolyTime
    (fun p : GateInput σ Value => evalGate p.1.1 p.1.2 p.2)
    gateInputEncoding (encOption valueEncoding) := by
  have ho : ComputableInPolyTime (fun p : GateInput σ Value => p.2.1)
      gateInputEncoding (encOption FiniteTermMachines.operationEncoding) := by fun_prop
  have hcontext : ComputableInPolyTime (fun p : GateInput σ Value => p.1.1)
      gateInputEncoding contextEncoding := by fun_prop
  have hname : ComputableInPolyTime (fun p : GateInput σ Value => p.2.2.1)
      gateInputEncoding encNat := by fun_prop
  have hinput := (optionSome (valueEncoding (Value := Value))).comp ((lookup_polyTime (Value := Value)).comp (hcontext.prod hname))
  have hcache : ComputableInPolyTime (fun p : GateInput σ Value × Operation σ => p.1.1.2)
      (encPair gateInputEncoding FiniteTermMachines.operationEncoding) cacheEncoding := by fun_prop
  have hop := snd (gateInputEncoding (σ := σ) (Value := Value)) (FiniteTermMachines.operationEncoding (σ := σ))
  have hrefs : ComputableInPolyTime (fun p : GateInput σ Value × Operation σ => p.1.2.2.2)
      (encPair gateInputEncoding FiniteTermMachines.operationEncoding) (encList encNat) := by fun_prop
  have hc : ComputableInPolyTime (fun p : GateInput σ Value × Operation σ => p.1.1.1)
      (encPair gateInputEncoding FiniteTermMachines.operationEncoding) contextEncoding := by fun_prop
  have hbody := evalNode_polyTime.comp ((hc.prod hcache).prod (hop.prod hrefs))
  exact ho.optionElimWithInput (body := fun (p : GateInput σ Value) operation => evalNode p.1.2 operation p.2.2.2)
    hinput hbody


private abbrev StepInput (σ : ℕ → Type) (Value : Type) := (Context × Option (Cache Value)) × RawGate σ
private noncomputable abbrev stepInputEncoding :=
  encPair (encPair contextEncoding (encOption (cacheEncoding (Value := Value)))) (gateEncoding (σ := σ))

noncomputable def step (context : Context) (cache : Option (Cache Value)) (gate : RawGate σ) : Option (Cache Value) :=
  cache.bind fun values => (evalGate context values gate).map (fun value => values ++ [value])

private theorem step_polyTime : ComputableInPolyTime
    (fun p : StepInput σ Value => step p.1.1 p.1.2 p.2)
    stepInputEncoding (encOption cacheEncoding) := by
  have hs : ComputableInPolyTime (fun p : StepInput σ Value => p.1.2)
      stepInputEncoding (encOption cacheEncoding) := by fun_prop
  let inner := encPair (stepInputEncoding (σ := σ) (Value := Value)) (cacheEncoding (Value := Value))
  have hcontext : ComputableInPolyTime (fun p : StepInput σ Value × Cache Value => p.1.1.1)
      inner contextEncoding := by fun_prop
  have hcache := snd (stepInputEncoding (σ := σ) (Value := Value)) (cacheEncoding (Value := Value))
  have hgate : ComputableInPolyTime (fun p : StepInput σ Value × Cache Value => p.1.2)
      inner gateEncoding := by fun_prop
  have heval := evalGate_polyTime.comp ((hcontext.prod hcache).prod hgate)
  have hc : ComputableInPolyTime (fun p : (StepInput σ Value × Cache Value) × Value => p.1.2)
      (encPair inner valueEncoding) cacheEncoding := by fun_prop
  have hv := snd inner (valueEncoding (Value := Value))
  have happend := listAppend' hc (cons' hv (const []))
  have hmap := heval.optionMapWithInput (f := fun (p : StepInput σ Value × Cache Value) value => p.2 ++ [value]) happend
  have h := hs.optionElimWithInput
    (body := fun (p : StepInput σ Value) cache => (evalGate p.1.1 cache p.2).map (fun value => cache ++ [value]))
    (const none) hmap
  convert h using 1
  funext p
  unfold step
  cases p.1.2 <;> rfl

noncomputable def run (context : Context) (gates : List (RawGate σ)) : Option (Cache Value) :=
  gates.foldl (step context) (some [])

theorem run_polyTime : ComputableInPolyTime
    (fun p : Context × List (RawGate σ) => (run p.1 p.2 : Option (Cache Value)))
    (encPair contextEncoding (encList gateEncoding)) (encOption cacheEncoding) := by
  let input := encPair contextEncoding (encList (gateEncoding (σ := σ)))
  have hlist := snd contextEncoding (encList (gateEncoding (σ := σ)))
  have hc : ComputableInPolyTime
      (fun p : ((Context × List (RawGate σ)) × Option (Cache Value)) × RawGate σ => p.1.1.1)
      (encPair (encPair input (encOption cacheEncoding)) gateEncoding) contextEncoding := by fun_prop
  have hs : ComputableInPolyTime
      (fun p : ((Context × List (RawGate σ)) × Option (Cache Value)) × RawGate σ => p.1.2)
      (encPair (encPair input (encOption cacheEncoding)) gateEncoding) (encOption cacheEncoding) := by fun_prop
  have hg := snd (encPair input (encOption (cacheEncoding (Value := Value)))) (gateEncoding (σ := σ))
  have hstep := step_polyTime.comp ((hc.prod hs).prod hg)
  apply foldlWithInput_of_bounded_growth (list := fun p : Context × List (RawGate σ) => p.2)
    (init := fun _ => (some [] : Option (Cache Value)))
    (step := fun p cache gate => step p.1 cache gate)
    (const (some [])) ⟨hlist, hstep, inferInstance, inferInstance⟩
    (growth := fun _ => 2 * Fintype.card Value + 1)
  constructor
  · exact PolyBounded.const _
  · intro p cache gate _
    cases cache with
    | none => simp [step]
    | some cache =>
      cases he : evalGate p.1 cache gate with
      | none => simp [step, he]
      | some value =>
        have hv := value_length_le value
        simp only [step, he, Option.bind_some, Option.map_some, encOption_some,
          List.length_cons, encList_append, List.length_append, encList_cons, encList_nil, List.append_nil]
        simp only [Turing.MultiTapeTM.length_frame, cacheEncoding]
        omega


omit [Fintype (Operation σ)] in
theorem evalGate_view (context : Context) (cache : Cache Value) (gate : Circuit.Gate σ ℕ) :
    evalGate context cache (viewGate gate) = gate.eval (lookup context) cache := by
  cases gate with
  | input j => rfl
  | @func n symbol refs =>
    have hb : (∀ ref ∈ List.ofFn refs, ref < cache.length) ↔ ∀ i, refs i < cache.length := by
      constructor
      · intro h i
        exact h (refs i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
      · intro h ref hr
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
        exact h i
    by_cases h : ∀ i, refs i < cache.length
    · have ht : (List.ofFn refs).length = n ∧ ∀ ref ∈ List.ofFn refs, ref < cache.length :=
        ⟨List.length_ofFn, hb.mpr h⟩
      change (if (List.ofFn refs).length = n ∧ ∀ ref ∈ List.ofFn refs, ref < cache.length then
        some (evalOperation cache ⟨n, symbol⟩ (List.ofFn refs)) else none) = _
      rw [ite_eq_left ht, Circuit.Gate.eval, dite_eq_left h]
      apply congrArg some
      unfold evalOperation
      apply congrArg (FirstOrder.Language.Structure.funMap (L := Equational.language σ) symbol)
      funext i
      rw [List.getD_eq_getElem (List.ofFn refs) 0 (by simpa only [List.length_ofFn] using i.isLt)]
      simp only [List.getElem_ofFn]
      exact List.getD_eq_getElem _ _ (h i)
    · have ht : ¬((List.ofFn refs).length = n ∧ ∀ ref ∈ List.ofFn refs, ref < cache.length) := fun ht => h (hb.mp ht.2)
      change (if (List.ofFn refs).length = n ∧ ∀ ref ∈ List.ofFn refs, ref < cache.length then
        some (evalOperation cache ⟨n, symbol⟩ (List.ofFn refs)) else none) = _
      rw [ite_eq_right ht, Circuit.Gate.eval, dite_eq_right h]

omit [Fintype (Operation σ)] in
private theorem foldl_none (context : Context) (gates : List (RawGate σ)) :
    gates.foldl (step (Value := Value) context) none = none := by
  induction gates with
  | nil => rfl
  | cons gate gates ih => exact ih

omit [Fintype (Operation σ)] in
theorem run_view (context : Context) (gates : List (Circuit.Gate σ ℕ)) :
    run context (gates.map viewGate) = Circuit.runFrom (lookup context : ℕ → Value) gates [] := by
  have h (cache : Cache Value) (gates : List (Circuit.Gate σ ℕ)) :
      (gates.map viewGate).foldl (step context) (some cache) = Circuit.runFrom (lookup context : ℕ → Value) gates cache := by
    induction gates generalizing cache with
    | nil => rfl
    | cons gate gates ih =>
      simp only [List.map_cons, List.foldl_cons, step, Option.bind_some, evalGate_view, Circuit.runFrom]
      cases he : gate.eval (lookup context : ℕ → Value) cache with
      | none => exact foldl_none context _
      | some value => exact ih (cache ++ [value])
  exact h [] gates


noncomputable def read (cache : Cache Value) (ref : ℕ) : Option Value :=
  if ref < cache.length then some (cache.getD ref fallback) else none

private theorem read_polyTime : ComputableInPolyTime
    (fun p : Cache Value × ℕ => read p.1 p.2) (encPair cacheEncoding encNat) (encOption valueEncoding) := by
  have hcache := fst (cacheEncoding (Value := Value)) encNat
  have href := snd (cacheEncoding (Value := Value)) encNat
  have hcount := unary_to_binary.comp ((length_list valueEncoding).comp hcache)
  have h := (binary_lt' href hcount).ite
    ((optionSome (valueEncoding (Value := Value))).comp binaryLookup_polyTime) (const none)
  convert h using 1
  funext p
  simp only [read, Function.comp_def, decide_eq_true_eq]

omit [Fintype (Operation σ)] [Fintype Value] in
theorem read_eq_getElem? (cache : Cache Value) (ref : ℕ) : read cache ref = cache[ref]? := by
  by_cases h : ref < cache.length
  · simp only [read, ite_eq_left h, List.getD_eq_getElem _ _ h, List.getElem?_eq_getElem h]
  · rw [read, ite_eq_right h]
    symm
    apply List.getElem?_eq_none
    omega

noncomputable def readPair (cache : Cache Value) (refs : ℕ × ℕ) : Option (Value × Value) := do
  let left ← read cache refs.1
  let right ← read cache refs.2
  return (left, right)

private theorem readPair_polyTime : ComputableInPolyTime
    (fun p : Cache Value × (ℕ × ℕ) => readPair p.1 p.2)
    (encPair cacheEncoding (encPair encNat encNat)) (encOption (encPair valueEncoding valueEncoding)) := by
  let input := encPair (cacheEncoding (Value := Value)) (encPair encNat encNat)
  have hc := fst (cacheEncoding (Value := Value)) (encPair encNat encNat)
  have hl : ComputableInPolyTime (fun p : Cache Value × (ℕ × ℕ) => p.2.1) input encNat := by fun_prop
  have hr : ComputableInPolyTime (fun p : Cache Value × (ℕ × ℕ) => p.2.2) input encNat := by fun_prop
  have h := optionPairWithInput_polyTime (read_polyTime.comp (hc.prod hl)) (read_polyTime.comp (hc.prod hr))
  convert h using 1
  funext p
  unfold readPair
  dsimp only [Function.comp_def]
  cases hl : read p.1 p.2.1 <;> cases hr : read p.1 p.2.2 <;> rfl

noncomputable def evaluate (context : Context) (data : RawEquation σ) : Option (Value × Value) :=
  (run context data.1).bind (fun cache => readPair cache data.2)

theorem evaluate_polyTime : ComputableInPolyTime
    (fun p : Context × RawEquation σ => (evaluate p.1 p.2 : Option (Value × Value)))
    (encPair contextEncoding dataEncoding) (encOption (encPair valueEncoding valueEncoding)) := by
  let input := encPair contextEncoding (dataEncoding (σ := σ))
  have hc := fst contextEncoding (dataEncoding (σ := σ))
  have hg : ComputableInPolyTime (fun p : Context × RawEquation σ => p.2.1) input (encList gateEncoding) := by fun_prop
  have hrun := (run_polyTime (σ := σ) (Value := Value)).comp (hc.prod hg)
  have hr : ComputableInPolyTime (fun p : (Context × RawEquation σ) × Cache Value => p.1.2.2)
      (encPair input cacheEncoding) (encPair encNat encNat) := by fun_prop
  have hcache := snd input (cacheEncoding (Value := Value))
  have hbody := readPair_polyTime.comp (hcache.prod hr)
  have h := hrun.optionElimWithInput (body := fun (p : Context × RawEquation σ) cache => readPair cache p.2.2)
    (const none) hbody
  convert h using 1
  funext p
  unfold evaluate
  dsimp only [Function.comp_def]
  cases run (Value := Value) p.1 p.2.1 <;> rfl

omit [Fintype (Operation σ)] in
theorem evaluate_view (context : Context) (equation : Circuit.Equation σ ℕ) :
    (evaluate context (view equation) : Option (Value × Value)) = equation.eval (lookup context) := by
  unfold evaluate view
  rw [run_view]
  unfold Circuit.Equation.eval
  cases h : Circuit.runFrom (lookup context : ℕ → Value) equation.gates [] with
  | none => rfl
  | some cache =>
    change readPair cache (equation.left, equation.right) = (do
      let left ← cache[equation.left]?
      let right ← cache[equation.right]?
      pure (left, right))
    simp only [readPair, read_eq_getElem?]

end KFOL.Complexity.CircuitMachine
