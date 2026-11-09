module
public import KFOL.Complexity.FullTermMachines
public import KFOL.Complexity.OptionTraversal
/-! # Cached original trees, exact evaluation traces and uniformly certified parser steps -/

@[expose] public section
namespace KFOL.Complexity.FullTermFold
open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FullTermCode
variable {Context Value : Type}

def fold (leaf : Context → ℕ → Value) (node : Context → Operation → List Value → Value)
    (context : Context) : Raw → Value
  | .var j => leaf context j
  | @FirstOrder.Language.Term.func _ _ n function children =>
    node context ⟨n, function⟩ (List.ofFn (fun i => fold leaf node context (children i)))

def cost : Raw → ℕ
  | .var _ => 1
  | @FirstOrder.Language.Term.func _ _ n _ children =>
      1 + (List.ofFn (fun i => cost (children i))).sum + n

private theorem sum_cost_bound (terms : List (Raw))
    (hyp : ∀ term ∈ terms, cost term + 1 ≤ 2 * (encode term).length) :
    (terms.map cost).sum + terms.length ≤ 2 * (terms.map (fun t => (encode t).length)).sum := by
  induction terms with
  | nil => simp
  | cons term terms ih =>
    have ht := hyp term (by simp)
    have hs := ih (fun t ht => hyp t (by simp [ht]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- Each tree step and every child-return step is charged to original syntax. -/
theorem cost_le_code (term : Raw) : cost term + 1 ≤ 2 * (encode term).length := by
  induction term with
  | var j => simp [cost, encode_var]
  | @func n function children ih =>
    have hs := sum_cost_bound (List.ofFn children) (by
      intro t ht
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht
      exact ih i)
    simp only [List.map_ofFn, List.length_ofFn, Function.comp_def] at hs
    simp only [cost, encode_func, List.length_cons, List.length_append, List.length_flatten,
      List.map_ofFn, Function.comp_def]
    omega

private theorem ofFn_getD {α : Type} (fallback : α) (values : List α) {n : ℕ} (h : values.length = n) :
    List.ofFn (fun i : Fin n => values.getD i.val fallback) = values := by
  apply List.ext_getElem (by simp [h])
  intro i hi hi'
  simp only [List.getElem_ofFn, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi', Option.getD_some]

abbrev Cached (Value : Type) := Raw × Value
abbrev Frame (Value : Type) := Operation × List (Cached Value)
abbrev Data (Value : Type) :=
  List (Frame Value) × (Option (Cached Value) × List Bool)
abbrev State (Value : Type) := Option (Data Value)

noncomputable abbrev cachedEncoding (valueEncoding : Value ↪ List Bool) :=
  encPair (FullTermMachines.termEncoding ) valueEncoding
noncomputable abbrev frameEncoding (valueEncoding : Value ↪ List Bool) :=
  encPair (FullTermMachines.operationEncoding ) (encList (cachedEncoding  valueEncoding))
noncomputable abbrev dataEncoding (valueEncoding : Value ↪ List Bool) :=
  encPair (encList (frameEncoding  valueEncoding))
    (encPair (encOption (cachedEncoding  valueEncoding)) encBits)
noncomputable abbrev stateEncoding (valueEncoding : Value ↪ List Bool) :=
  encOption (dataEncoding  valueEncoding)

noncomputable def cacheNode (node : Context → Operation → List Value → Value)
    (context : Context) (operation : Operation) (children : List (Cached Value)) : Cached Value :=
  (FullTermMachines.construct operation (children.map Prod.fst),
    node context operation (children.map Prod.snd))

private theorem construct_fold (leaf : Context → ℕ → Value)
    (node : Context → Operation → List Value → Value) (context : Context)
    (operation : Operation) (children : List (Raw))
    (h : children.length = operation.1) :
    fold leaf node context (FullTermMachines.construct operation children) =
      node context operation (children.map (fold leaf node context)) := by
  unfold FullTermMachines.construct
  simp only [fold]
  congr 1
  change List.ofFn ((fold leaf node context) ∘ fun i : Fin operation.1 => children.getD i.val (.var 0)) = _
  rw [← List.map_ofFn, ofFn_getD (.var 0) children h]

private theorem construct_code (operation : Operation) (children : List (Raw))
    (h : children.length = operation.1) :
    encode (FullTermMachines.construct operation children) =
      true :: (Words.delimit (encodeOperation operation) ++ (children.map (encode)).flatten) := by
  unfold FullTermMachines.construct
  rw [encode_func]
  congr 2
  change List.flatten (List.ofFn ((encode) ∘ fun i : Fin operation.1 => children.getD i.val (.var 0))) = _
  rw [← List.map_ofFn, ofFn_getD (.var 0) children h]

def cachedValid (leaf : Context → ℕ → Value) (node : Context → Operation → List Value → Value)
    (context : Context) (cache : Cached Value) : Prop :=
  cache.2 = fold leaf node context cache.1

private theorem cacheNode_valid (leaf : Context → ℕ → Value)
    (node : Context → Operation → List Value → Value) (context : Context)
    (operation : Operation) (children : List (Cached Value))
    (h : children.length = operation.1) (hv : ∀ child ∈ children, cachedValid leaf node context child) :
    cachedValid leaf node context (cacheNode node context operation children) := by
  unfold cachedValid cacheNode
  rw [construct_fold leaf node context operation _ (by simpa using h)]
  change node context operation (children.map Prod.snd) = _
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro child hc
  exact hv child hc

noncomputable def frameWeight (frame : Frame Value) : ℕ :=
  1 + (Words.delimit (encodeOperation frame.1)).length +
    (frame.2.map (fun cache => (encode cache.1).length)).sum

noncomputable def dataWeight (data : Data Value) : ℕ :=
  (data.1.map frameWeight).sum + data.2.1.elim 0 (fun cache => (encode cache.1).length) + data.2.2.length

noncomputable def stateWeight (state : State Value) : ℕ := state.elim 0 dataWeight

noncomputable def accept (node : Context → Operation → List Value → Value) (context : Context)
    (stack : List (Frame Value)) (focus : Cached Value) (rest : List Bool) : Option (Data Value) :=
  match stack with
  | [] => some ([], some focus, rest)
  | (operation, children) :: tail =>
    let children := children ++ [focus]
    if children.length < operation.1 then some ((operation, children) :: tail, none, rest)
    else if children.length = operation.1 then
      some (tail, some (cacheNode node context operation children), rest)
    else none

noncomputable def readPayload (leaf : Context → ℕ → Value)
    (node : Context → Operation → List Value → Value) (context : Context)
    (stack : List (Frame Value)) (tag : Bool) (payload : List Bool × List Bool) : Option (Data Value) :=
  if tag then
    (decodeOperation payload.1).map (fun operation =>
      if operation.1 = 0 then (stack, some (cacheNode node context operation []), payload.2)
      else ((operation, []) :: stack, none, payload.2))
  else (Words.BinaryNatCode.decode? payload.1).map (fun j => (stack, some (.var j, leaf context j), payload.2))

noncomputable def readToken (leaf : Context → ℕ → Value)
    (node : Context → Operation → List Value → Value) (context : Context)
    (stack : List (Frame Value)) (word : List Bool) : Option (Data Value) :=
  if word.isEmpty then none else
    (Words.unpair? word.tail).elim none (readPayload leaf node context stack (word.headD false))

noncomputable def next (leaf : Context → ℕ → Value)
    (node : Context → Operation → List Value → Value) (context : Context)
    (data : Data Value) : Option (Data Value) :=
  data.2.1.elim (readToken leaf node context data.1 data.2.2)
    (fun focus => accept node context data.1 focus data.2.2)

noncomputable def step (leaf : Context → ℕ → Value)
    (node : Context → Operation → List Value → Value) (context : Context)
    (state : Option (Data Value)) : Option (Data Value) :=
  state.elim none (next leaf node context)

private theorem accept_weight (node : Context → Operation → List Value → Value)
    (context : Context) (stack : List (Frame Value)) (focus : Cached Value) (rest : List Bool) :
    stateWeight (accept node context stack focus rest) ≤ dataWeight (stack, some focus, rest) := by
  cases stack with
  | nil => simp [accept, stateWeight, dataWeight]
  | cons frame stack =>
    rcases frame with ⟨operation, children⟩
    simp only [accept]
    split
    next hlt =>
      simp only [stateWeight, dataWeight, frameWeight, List.map_cons, List.sum_cons,
        List.map_append, List.map_nil, List.sum_nil, List.sum_append,
        Option.elim_none, Option.elim_some]
      omega
    next hlt =>
      split
      next heq =>
        have hc := construct_code operation ((children ++ [focus]).map Prod.fst)
          (by simpa only [List.length_map] using heq)
        change (stack.map frameWeight).sum +
          (encode (FullTermMachines.construct operation ((children ++ [focus]).map Prod.fst))).length +
          rest.length ≤ frameWeight (operation, children) + (stack.map frameWeight).sum +
            (encode focus.1).length + rest.length
        rw [hc]
        simp only [frameWeight, List.length_cons, List.length_append, List.length_flatten,
          List.map_map, Function.comp_def, List.map_append, List.map_cons, List.map_nil,
          List.sum_append, List.sum_cons, List.sum_nil]
        simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.zero_add]
        apply le_of_eq
        congr 1
      next => simp [stateWeight]

private theorem readPayload_weight (leaf : Context → ℕ → Value)
    (node : Context → Operation → List Value → Value) (context : Context)
    (stack : List (Frame Value)) (tag : Bool) (payload : List Bool × List Bool) :
    stateWeight (readPayload leaf node context stack tag payload) ≤
      (stack.map frameWeight).sum + 1 + (Words.delimit payload.1).length + payload.2.length := by
  cases tag with
  | false =>
    simp only [readPayload, Bool.false_eq_true, ite_false]
    cases hd : Words.BinaryNatCode.decode? payload.1 with
    | none => simp [stateWeight]
    | some j =>
      have he := (Words.BinaryNatCode.decode?_eq_some_iff payload.1 j).mp hd
      simp only [Option.map_some, stateWeight, dataWeight, Option.elim_some, encode_var,
        List.length_cons]
      rw [he]
      omega
  | true =>
    simp only [readPayload, ite_true]
    cases hd : decodeOperation payload.1 with
    | none => simp [stateWeight]
    | some operation =>
      have he := encodeOperation_of_decodeOperation hd
      simp only [Option.map_some]
      split
      next hz =>
        have hc := construct_code operation [] hz.symm
        simp only [stateWeight, dataWeight, cacheNode, Option.elim_some, List.map_nil,
          hc, List.flatten_nil, List.append_nil, List.length_cons]
        rw [he]
        omega
      next =>
        change frameWeight (operation, ([] : List (Cached Value))) + (stack.map frameWeight).sum + 0 +
          payload.2.length ≤ _
        simp only [frameWeight, List.map_nil, List.sum_nil]
        rw [he]
        omega

private theorem readToken_weight (leaf : Context → ℕ → Value)
    (node : Context → Operation → List Value → Value) (context : Context)
    (stack : List (Frame Value)) (word : List Bool) :
    stateWeight (readToken leaf node context stack word) ≤
      (stack.map frameWeight).sum + word.length := by
  cases word with
  | nil => simp [readToken, stateWeight]
  | cons tag word =>
    simp only [readToken, List.isEmpty_cons, Bool.false_eq_true, ite_false,
      List.tail_cons, List.headD_cons]
    cases hp : Words.unpair? word with
    | none => simp [stateWeight]
    | some payload =>
      have he := Words.eq_delimit_append_of_unpair?_eq_some hp
      simpa only [Option.elim_some, he, List.length_cons, List.length_append,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        readPayload_weight leaf node context stack tag payload

/-- The serialized source forest never grows: every completed AST replaces its
operation header and exactly its consumed child encodings. -/
theorem step_weight (leaf : Context → ℕ → Value)
    (node : Context → Operation → List Value → Value) (context : Context) (state : State Value) :
    stateWeight (step leaf node context state) ≤ stateWeight state := by
  cases state with
  | none => rfl
  | some data =>
    rcases data with ⟨stack, focus, rest⟩
    cases focus with
    | none => exact readToken_weight leaf node context stack rest
    | some focus => exact accept_weight node context stack focus rest

def dataValid (leaf : Context → ℕ → Value) (node : Context → Operation → List Value → Value)
    (context : Context) (data : Data Value) : Prop :=
  (∀ frame ∈ data.1, ∀ cache ∈ frame.2, cachedValid leaf node context cache) ∧
    ∀ cache, data.2.1 = some cache → cachedValid leaf node context cache

def stateValid (leaf : Context → ℕ → Value) (node : Context → Operation → List Value → Value)
    (context : Context) (state : State Value) : Prop := state.elim True (dataValid leaf node context)

private theorem accept_valid (leaf : Context → ℕ → Value)
    (node : Context → Operation → List Value → Value) (context : Context)
    (stack : List (Frame Value)) (focus : Cached Value) (rest : List Bool)
    (hv : dataValid leaf node context (stack, some focus, rest)) :
    stateValid leaf node context (accept node context stack focus rest) := by
  cases stack with
  | nil => exact hv
  | cons frame stack =>
    have hfocus : cachedValid leaf node context focus := hv.2 focus rfl
    have htail : ∀ f ∈ stack, ∀ c ∈ f.2, cachedValid leaf node context c := by
      intro f hf
      exact hv.1 f (List.mem_cons_of_mem _ hf)
    have hchildren : ∀ c ∈ frame.2 ++ [focus], cachedValid leaf node context c := by
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact hv.1 frame (List.mem_cons_self ..) c hc
      · simpa only [List.mem_singleton.mp hc] using hfocus
    simp only [accept]
    split
    next hlt =>
      constructor
      · intro f hf c hc
        rcases List.mem_cons.mp hf with rfl | hf
        · exact hchildren c hc
        · exact htail f hf c hc
      · intro c h
        cases h
    next hlt =>
      split
      next heq =>
        constructor
        · exact htail
        · intro c hc
          cases Option.some.inj hc
          exact cacheNode_valid leaf node context frame.1 _ heq hchildren
      next => trivial

private theorem readPayload_valid (leaf : Context → ℕ → Value)
    (node : Context → Operation → List Value → Value) (context : Context)
    (stack : List (Frame Value)) (tag : Bool) (payload : List Bool × List Bool)
    (hv : ∀ frame ∈ stack, ∀ cache ∈ frame.2, cachedValid leaf node context cache) :
    stateValid leaf node context (readPayload leaf node context stack tag payload) := by
  cases tag with
  | false =>
    simp only [readPayload, Bool.false_eq_true, ite_false]
    cases Words.BinaryNatCode.decode? payload.1 with
    | none => trivial
    | some j =>
      constructor
      · exact hv
      · intro cache hc
        cases Option.some.inj hc
        rfl
  | true =>
    simp only [readPayload, ite_true]
    cases decodeOperation payload.1 with
    | none => trivial
    | some operation =>
      simp only [Option.map_some]
      split
      next hz =>
        constructor
        · exact hv
        · intro cache hc
          cases Option.some.inj hc
          exact cacheNode_valid leaf node context operation [] hz.symm (by simp)
      next =>
        constructor
        · intro frame hf cache hc
          rcases List.mem_cons.mp hf with rfl | hf
          · cases hc
          · exact hv frame hf cache hc
        · intro cache hc
          cases hc

/-- Every stored annotation continues to be the mathematical fold of its own
stored subtree. The proof is independent of any running-time bound. -/
theorem step_valid (leaf : Context → ℕ → Value)
    (node : Context → Operation → List Value → Value) (context : Context) (state : State Value)
    (hv : stateValid leaf node context state) :
    stateValid leaf node context (step leaf node context state) := by
  cases state with
  | none => trivial
  | some data =>
    rcases data with ⟨stack, focus, rest⟩
    cases focus with
    | some focus => exact accept_valid leaf node context stack focus rest hv
    | none =>
      change stateValid leaf node context (readToken leaf node context stack rest)
      unfold readToken
      split
      · trivial
      · cases Words.unpair? rest.tail with
        | none => trivial
        | some payload => exact readPayload_valid leaf node context stack _ payload hv.1

def sourceCache (leaf : Context → ℕ → Value) (node : Context → Operation → List Value → Value)
    (context : Context) (term : Raw) : Cached Value := (term, fold leaf node context term)

private theorem cacheNode_ofFn (leaf : Context → ℕ → Value)
    (node : Context → Operation → List Value → Value) (context : Context)
    {n : ℕ} (function : RawSymbol n) (children : Fin n → Raw) :
    cacheNode node context ⟨n, function⟩ (List.ofFn (fun i => sourceCache leaf node context (children i))) =
      sourceCache leaf node context (.func function children) := by
  unfold cacheNode sourceCache
  simp only [List.map_ofFn, Function.comp_def, FullTermMachines.construct_ofFn, fold]

private theorem step_variable (leaf : Context → ℕ → Value)
    (node : Context → Operation → List Value → Value) (context : Context)
    (stack : List (Frame Value)) (j : ℕ) (rest : List Bool) :
    step leaf node context (some (stack, none, encode (.var j) ++ rest)) =
      some (stack, some (sourceCache leaf node context (.var j)), rest) := by
  simp [step, next, readToken, readPayload, encode_var, sourceCache, fold]

private theorem step_operation (leaf : Context → ℕ → Value)
    (node : Context → Operation → List Value → Value) (context : Context)
    (stack : List (Frame Value)) (operation : Operation) (body : List Bool) :
    step leaf node context (some (stack, none, true :: (Words.delimit (encodeOperation operation) ++ body))) =
      if operation.1 = 0 then some (stack, some (cacheNode node context operation []), body)
      else some ((operation, []) :: stack, none, body) := by
  simp [step, next, readToken, readPayload]
  split <;> rfl

private theorem sum_succ_cost (terms : List (Raw)) :
    (terms.map (fun t => cost t + 1)).sum = (terms.map cost).sum + terms.length := by
  induction terms with
  | nil => rfl
  | cons t terms ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega

private theorem trace_children (leaf : Context → ℕ → Value)
    (node : Context → Operation → List Value → Value) (context : Context)
    (terms : List (Raw))
    (hyp : ∀ t ∈ terms, ∀ stack rest,
      (step leaf node context)^[cost t] (some (stack, none, encode t ++ rest)) =
        some (stack, some (sourceCache leaf node context t), rest))
    (operation : Operation) (done : List (Cached Value))
    (stack : List (Frame Value)) (rest : List Bool)
    (hne : terms ≠ []) (hlen : done.length + terms.length = operation.1) :
    (step leaf node context)^[(terms.map (fun t => cost t + 1)).sum]
      (some ((operation, done) :: stack, none, (terms.map (encode)).flatten ++ rest)) =
      some (stack, some (cacheNode node context operation
        (done ++ terms.map (sourceCache leaf node context))), rest) := by
  induction terms generalizing done with
  | nil => contradiction
  | cons t terms ih =>
    have hc : ((t :: terms).map (fun t => cost t + 1)).sum =
        (terms.map (fun t => cost t + 1)).sum + (cost t + 1) := by simp; omega
    rw [hc, Function.iterate_add_apply, Function.iterate_succ_apply']
    simp only [List.map_cons, List.flatten_cons, List.append_assoc]
    rw [hyp t (List.mem_cons_self ..)]
    simp only [step, next, accept, Option.elim_some]
    cases terms with
    | nil =>
      have he : (done ++ [sourceCache leaf node context t]).length = operation.1 := by
        simp only [List.length_cons, List.length_nil] at hlen
        simp only [List.length_append, List.length_singleton]
        omega
      simp only [he, lt_self_iff_false, ite_false, ite_true, List.map_nil, List.sum_nil,
        List.flatten_nil, List.nil_append, Function.iterate_zero_apply]
    | cons t' terms =>
      have hlt : (done ++ [sourceCache leaf node context t]).length < operation.1 := by
        simp only [List.length_cons] at hlen
        simp only [List.length_append, List.length_singleton]
        omega
      simp only [hlt, ite_true]
      rw [ih (fun u hu => hyp u (List.mem_cons_of_mem _ hu)) _ (by simp) (by
        simp only [List.length_append, List.length_cons, List.length_nil] at *
        omega)]
      simp only [List.map_cons, List.append_assoc, List.singleton_append]

/-- The actual machine evaluates an original subtree and preserves every
surrounding frame and suffix at the exact tree/child-return clock. -/
theorem trace_term (leaf : Context → ℕ → Value)
    (node : Context → Operation → List Value → Value) (context : Context)
    (term : Raw) (stack : List (Frame Value)) (rest : List Bool) :
    (step leaf node context)^[cost term] (some (stack, none, encode term ++ rest)) =
      some (stack, some (sourceCache leaf node context term), rest) := by
  induction term generalizing stack rest with
  | var j => simpa only [cost, Function.iterate_one] using step_variable leaf node context stack j rest
  | @func n function children ih =>
    have hc : cost (.func function children) =
        (List.ofFn (fun i => cost (children i) + 1)).sum + 1 := by
      have hs := sum_succ_cost (List.ofFn children)
      simp only [List.map_ofFn, List.length_ofFn, Function.comp_def] at hs
      simp only [cost]
      omega
    rw [hc, Function.iterate_succ_apply]
    rw [encode_func]
    simp only [List.cons_append, List.append_assoc]
    rw [step_operation]
    by_cases hn : n = 0
    · subst n
      simp only [ite_true, List.ofFn_zero, List.flatten_nil, List.nil_append, List.sum_nil,
        Function.iterate_zero_apply]
      have he := cacheNode_ofFn leaf node context function children
      simpa only [List.ofFn_zero] using congrArg (fun cache => some (stack, some cache, rest)) he
    · simp only [hn, ite_false]
      have ht := trace_children leaf node context (List.ofFn children)
        (by intro t ht stack rest; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht; exact ih i stack rest)
        (⟨n, function⟩ : Operation) [] stack rest
        (by intro h; have he := congrArg List.length h; simp only [List.length_ofFn, List.length_nil] at he; contradiction)
        (by simp)
      simp only [List.map_ofFn, List.nil_append, Function.comp_def, cacheNode_ofFn] at ht
      exact ht

variable {contextEncoding : Context ↪ List Bool} {valueEncoding : Value ↪ List Bool}

/-- Joint certification of the original context, exact AST constructor, and
algebra callback; intermediate child lists remain explicitly stored. -/
theorem cacheNode_polyTime (node : Context → Operation → List Value → Value)
    (hnode : ComputableInPolyTime (fun p : Context × (Operation × List Value) => node p.1 p.2.1 p.2.2)
      (encPair contextEncoding (encPair FullTermMachines.operationEncoding (encList valueEncoding))) valueEncoding) :
    ComputableInPolyTime
      (fun p : Context × (Operation × List (Cached Value)) => cacheNode node p.1 p.2.1 p.2.2)
      (encPair contextEncoding (encPair FullTermMachines.operationEncoding (encList (cachedEncoding  valueEncoding))))
      (cachedEncoding  valueEncoding) := by
  let input := encPair contextEncoding
    (encPair (FullTermMachines.operationEncoding ) (encList (cachedEncoding  valueEncoding)))
  have hc := fst contextEncoding (encPair (FullTermMachines.operationEncoding )
    (encList (cachedEncoding  valueEncoding)))
  have hop : ComputableInPolyTime (fun p : Context × (Operation × List (Cached Value)) => p.2.1)
      input FullTermMachines.operationEncoding := by fun_prop
  have hchildren : ComputableInPolyTime (fun p : Context × (Operation × List (Cached Value)) => p.2.2)
      input (encList (cachedEncoding  valueEncoding)) := by fun_prop
  have ht : ComputableInPolyTime
      (fun p : (Context × (Operation × List (Cached Value))) × Cached Value => p.2.1)
      (encPair input (cachedEncoding  valueEncoding)) FullTermMachines.termEncoding := by fun_prop
  have hv : ComputableInPolyTime
      (fun p : (Context × (Operation × List (Cached Value))) × Cached Value => p.2.2)
      (encPair input (cachedEncoding  valueEncoding)) valueEncoding := by fun_prop
  have hterms := mapWithInput (f := fun (_ : Context × (Operation × List (Cached Value))) cache => cache.1)
    hchildren ht
  have hvalues := mapWithInput (f := fun (_ : Context × (Operation × List (Cached Value))) cache => cache.2)
    hchildren hv
  exact (FullTermMachines.construct_polyTime.comp (hop.prod hterms)).prod
    (hnode.comp (hc.prod (hop.prod hvalues)))

abbrev PayloadInput (Context Value : Type) :=
  (Context × List (Frame Value)) × (Bool × (List Bool × List Bool))
noncomputable abbrev payloadEncoding :=
  encPair (encPair contextEncoding (encList (frameEncoding  valueEncoding)))
    (encPair encBool (encPair encBits encBits))

theorem readPayload_polyTime (leaf : Context → ℕ → Value)
    (node : Context → Operation → List Value → Value)
    (hleaf : ComputableInPolyTime (fun p : Context × ℕ => leaf p.1 p.2)
      (encPair contextEncoding encNat) valueEncoding)
    (hnode : ComputableInPolyTime (fun p : Context × (Operation × List Value) => node p.1 p.2.1 p.2.2)
      (encPair contextEncoding (encPair FullTermMachines.operationEncoding (encList valueEncoding))) valueEncoding) :
    ComputableInPolyTime (fun p : PayloadInput Context Value => readPayload leaf node p.1.1 p.1.2 p.2.1 p.2.2)
      (payloadEncoding (contextEncoding := contextEncoding) (valueEncoding := valueEncoding))
      (stateEncoding  valueEncoding) := by
  let input := payloadEncoding  (contextEncoding := contextEncoding) (valueEncoding := valueEncoding)
  have hc : ComputableInPolyTime (fun p : PayloadInput Context Value => p.1.1) input contextEncoding := by fun_prop
  have hs : ComputableInPolyTime (fun p : PayloadInput Context Value => p.1.2) input
      (encList (frameEncoding  valueEncoding)) := by fun_prop
  have hcode : ComputableInPolyTime (fun p : PayloadInput Context Value => p.2.2.1) input encBits := by fun_prop
  have hr : ComputableInPolyTime (fun p : PayloadInput Context Value => p.2.2.2) input encBits := by fun_prop
  have htag : ComputableInPolyTime (fun p : PayloadInput Context Value => p.2.1) input encBool := by fun_prop
  let inner := encPair input FullTermMachines.operationEncoding
  have hop := snd input FullTermMachines.operationEncoding
  have hcOp := hc.comp (fst input FullTermMachines.operationEncoding)
  have hsOp := hs.comp (fst input FullTermMachines.operationEncoding)
  have hrOp := hr.comp (fst input FullTermMachines.operationEncoding)
  have hcache := (cacheNode_polyTime node hnode).comp (hcOp.prod (hop.prod (const [])))
  have hzero := hsOp.prod (((optionSome (cachedEncoding valueEncoding)).comp hcache).prod hrOp)
  have hstack := cons' (hop.prod (const [])) hsOp
  have hnonzero := hstack.prod ((const (encOut := encOption (cachedEncoding valueEncoding)) (none : Option (Cached Value))).prod hrOp)
  have htest := decide_eq' (FullTermMachines.arity_polyTime.comp hop) (const 0)
  have hbody : ComputableInPolyTime
      (fun p : PayloadInput Context Value × Operation =>
        if p.2.1 = 0 then (p.1.1.2, some (cacheNode node p.1.1.1 p.2 []), p.1.2.2.2)
        else ((p.2, []) :: p.1.1.2, none, p.1.2.2.2)) inner (dataEncoding valueEncoding) := by
    convert htest.ite hzero hnonzero using 1
    funext p
    simp only [Function.comp_def, decide_eq_true_eq]
  have hdecode := FullTermMachines.decodeOperation_polyTime.comp hcode
  have hfunctions := hdecode.optionMapWithInput
    (f := fun (p : PayloadInput Context Value) operation =>
      if operation.1 = 0 then (p.1.2, some (cacheNode node p.1.1 operation []), p.2.2.2)
      else ((operation, []) :: p.1.2, none, p.2.2.2)) hbody
  have hc' := hc.comp (fst input encNat)
  have hs' := hs.comp (fst input encNat)
  have hr' := hr.comp (fst input encNat)
  have hj := snd input encNat
  have hvalue := hleaf.comp (hc'.prod hj)
  have hsyntax := (FullTermMachines.var_polyTime ).comp hj
  have hleafResult := hs'.prod (((optionSome (cachedEncoding  valueEncoding)).comp (hsyntax.prod hvalue)).prod hr')
  have hvariables := (Dictionary.decode_polyTime.comp hcode).optionMapWithInput
    (f := fun (p : PayloadInput Context Value) j => (p.1.2, some ((.var j : Raw), leaf p.1.1 j), p.2.2.2)) hleafResult
  have h := htag.ite hfunctions hvariables
  convert h using 1
  funext p
  simp only [readPayload, Function.comp_def]

abbrev ReadInput (Context Value : Type) := (Context × List (Frame Value)) × List Bool
noncomputable abbrev readEncoding :=
  encPair (encPair contextEncoding (encList (frameEncoding  valueEncoding))) encBits

theorem readToken_polyTime (leaf : Context → ℕ → Value)
    (node : Context → Operation → List Value → Value)
    (hleaf : ComputableInPolyTime (fun p : Context × ℕ => leaf p.1 p.2)
      (encPair contextEncoding encNat) valueEncoding)
    (hnode : ComputableInPolyTime (fun p : Context × (Operation × List Value) => node p.1 p.2.1 p.2.2)
      (encPair contextEncoding (encPair FullTermMachines.operationEncoding (encList valueEncoding))) valueEncoding) :
    ComputableInPolyTime (fun p : ReadInput Context Value => readToken leaf node p.1.1 p.1.2 p.2)
      (readEncoding (contextEncoding := contextEncoding) (valueEncoding := valueEncoding))
      (stateEncoding  valueEncoding) := by
  let input := readEncoding  (contextEncoding := contextEncoding) (valueEncoding := valueEncoding)
  have hword := snd (encPair contextEncoding (encList (frameEncoding  valueEncoding))) encBits
  have hparsed := Framing.unpair_polyTime.comp (bitsTail.comp hword)
  have hcontext : ComputableInPolyTime (fun p : (ReadInput Context Value) × (List Bool × List Bool) => p.1.1)
      (encPair input (encPair encBits encBits)) (encPair contextEncoding (encList (frameEncoding  valueEncoding))) := by fun_prop
  have htag := ((headD (encA := encBool) (encL := encBits) false).comp hword).comp
    (fst input (encPair encBits encBits))
  have hpayload := snd input (encPair encBits encBits)
  have hbody := (readPayload_polyTime leaf node hleaf hnode).comp (hcontext.prod (htag.prod hpayload))
  have hread := hparsed.optionElimWithInput (body := fun (p : ReadInput Context Value) payload =>
    readPayload leaf node p.1.1 p.1.2 (p.2.headD false) payload) (const none) hbody
  have h := (bitsIsEmpty.comp hword).ite (const none) hread
  convert h using 1
  funext p
  simp only [readToken, Function.comp_def]

abbrev AcceptInput (Context Value : Type) :=
  Context × (List (Frame Value) × (Cached Value × List Bool))
noncomputable abbrev acceptEncoding := encPair contextEncoding
  (encPair (encList (frameEncoding  valueEncoding)) (encPair (cachedEncoding  valueEncoding) encBits))

theorem accept_polyTime (node : Context → Operation → List Value → Value)
    (hnode : ComputableInPolyTime (fun p : Context × (Operation × List Value) => node p.1 p.2.1 p.2.2)
      (encPair contextEncoding (encPair FullTermMachines.operationEncoding (encList valueEncoding))) valueEncoding) :
    ComputableInPolyTime (fun p : AcceptInput Context Value => accept node p.1 p.2.1 p.2.2.1 p.2.2.2)
      (acceptEncoding (contextEncoding := contextEncoding) (valueEncoding := valueEncoding))
      (stateEncoding  valueEncoding) := by
  let input := acceptEncoding  (contextEncoding := contextEncoding) (valueEncoding := valueEncoding)
  let inner := encPair input (frameEncoding  valueEncoding)
  have hstack : ComputableInPolyTime (fun p : AcceptInput Context Value => p.2.1) input
      (encList (frameEncoding  valueEncoding)) := by fun_prop
  have hfocus : ComputableInPolyTime (fun p : AcceptInput Context Value => p.2.2.1) input
      (cachedEncoding  valueEncoding) := by fun_prop
  have hrest : ComputableInPolyTime (fun p : AcceptInput Context Value => p.2.2.2) input encBits := by fun_prop
  have hhead := (head? (frameEncoding  valueEncoding)).comp hstack
  have hfallback := (optionSome (dataEncoding  valueEncoding)).comp
    ((const []).prod (((optionSome (cachedEncoding  valueEncoding)).comp hfocus).prod hrest))
  have hc : ComputableInPolyTime (fun p : (AcceptInput Context Value) × Frame Value => p.1.1)
      inner contextEncoding := by fun_prop
  have htail := (tail (encA := frameEncoding  valueEncoding)).comp (hstack.comp (fst input (frameEncoding  valueEncoding)))
  have hf := hfocus.comp (fst input (frameEncoding  valueEncoding))
  have hr := hrest.comp (fst input (frameEncoding  valueEncoding))
  have hop : ComputableInPolyTime (fun p : (AcceptInput Context Value) × Frame Value => p.2.1)
      inner FullTermMachines.operationEncoding := by fun_prop
  have hold : ComputableInPolyTime (fun p : (AcceptInput Context Value) × Frame Value => p.2.2)
      inner (encList (cachedEncoding  valueEncoding)) := by fun_prop
  have hchildren := listAppend' hold (cons' hf (const []))
  have hcache := (cacheNode_polyTime node hnode).comp (hc.prod (hop.prod hchildren))
  have hkeep := (optionSome (dataEncoding  valueEncoding)).comp
    ((cons' (hop.prod hchildren) htail).prod ((const none).prod hr))
  have hdone := (optionSome (dataEncoding  valueEncoding)).comp
    (htail.prod (((optionSome (cachedEncoding  valueEncoding)).comp hcache).prod hr))
  have hcount := (length_list (cachedEncoding  valueEncoding)).comp hchildren
  have harity : ComputableInPolyTime (fun p : (AcceptInput Context Value) × Frame Value => p.2.1.1)
      inner encUnary := FullTermMachines.arity_polyTime.comp hop
  have hlt := unary_lt.comp (hcount.prod harity)
  have heq := decide_eq' hcount harity
  have hbody := hlt.ite hkeep (heq.ite hdone (const none))
  have hb : ComputableInPolyTime
      (fun p : (AcceptInput Context Value) × Frame Value =>
        let children := p.2.2 ++ [p.1.2.2.1]
        if children.length < p.2.1.1 then some ((p.2.1, children) :: p.1.2.1.tail, none, p.1.2.2.2)
        else if children.length = p.2.1.1 then
          some (p.1.2.1.tail, some (cacheNode node p.1.1 p.2.1 children), p.1.2.2.2)
        else none) inner (stateEncoding  valueEncoding) := by
    convert hbody using 1
    funext p
    simp only [decide_eq_true_eq, Function.comp_def]
  have h := hhead.optionElimWithInput (body := fun (p : AcceptInput Context Value) frame =>
      let children := frame.2 ++ [p.2.2.1]
      if children.length < frame.1.1 then some ((frame.1, children) :: p.2.1.tail, none, p.2.2.2)
      else if children.length = frame.1.1 then
        some (p.2.1.tail, some (cacheNode node p.1 frame.1 children), p.2.2.2)
      else none) hfallback hb
  convert h using 1
  funext p
  change accept node p.1 p.2.1 p.2.2.1 p.2.2.2 =
    p.2.1.head?.elim (some ([], some p.2.2.1, p.2.2.2)) _
  cases p.2.1 <;> rfl

theorem next_polyTime (leaf : Context → ℕ → Value)
    (node : Context → Operation → List Value → Value)
    (hleaf : ComputableInPolyTime (fun p : Context × ℕ => leaf p.1 p.2)
      (encPair contextEncoding encNat) valueEncoding)
    (hnode : ComputableInPolyTime (fun p : Context × (Operation × List Value) => node p.1 p.2.1 p.2.2)
      (encPair contextEncoding (encPair FullTermMachines.operationEncoding (encList valueEncoding))) valueEncoding) :
    ComputableInPolyTime (fun p : Context × Data Value => next leaf node p.1 p.2)
      (encPair contextEncoding (dataEncoding  valueEncoding)) (stateEncoding  valueEncoding) := by
  let input := encPair contextEncoding (dataEncoding  valueEncoding)
  have hc := fst contextEncoding (dataEncoding  valueEncoding)
  have hs : ComputableInPolyTime (fun p : Context × Data Value => p.2.1)
      input (encList (frameEncoding  valueEncoding)) := by fun_prop
  have hf : ComputableInPolyTime (fun p : Context × Data Value => p.2.2.1)
      input (encOption (cachedEncoding  valueEncoding)) := by fun_prop
  have hr : ComputableInPolyTime (fun p : Context × Data Value => p.2.2.2) input encBits := by fun_prop
  have hread := (readToken_polyTime leaf node hleaf hnode).comp ((hc.prod hs).prod hr)
  have hc' := hc.comp (fst input (cachedEncoding  valueEncoding))
  have hs' := hs.comp (fst input (cachedEncoding  valueEncoding))
  have hr' := hr.comp (fst input (cachedEncoding  valueEncoding))
  have hfocus := snd input (cachedEncoding  valueEncoding)
  have haccept := (accept_polyTime node hnode).comp (hc'.prod (hs'.prod (hfocus.prod hr')))
  have h := hf.optionElimWithInput (body := fun (p : Context × Data Value) focus =>
    accept node p.1 p.2.1 focus p.2.2.2) hread haccept
  convert h using 1
  funext p
  simp only [next, Function.comp_def]

/-- A complete parser/evaluator machine step, certified jointly in the captured
context and every intermediate cached subtree. -/
theorem step_polyTime (leaf : Context → ℕ → Value)
    (node : Context → Operation → List Value → Value)
    (hleaf : ComputableInPolyTime (fun p : Context × ℕ => leaf p.1 p.2)
      (encPair contextEncoding encNat) valueEncoding)
    (hnode : ComputableInPolyTime (fun p : Context × (Operation × List Value) => node p.1 p.2.1 p.2.2)
      (encPair contextEncoding (encPair FullTermMachines.operationEncoding (encList valueEncoding))) valueEncoding) :
    ComputableInPolyTime (fun p : Context × State Value => step leaf node p.1 p.2)
      (encPair contextEncoding (stateEncoding  valueEncoding)) (stateEncoding  valueEncoding) := by
  let input := encPair contextEncoding (stateEncoding  valueEncoding)
  have hc : ComputableInPolyTime (fun p : (Context × State Value) × Data Value => p.1.1)
      (encPair input (dataEncoding  valueEncoding)) contextEncoding := by fun_prop
  have hd := snd input (dataEncoding  valueEncoding)
  have hnext := (next_polyTime leaf node hleaf hnode).comp (hc.prod hd)
  have h := (snd contextEncoding (stateEncoding  valueEncoding)).optionElimWithInput
    (body := fun (p : Context × State Value) data => next leaf node p.1 data) (const none) hnext
  convert h using 1
  funext p
  simp only [step]

end KFOL.Complexity.FullTermFold
