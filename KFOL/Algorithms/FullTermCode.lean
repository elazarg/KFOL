module
public import KFOL.Definitions.Encoding
public import KFOL.Algorithms.Words
public import KFOL.Algorithms.GuardRecord
/-! # Exact uniform explicit-array full-term tree-code roundtrips -/

@[expose] public section
namespace KFOL.FullTermCode
@[simp] theorem operationPayload_delimit (word : List Bool) :
    operationPayload (Words.delimit word) = some word := by
  unfold operationPayload
  have hp := Words.unpair?_delimit_append word []
  simp only [List.append_nil] at hp
  rw [hp]
  rfl

theorem delimit_of_operationPayload {word payload : List Bool}
    (h : operationPayload word = some payload) : Words.delimit payload = word := by
  unfold operationPayload at h
  obtain ⟨⟨value,rest⟩,hp,he⟩ := Option.bind_eq_some_iff.mp h
  change (if rest.isEmpty then some value else none) = some payload at he
  split at he
  next hr =>
    cases Option.some.inj he
    have hrest : rest = [] := List.isEmpty_iff.mp hr
    simpa only [hrest,List.append_nil] using
      (Words.eq_delimit_append_of_unpair?_eq_some hp).symm
  next => cases he

@[simp] theorem decodeOperation_encodeOperation (operation : Operation) :
    decodeOperation (encodeOperation operation) = some operation := by
  rcases operation with ⟨n,operation⟩
  cases operation <;> simp [encodeOperation,decodeOperation]

theorem encodeOperation_of_decodeOperation {word : List Bool} {operation : Operation}
    (h : decodeOperation word = some operation) : encodeOperation operation = word := by
  cases word with
  | nil => simp [decodeOperation] at h
  | cons first word =>
    cases word with
    | nil => cases first <;> simp [decodeOperation] at h
    | cons second body =>
      cases first <;> cases second
      all_goals simp only [decodeOperation] at h
      all_goals first
      | cases h
      | obtain ⟨payload,hpayload,h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨value,hvalue,he⟩ := Option.bind_eq_some_iff.mp h
        cases Option.some.inj he
        simp only [encodeOperation]
        rw [show Words.BinaryNatCode.encode value = payload from
          ((Words.BinaryNatCode.decode?_eq_some_iff payload value).mp hvalue).symm]
        rw [delimit_of_operationPayload hpayload]
      | obtain ⟨payload,hpayload,h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨value,hvalue,he⟩ := Option.bind_eq_some_iff.mp h
        cases Option.some.inj he
        simp only [encodeOperation]
        rw [Algorithms.LabelDictionary.encode_of_decode hvalue,
          delimit_of_operationPayload hpayload]

theorem encodeOperation_injective : Function.Injective encodeOperation := by
  intro operation other he
  have hd := congrArg decodeOperation he
  simpa only [decodeOperation_encodeOperation,Option.some.injEq] using hd

theorem arity_le_two (operation : Operation) : operation.1 ≤ 2 := by
  rcases operation with ⟨n,operation⟩
  cases operation <;> dsimp only <;> omega

@[simp] theorem encode_var (j : ℕ) :
    encode (.var j) = false :: Words.delimit (Words.BinaryNatCode.encode j) := rfl
@[simp] theorem encode_func {n : ℕ} (function : RawSymbol n) (args : Fin n → Raw) :
    encode (.func function args) = true ::
      (Words.delimit (encodeOperation ⟨n, function⟩) ++ (List.ofFn (fun i => encode (args i))).flatten) := rfl

theorem length_encode_pos (term : Raw) : 0 < (encode term).length := by
  cases term <;> simp [encode]

private theorem parseChildren_append {terms : List (Raw)} {fuel : ℕ}
    (hyp : ∀ t ∈ terms, ∀ rest, parse fuel (encode t ++ rest) = some (t, rest))
    (rest : List Bool) :
    parseChildren fuel terms.length ((terms.map (encode)).flatten ++ rest) = some (terms, rest) := by
  induction terms generalizing rest with
  | nil => simp [parseChildren]
  | cons t terms ih =>
    simp only [List.length_cons, List.map_cons, List.flatten_cons, List.append_assoc, parseChildren]
    rw [hyp t (by simp) _]
    change (parseChildren fuel terms.length ((terms.map (encode)).flatten ++ rest)).bind
      (fun p => some (t :: p.1, p.2)) = some (t :: terms, rest)
    rw [ih (fun t ht => hyp t (by simp [ht]))]
    rfl

/-- Prefix decoding preserves every supplied suffix, with fuel bounded by the
original encoded subtree length. -/
theorem parse_encode (term : Raw) (rest : List Bool) (fuel : ℕ)
    (hf : (encode term).length ≤ fuel) :
    parse fuel (encode term ++ rest) = some (term, rest) := by
  induction term generalizing rest fuel with
  | var j =>
    cases fuel with
    | zero => have := length_encode_pos (.var j); omega
    | succ fuel => simp [encode_var, parse]
  | @func n function args ih =>
    cases fuel with
    | zero => have := length_encode_pos (.func function args); omega
    | succ fuel =>
      have hchild : ∀ i, (encode (args i)).length ≤ fuel := by
        intro i
        have hm : encode (args i) ∈ List.ofFn (fun i => encode (args i)) :=
          List.mem_ofFn.mpr ⟨i, rfl⟩
        have hl : (encode (args i)).length ≤ (List.ofFn (fun i => encode (args i))).flatten.length := by
          have hs := List.sublist_flatten_of_mem hm
          exact hs.length_le
        have hhead : (encode (.func function args)).length =
            1 + (Words.delimit (encodeOperation ⟨n, function⟩)).length +
              (List.ofFn (fun i => encode (args i))).flatten.length := by rw [encode.eq_2]; simp only [List.length_cons, List.length_append]; omega
        rw [hhead] at hf
        omega
      have hp := parseChildren_append (terms := List.ofFn args) (fuel := fuel)
        (by intro t ht tail; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht; exact ih i tail fuel (hchild i)) rest
      rw [encode.eq_2]
      simp only [List.cons_append, List.append_assoc, parse]
      rw [Words.unpair?_delimit_append]
      change (decodeOperation (encodeOperation ⟨n, function⟩)).bind
        (fun operation => (parseChildren fuel operation.1
          ((List.ofFn (fun i => encode (args i))).flatten ++ rest)).bind
          (fun p => some (FirstOrder.Language.Term.func (L := Equational.language RawSymbol) operation.2 (fun i => p.1.getD i.val (.var 0)), p.2))) = _
      rw [decodeOperation_encodeOperation]
      change (parseChildren fuel n ((List.ofFn (fun i => encode (args i))).flatten ++ rest)).bind
        (fun p => some (FirstOrder.Language.Term.func (L := Equational.language RawSymbol) function (fun i => p.1.getD i.val (.var 0)), p.2)) = _
      rw [show (List.ofFn (fun i => encode (args i))).flatten =
        ((List.ofFn args).map (encode)).flatten by simp only [List.map_ofFn]; rfl]
      simp only [List.length_ofFn] at hp
      rw [hp]
      change some (FirstOrder.Language.Term.func (L := Equational.language RawSymbol) function
        (fun i => (List.ofFn args).getD i.val (.var 0)), rest) =
        some (FirstOrder.Language.Term.func function args, rest)
      congr 2
      congr 1
      funext i
      simp
private theorem ofFn_getD {n : ℕ} (terms : List (Raw)) (h : terms.length = n) :
    List.ofFn (fun i : Fin n => terms.getD i.val (.var 0)) = terms := by
  apply List.ext_getElem (by simp [h])
  intro i hi hi'
  simp only [List.getElem_ofFn, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi', Option.getD_some]

private theorem children_sound (fuel : ℕ)
    (ih : ∀ {word rest : List Bool} {t : Raw},
      parse fuel word = some (t, rest) → encode t ++ rest = word)
    (count : ℕ) {word rest : List Bool} {terms : List (Raw)}
    (h : parseChildren fuel count word = some (terms, rest)) :
    terms.length = count ∧ (terms.map (encode)).flatten ++ rest = word := by
  induction count generalizing word terms with
  | zero =>
    simp only [parseChildren] at h
    cases Option.some.inj h
    exact ⟨rfl, rfl⟩
  | succ count ihcount =>
    simp only [parseChildren] at h
    obtain ⟨⟨term, tail⟩, ht, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨ts, suffix⟩, hs, he⟩ := Option.bind_eq_some_iff.mp h
    cases Option.some.inj he
    obtain ⟨hlen, hrest⟩ := ihcount hs
    constructor
    · simp [hlen]
    · simp only [List.map_cons, List.flatten_cons, List.append_assoc, hrest, ih ht]

/-- Successful decoding reconstructs the original exact word; malformed input
cannot silently introduce missing children or accept trailing bits. -/
theorem encode_append_of_parse {fuel : ℕ} {word rest : List Bool} {term : Raw}
    (h : parse fuel word = some (term, rest)) : encode term ++ rest = word := by
  induction fuel generalizing word rest term with
  | zero => simp [parse] at h
  | succ fuel ih =>
    cases word with
    | nil => simp [parse] at h
    | cons tag word =>
      cases tag with
      | false =>
        simp only [parse] at h
        obtain ⟨⟨name, tail⟩, hp, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨j, hj, he⟩ := Option.bind_eq_some_iff.mp h
        cases Option.some.inj he
        have hn := (Words.BinaryNatCode.decode?_eq_some_iff name j).mp hj
        simp only [encode_var, List.cons_append, ← hn]
        exact congrArg (List.cons false) (Words.eq_delimit_append_of_unpair?_eq_some hp).symm
      | true =>
        simp only [parse] at h
        obtain ⟨⟨code, body⟩, hp, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨operation, ho, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨⟨children, suffix⟩, hc, he⟩ := Option.bind_eq_some_iff.mp h
        cases Option.some.inj he
        obtain ⟨hlen, hbody⟩ := children_sound fuel (fun h => ih h) operation.1 hc
        rw [encode_func]
        simp only [List.cons_append, List.append_assoc]
        have ht : List.ofFn (fun i : Fin operation.1 =>
          encode (children.getD i.val (.var 0))) = children.map (encode) := by
          change List.ofFn ((encode) ∘ fun i : Fin operation.1 => children.getD i.val (.var 0)) = _
          rw [← List.map_ofFn, ofFn_getD children hlen]
        rw [ht, hbody, encodeOperation_of_decodeOperation ho]
        exact congrArg (List.cons true) (Words.eq_delimit_append_of_unpair?_eq_some hp).symm

@[simp] theorem decode_encode (term : Raw) : decode (encode term) = some term := by
  unfold decode
  have hp := parse_encode term [] (encode term).length le_rfl
  simp only [List.append_nil] at hp
  rw [hp]
  rfl

theorem encode_of_decode {word : List Bool} {term : Raw}
    (h : decode word = some term) : encode term = word := by
  unfold decode at h
  obtain ⟨⟨t, rest⟩, ht, h⟩ := Option.bind_eq_some_iff.mp h
  change (if rest.isEmpty then some t else none) = some term at h
  split at h
  next hr =>
    cases Option.some.inj h
    have hr : rest = [] := List.isEmpty_iff.mp hr
    simpa only [hr, List.append_nil] using encode_append_of_parse ht
  next => cases h

theorem encode_injective : Function.Injective (encode) := by
  intro t u h
  have hd := congrArg (decode) h
  simpa only [decode_encode, Option.some.injEq] using hd

end KFOL.FullTermCode
