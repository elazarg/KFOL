module
public import KFOL.Definitions.Encoding
public import KFOL.Algorithms.Words
/-! # Exact finite-signature tree-code roundtrips and malformed-word semantics -/

@[expose] public section
namespace KFOL.FiniteTermCode
variable {σ : ℕ → Type} [Fintype (Operation σ)]
@[simp] theorem decodeOperation_encodeOperation (operation : Operation σ) :
    decodeOperation σ (encodeOperation σ operation) = some operation := by
  simp [decodeOperation, encodeOperation, (operationNumbering σ operation).isLt]
theorem encodeOperation_of_decodeOperation {word : List Bool} {operation : Operation σ}
    (h : decodeOperation σ word = some operation) : encodeOperation σ operation = word := by
  unfold decodeOperation at h
  obtain ⟨index, hi, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  next hb =>
    cases Option.some.inj h
    simpa only [encodeOperation, Equiv.apply_symm_apply] using
      ((Words.BinaryNatCode.decode?_eq_some_iff word index).mp hi).symm
  next => cases h

theorem arity_le_maxArity (operation : Operation σ) : operation.1 ≤ maxArity σ :=
  Finset.le_sup (f := fun operation : Operation σ => operation.1) (Finset.mem_univ operation)

@[simp] theorem encode_var (j : ℕ) :
    encode σ (.var j) = false :: Words.delimit (Words.BinaryNatCode.encode j) := rfl
@[simp] theorem encode_func {n : ℕ} (function : σ n) (args : Fin n → Equational.Term σ ℕ) :
    encode σ (.func function args) = true ::
      (Words.delimit (encodeOperation σ ⟨n, function⟩) ++ (List.ofFn (fun i => encode σ (args i))).flatten) := rfl

theorem length_encode_pos (term : Equational.Term σ ℕ) : 0 < (encode σ term).length := by
  cases term <;> simp [encode]

private theorem parseChildren_append {terms : List (Equational.Term σ ℕ)} {fuel : ℕ}
    (hyp : ∀ t ∈ terms, ∀ rest, parse σ fuel (encode σ t ++ rest) = some (t, rest))
    (rest : List Bool) :
    parseChildren σ fuel terms.length ((terms.map (encode σ)).flatten ++ rest) = some (terms, rest) := by
  induction terms generalizing rest with
  | nil => simp [parseChildren]
  | cons t terms ih =>
    simp only [List.length_cons, List.map_cons, List.flatten_cons, List.append_assoc, parseChildren]
    rw [hyp t (by simp) _]
    change (parseChildren σ fuel terms.length ((terms.map (encode σ)).flatten ++ rest)).bind
      (fun p => some (t :: p.1, p.2)) = some (t :: terms, rest)
    rw [ih (fun t ht => hyp t (by simp [ht]))]
    rfl

/-- Prefix decoding preserves every supplied suffix, with fuel bounded by the
original encoded subtree length. -/
theorem parse_encode (term : Equational.Term σ ℕ) (rest : List Bool) (fuel : ℕ)
    (hf : (encode σ term).length ≤ fuel) :
    parse σ fuel (encode σ term ++ rest) = some (term, rest) := by
  induction term generalizing rest fuel with
  | var j =>
    cases fuel with
    | zero => have := length_encode_pos (σ := σ) (.var j); omega
    | succ fuel => simp [encode_var, parse]
  | @func n function args ih =>
    cases fuel with
    | zero => have := length_encode_pos (σ := σ) (.func function args); omega
    | succ fuel =>
      have hchild : ∀ i, (encode σ (args i)).length ≤ fuel := by
        intro i
        have hm : encode σ (args i) ∈ List.ofFn (fun i => encode σ (args i)) :=
          List.mem_ofFn.mpr ⟨i, rfl⟩
        have hl : (encode σ (args i)).length ≤ (List.ofFn (fun i => encode σ (args i))).flatten.length := by
          have hs := List.sublist_flatten_of_mem hm
          exact hs.length_le
        have hhead : (encode σ (.func function args)).length =
            1 + (Words.delimit (encodeOperation σ ⟨n, function⟩)).length +
              (List.ofFn (fun i => encode σ (args i))).flatten.length := by rw [encode.eq_2]; simp only [List.length_cons, List.length_append]; omega
        rw [hhead] at hf
        omega
      have hp := parseChildren_append (terms := List.ofFn args) (fuel := fuel)
        (by intro t ht tail; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht; exact ih i tail fuel (hchild i)) rest
      rw [encode.eq_2]
      simp only [List.cons_append, List.append_assoc, parse]
      rw [Words.unpair?_delimit_append]
      change (decodeOperation σ (encodeOperation σ ⟨n, function⟩)).bind
        (fun operation => (parseChildren σ fuel operation.1
          ((List.ofFn (fun i => encode σ (args i))).flatten ++ rest)).bind
          (fun p => some (FirstOrder.Language.Term.func (L := Equational.language σ) operation.2 (fun i => p.1.getD i.val (.var 0)), p.2))) = _
      rw [decodeOperation_encodeOperation]
      change (parseChildren σ fuel n ((List.ofFn (fun i => encode σ (args i))).flatten ++ rest)).bind
        (fun p => some (FirstOrder.Language.Term.func (L := Equational.language σ) function (fun i => p.1.getD i.val (.var 0)), p.2)) = _
      rw [show (List.ofFn (fun i => encode σ (args i))).flatten =
        ((List.ofFn args).map (encode σ)).flatten by simp only [List.map_ofFn]; rfl]
      simp only [List.length_ofFn] at hp
      rw [hp]
      change some (FirstOrder.Language.Term.func (L := Equational.language σ) function
        (fun i => (List.ofFn args).getD i.val (.var 0)), rest) =
        some (FirstOrder.Language.Term.func function args, rest)
      congr 2
      congr 1
      funext i
      simp
omit [Fintype (Operation σ)] in
private theorem ofFn_getD {n : ℕ} (terms : List (Equational.Term σ ℕ)) (h : terms.length = n) :
    List.ofFn (fun i : Fin n => terms.getD i.val (.var 0)) = terms := by
  apply List.ext_getElem (by simp [h])
  intro i hi hi'
  simp only [List.getElem_ofFn, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi', Option.getD_some]

private theorem children_sound (fuel : ℕ)
    (ih : ∀ {word rest : List Bool} {t : Equational.Term σ ℕ},
      parse σ fuel word = some (t, rest) → encode σ t ++ rest = word)
    (count : ℕ) {word rest : List Bool} {terms : List (Equational.Term σ ℕ)}
    (h : parseChildren σ fuel count word = some (terms, rest)) :
    terms.length = count ∧ (terms.map (encode σ)).flatten ++ rest = word := by
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
theorem encode_append_of_parse {fuel : ℕ} {word rest : List Bool} {term : Equational.Term σ ℕ}
    (h : parse σ fuel word = some (term, rest)) : encode σ term ++ rest = word := by
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
          encode σ (children.getD i.val (.var 0))) = children.map (encode σ) := by
          change List.ofFn ((encode σ) ∘ fun i : Fin operation.1 => children.getD i.val (.var 0)) = _
          rw [← List.map_ofFn, ofFn_getD children hlen]
        rw [ht, hbody, encodeOperation_of_decodeOperation ho]
        exact congrArg (List.cons true) (Words.eq_delimit_append_of_unpair?_eq_some hp).symm

@[simp] theorem decode_encode (term : Equational.Term σ ℕ) : decode σ (encode σ term) = some term := by
  unfold decode
  have hp := parse_encode term [] (encode σ term).length le_rfl
  simp only [List.append_nil] at hp
  rw [hp]
  rfl

theorem encode_of_decode {word : List Bool} {term : Equational.Term σ ℕ}
    (h : decode σ word = some term) : encode σ term = word := by
  unfold decode at h
  obtain ⟨⟨t, rest⟩, ht, h⟩ := Option.bind_eq_some_iff.mp h
  change (if rest.isEmpty then some t else none) = some term at h
  split at h
  next hr =>
    cases Option.some.inj h
    have hr : rest = [] := List.isEmpty_iff.mp hr
    simpa only [hr, List.append_nil] using encode_append_of_parse ht
  next => cases h

theorem encode_injective : Function.Injective (encode σ) := by
  intro t u h
  have hd := congrArg (decode σ) h
  simpa only [decode_encode, Option.some.injEq] using hd

end KFOL.FiniteTermCode
