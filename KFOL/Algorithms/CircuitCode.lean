module

public import KFOL.Definitions.Circuits
public import KFOL.Algorithms.FiniteTermCode
public import KFOL.Algorithms.GuardRecord
public import Mathlib.Data.List.GetD

/-! Exact flat shared-graph codec. Each gate appears once; references and
variable labels are canonical binary naturals, with no numeric-max padding. -/

@[expose] public section

namespace KFOL.Circuit.Code

open KFOL.Words KFOL.FiniteTermCode

variable (σ : ℕ → Type) [Fintype (Operation σ)]

@[simp] theorem decodeGate_encodeGate (gate : Gate σ ℕ) : decodeGate σ (encodeGate σ gate) = some gate := by
  cases gate with
  | input j => simp [encodeGate, decodeGate]
  | @func n symbol refs =>
    simp [encodeGate, decodeGate]

@[simp] theorem decodeGates_encodeGates (gates : List (Gate σ ℕ)) :
    decodeGates σ (encodeGates σ gates) = some gates := by
  unfold decodeGates encodeGates
  rw [undelimitBlocks_flatten_delimit]
  exact Algorithms.Framing.mapM_decode_encode (encodeGate σ) (decodeGate σ) (decodeGate_encodeGate σ) gates

@[simp] theorem decode_encode (equation : Equation σ ℕ) : decode σ (encode σ equation) = some equation := by
  simp [encode, decode]

theorem encodeGate_of_decodeGate {word : List Bool} {gate : Gate σ ℕ}
    (h : decodeGate σ word = some gate) : encodeGate σ gate = word := by
  cases word with
  | nil => cases h
  | cons bit word =>
    cases bit with
    | false =>
      obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
      exact congrArg (List.cons false) ((BinaryNatCode.decode?_eq_some_iff word j).mp hj).symm
    | true =>
      unfold decodeGate at h
      obtain ⟨⟨opcode, body⟩, hp, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨operation, hop, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨refs, hrefs, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      next hlen =>
        cases Option.some.inj h
        have hr : List.ofFn (fun i : Fin operation.1 => refs.getD i.val 0) = refs := by
          apply List.ext_getElem (by simpa only [List.length_ofFn] using hlen.symm)
          intro i hi hi'
          simp only [List.getElem_ofFn]
          exact List.getD_eq_getElem _ _ hi'
        change true :: pair (encodeOperation σ operation)
          (Algorithms.LabelDictionary.encode (List.ofFn (fun i : Fin operation.1 => refs.getD i.val 0))) = true :: word
        rw [hr, encodeOperation_of_decodeOperation hop, Algorithms.LabelDictionary.encode_of_decode hrefs]
        exact congrArg (List.cons true) (eq_pair_of_unpair?_eq_some hp).symm
      next => cases h

theorem encodeGates_of_decodeGates {word : List Bool} {gates : List (Gate σ ℕ)}
    (h : decodeGates σ word = some gates) : encodeGates σ gates = word := by
  unfold decodeGates at h
  obtain ⟨blocks, hb, hg⟩ := Option.bind_eq_some_iff.mp h
  have he := Algorithms.Framing.map_eq_of_mapM_decode (encodeGate σ) (decodeGate σ)
    (fun _ _ => encodeGate_of_decodeGate σ) blocks gates hg
  rw [encodeGates, he]
  exact Algorithms.Framing.undelimitBlocks_sound hb

theorem encode_of_decode {word : List Bool} {equation : Equation σ ℕ}
    (h : decode σ word = some equation) : encode σ equation = word := by
  unfold decode at h
  obtain ⟨⟨stream, outputs⟩, hp, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨gates, hg, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨leftCode, rightCode⟩, hout, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨left, hl, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨right, hr, he⟩ := Option.bind_eq_some_iff.mp h
  cases Option.some.inj he
  unfold encode
  rw [encodeGates_of_decodeGates σ hg,
    ← (BinaryNatCode.decode?_eq_some_iff leftCode left).mp hl,
    ← (BinaryNatCode.decode?_eq_some_iff rightCode right).mp hr,
    ← eq_pair_of_unpair?_eq_some hout]
  exact (eq_pair_of_unpair?_eq_some hp).symm

theorem decode_eq_some_iff (word : List Bool) (equation : Equation σ ℕ) :
    decode σ word = some equation ↔ word = encode σ equation :=
  ⟨fun h => (encode_of_decode σ h).symm, fun he => he ▸ decode_encode σ equation⟩

noncomputable def encoding : Equation σ ℕ ↪ List Bool :=
  ⟨encode σ, fun _ _ h => Option.some.inj (by simpa only [decode_encode] using congrArg (decode σ) h)⟩


/- The complete original shared-graph word language. It excludes both
malformed codes and well-typed graphs with invalid references/outputs. -/
theorem mem_language_iff_decode {M : Type*} [(Equational.language σ).Structure M] (word : List Bool) :
    word ∈ Language σ M ↔ ∃ equation : Equation σ ℕ,
      decode σ word = some equation ∧ equation.Holds M := by
  constructor
  · rintro ⟨equation, rfl, hh⟩
    exact ⟨equation, decode_encode σ equation, hh⟩
  · rintro ⟨equation, hd, hh⟩
    exact ⟨equation, encode_of_decode σ hd, hh⟩

end KFOL.Circuit.Code

namespace KFOL.Circuit.Code

open KFOL.Words KFOL.FiniteTermCode
variable (σ : ℕ → Type) [Fintype (Operation σ)]

/-- Every original node occupies a physical frame in the shared stream;
sparse numeric labels cannot affect the number of certificate positions. -/
theorem gates_length_le_encode (equation : Equation σ ℕ) : equation.gates.length ≤ (encode σ equation).length := by
  have h (gates : List (Gate σ ℕ)) : gates.length ≤ (encodeGates σ gates).length := by
    induction gates with
    | nil => rfl
    | cons gate gates ih =>
      change gates.length + 1 ≤ (delimit (encodeGate σ gate) ++ encodeGates σ gates).length
      rw [List.length_append, delimit_length]
      omega
  have hn := h equation.gates
  simp only [encode, pair_length]
  omega

end KFOL.Circuit.Code
