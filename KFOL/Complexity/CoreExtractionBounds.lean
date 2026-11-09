module

public import KFOL.Complexity.FullTermSize
public import KFOL.Complexity.CoreExtractionArrays
public import KFOL.Algorithms.FullTermCode.Core

/-! # Explicit cubic storage bounds for uniform original-input extraction -/

@[expose] public section

namespace KFOL.Complexity.CoreExtraction

open Turing.MultiTapeTM
open KFOL.FullTermCode FullTermSize

/-- Byte bounds charge binary labels themselves, including labels too large
to be safely expanded into unary counters. -/
def ByteBound (N : ℕ) (values : List ℕ) : Prop :=
  ∀ value ∈ values, (encNat value).length ≤ N

theorem byteBound_of_weight (values : List ℕ) {N : ℕ} (h : weight values ≤ N) : ByteBound N values := by
  intro value hv
  exact (SizedListEncoding.length_elem_le (encA := encNat) (encL := arrayEncoding) values value hv).trans h

theorem byteBound_getD {N : ℕ} {values : List ℕ} (h : ByteBound N values) (index : ℕ) :
    (encNat (values.getD index 0)).length ≤ N := by
  by_cases hi : index < values.length
  · simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
    exact h _ (List.getElem_mem hi)
  · have he : values[index]? = none := List.getElem?_eq_none (Nat.le_of_not_lt hi)
    simp [List.getD_eq_getElem?_getD,he,encNat_apply]

theorem weight_of_byteBound {N : ℕ} {values : List ℕ} (h : ByteBound N values) :
    weight values ≤ values.length*(2*N+1) := by
  induction values with
  | nil => simp
  | cons value values ih =>
    have hv := h value (by simp)
    have hs := ih (fun v hv => h v (by simp [hv]))
    simp only [weight_cons,List.length_cons,encNat_apply] at hv ⊢
    nlinarith

theorem dictionary_length_le_two_weight (values : List ℕ) :
    (Algorithms.LabelDictionary.encode values).length ≤ 2*weight values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    simp only [Algorithms.LabelDictionary.encode,List.map_cons,List.flatten_cons,List.length_append,
      Words.delimit_length,Words.BinaryNatCode.encode,weight_cons] at ih ⊢
    omega

theorem encode_rawWinner_length (role : ℕ) :
    (encode (rawWinner role)).length = 4*role.bits.length+11 := by
  simp only [rawWinner,encode_func,encodeOperation,List.ofFn_zero,List.flatten_nil,List.append_nil,
    List.length_cons,Words.delimit_length,Words.BinaryNatCode.encode]
  omega

theorem encode_rawChoice_length (owner : ℕ) (left right : Raw) :
    (encode (rawChoice owner left right)).length =
      4*owner.bits.length+11+(encode left).length+(encode right).length := by
  simp [rawChoice,encode_func,encodeOperation,List.ofFn_succ,Words.delimit_length,Words.BinaryNatCode.encode]
  omega

theorem encode_rawRename_length (forward : List ℕ) (raw : Raw) :
    (encode (rawRename forward raw)).length =
      4*(Algorithms.LabelDictionary.encode forward).length+11+(encode raw).length := by
  simp [rawRename,encode_func,encodeOperation,List.ofFn_succ,Words.delimit_length]
  omega

/-- Original bytes are bounded by literal constructor count plus the complete
source pool, retaining every explicit array entry and every repeated label. -/
theorem encode_le_nodes_weight (raw : Raw) :
    (encode raw).length ≤ 11*(nodes raw+weight (labels raw)) := by
  induction raw with
  | var name =>
    simp only [encode_var,List.length_cons,Words.delimit_length,Words.BinaryNatCode.encode,nodes,
      labels,weight_cons,weight_nil]
    omega
  | @func n operation children ih =>
    cases operation with
    | winner role =>
      change (encode (rawWinner role)).length ≤ 11*(1+weight [role])
      rw [encode_rawWinner_length,weight_cons,weight_nil]
      omega
    | choice owner =>
      have hl := ih 0
      have hr := ih 1
      change (encode (rawChoice owner (children 0) (children 1))).length ≤ _
      rw [encode_rawChoice_length]
      simp only [nodes,labels,weight_cons,weight_append]
      omega
    | rename forward =>
      have hc := ih 0
      have hd := dictionary_length_le_two_weight forward
      change (encode (rawRename forward (children 0))).length ≤ _
      rw [encode_rawRename_length]
      simp only [nodes,labels,weight_append]
      omega

/-- Transport preserves actual node count, even for malformed raw trees. -/
theorem nodes_mapRoles (forward : List ℕ) (raw : Raw) : nodes (mapRoles forward raw) = nodes raw := by
  induction raw with
  | var => rfl
  | @func n operation children ih =>
    cases operation <;> simp [mapRoles,nodes,rawWinner,rawChoice,rawRename,ih]

/-- Array transport introduces only a bounded number of bounded binary labels. -/
theorem weight_mapRoles (forward : List ℕ) (raw : Raw) :
    weight (labels (mapRoles forward raw)) ≤
      weight (labels raw)+nodes raw*(2*weight forward+1) := by
  have hlookup (index : ℕ) : (encNat (forward.getD index 0)).length ≤ weight forward :=
    byteBound_getD (byteBound_of_weight forward le_rfl) index
  induction raw with
  | var name => simp [mapRoles,labels,nodes]
  | @func n operation children ih =>
    cases operation with
    | winner role =>
      have hl := hlookup role
      simp only [mapRoles,rawWinner,labels,weight_cons,weight_nil,nodes,encNat_apply] at hl ⊢
      omega
    | choice owner =>
      have hl := ih 0
      have hr := ih 1
      have ho := hlookup owner
      simp only [mapRoles,rawChoice,labels,weight_cons,weight_append,nodes,encNat_apply] at ho ⊢
      change _ + (weight (labels (mapRoles forward (children 0))) +
        weight (labels (mapRoles forward (children 1)))) ≤ _
      nlinarith
    | rename original =>
      have hc := ih 0
      simp only [mapRoles,rawRename,labels,weight_append,nodes]
      nlinarith

/-- The nested label-map traversal has a concrete quadratic byte bound. -/
theorem encode_mapRoles_bound (forward : List ℕ) (raw : Raw) :
    (encode (mapRoles forward raw)).length ≤
      100*(weight forward+(encode raw).length+1)^2 := by
  have hcode := encode_le_nodes_weight (mapRoles forward raw)
  rw [nodes_mapRoles] at hcode
  have hw := weight_mapRoles forward raw
  have hn := nodes_le_encode raw
  have hp := labels_weight_le_encode raw
  have hm := Nat.mul_le_mul_right (2*weight forward+1) hn
  nlinarith [hcode,hw,hm]

end KFOL.Complexity.CoreExtraction
