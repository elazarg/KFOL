module
public import KFOL.Complexity.OptionTraversal
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
public import Mathlib.Data.Fintype.EquivFin
/-! Shared finite-algebra value codes and padded countervaluation witnesses. -/
@[expose] public section
namespace KFOL.Complexity.FiniteAlgebraVerifier
open Turing.MultiTapeTM ComputableInPolyTime
variable {Value : Type} [Fintype Value] [Nonempty Value]
noncomputable def numbering : Value ≃ Fin (Fintype.card Value) := Fintype.equivFin Value

noncomputable def index (value : Value) : ℕ := (numbering value).val

noncomputable def valueEncoding : Value ↪ List Bool :=
  ⟨fun value => encUnary (index value), fun _a _b he =>
    numbering.injective (Fin.ext (encUnary.injective he))⟩

noncomputable def values : List Value := (List.finRange (Fintype.card Value)).map numbering.symm

noncomputable def fallback : Value := Classical.choice inferInstance

omit [Nonempty Value] in
private theorem index_lt (value : Value) : index value < Fintype.card Value := (numbering value).isLt

omit [Nonempty Value] in
private theorem index_injective : Function.Injective (index (Value := Value)) := by
  intro a b he
  exact numbering.injective (Fin.ext he)

omit [Nonempty Value] in
private theorem mem_values (value : Value) : value ∈ values := by
  exact List.mem_map.mpr ⟨numbering value, by simp, (numbering.symm_apply_apply value)⟩

/-- A finite-value block is decoded by its first indicated value. Every bit
word supplies a genuine algebra value, including malformed/short blocks. -/
noncomputable def decodeValue (word : List Bool) : Value :=
  (values.find? (fun value => word.getD (index value) false)).getD fallback

theorem decodeValue_polyTime : ComputableInPolyTime (decodeValue (Value := Value)) encBits valueEncoding := by
  classical
  have hi : ComputableInPolyTime (index (Value := Value)) valueEncoding encUnary := .of_finite _
  have hread := bitsGetDWithInput (fst encBits valueEncoding) (hi.comp (snd encBits valueEncoding)) false
  have hfind := findWithInput (test := fun (word : List Bool) value => word.getD (index value) false)
    (const values) hread
  exact hfind.optionGetDWithInput (const fallback)

abbrev Context := List ℕ × List Bool
abbrev contextEncoding := encPair (encList encNat) encBits

/-- Lookup uses the first occurrence position, scaled by a fixed finite-value
block width. The numeric variable name is compared as binary input data. -/
noncomputable def lookup (context : Context) (j : ℕ) : Value :=
  decodeValue (context.2.drop (Fintype.card Value * context.1.idxOf j))

theorem lookup_polyTime : ComputableInPolyTime
    (fun p : Context × ℕ => (lookup p.1 p.2 : Value)) (encPair contextEncoding encNat) valueEncoding := by
  have hlabels : ComputableInPolyTime (fun p : Context × ℕ => p.1.1)
      (encPair contextEncoding encNat) (encList encNat) := by fun_prop
  have hword : ComputableInPolyTime (fun p : Context × ℕ => p.1.2)
      (encPair contextEncoding encNat) encBits := by fun_prop
  have hj := snd contextEncoding encNat
  have hindex := idxOfWithInput hlabels hj
  have hoffset := unary_mul' (const (Fintype.card Value)) hindex
  exact decodeValue_polyTime.comp (bitsDropWithInput hword hoffset)

/-- A fixed-width one-hot block for every listed occurrence. This is only a
mathematical existence witness; the verifier decodes arbitrary supplied bits. -/
noncomputable def witness (labels : List ℕ) (valuation : ℕ → Value) : List Bool :=
  List.ofFn (fun i : Fin (Fintype.card Value * labels.length) =>
    decide (index (valuation (labels.getD (i.val / Fintype.card Value) 0)) = i.val % Fintype.card Value))

omit [Nonempty Value] in
@[simp] theorem length_witness (labels : List ℕ) (valuation : ℕ → Value) :
    (witness labels valuation).length = Fintype.card Value * labels.length := by simp [witness]

private theorem getD_witness (labels : List ℕ) (valuation : ℕ → Value) (j : ℕ) (hj : j ∈ labels)
    (padding : List Bool) (r : Fin (Fintype.card Value)) :
    (witness labels valuation ++ padding).getD (Fintype.card Value * labels.idxOf j + r.val) false =
      decide (index (valuation j) = r.val) := by
  have hm : 0 < Fintype.card Value := Fintype.card_pos
  have hi := List.idxOf_lt_length_iff.mpr hj
  have hlt : Fintype.card Value * labels.idxOf j + r.val < (witness labels valuation).length := by
    rw [length_witness]
    nlinarith [r.isLt]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, List.getElem?_eq_getElem hlt]
  simp only [witness, List.getElem_ofFn]
  have hd : (Fintype.card Value * labels.idxOf j + r.val) / Fintype.card Value = labels.idxOf j := by
    rw [Nat.mul_add_div hm, Nat.div_eq_of_lt r.isLt, Nat.add_zero]
  have hr : (Fintype.card Value * labels.idxOf j + r.val) % Fintype.card Value = r.val := by
    rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt r.isLt]
  rw [hd, hr, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getElem_idxOf hi]
  rfl

private theorem find_unique {A : Type} (list : List A) (predicate : A → Bool) (value : A)
    (hv : value ∈ list) (hp : predicate value = true)
    (hunique : ∀ other ∈ list, predicate other = true → other = value) :
    list.find? predicate = some value := by
  cases hfind : list.find? predicate with
  | none =>
    have hnone := List.find?_eq_none.mp hfind
    exact False.elim (hnone value hv hp)
  | some other =>
    have he := hunique other (List.mem_of_find?_eq_some hfind) (List.find?_some hfind)
    rw [he]

/-- All supplied padding is ignored at the positions needed by the instance. -/
theorem lookup_witness (labels : List ℕ) (valuation : ℕ → Value) (j : ℕ) (hj : j ∈ labels)
    (padding : List Bool) : lookup (labels, witness labels valuation ++ padding) j = valuation j := by
  classical
  unfold lookup decodeValue
  have hread (value : Value) :
      ((witness labels valuation ++ padding).drop (Fintype.card Value * labels.idxOf j)).getD (index value) false =
        decide (valuation j = value) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_drop]
    have h := getD_witness labels valuation j hj padding (numbering value)
    simp only [List.getD_eq_getElem?_getD] at h
    change (witness labels valuation ++ padding)[Fintype.card Value * labels.idxOf j + index value]?.getD false =
      decide (index (valuation j) = index value) at h
    rw [h]
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using index_injective.eq_iff
  have hfind :
      values.find? (fun value =>
        ((witness labels valuation ++ padding).drop (Fintype.card Value * labels.idxOf j)).getD (index value) false) =
        some (valuation j) := by
    apply find_unique _ _ _ (mem_values _) (by rw [hread]; simp)
    intro other _ ho
    rw [hread, decide_eq_true_eq] at ho
    exact ho.symm
  rw [hfind]
  rfl


omit [Nonempty Value] in
theorem value_length_le (value : Value) :
    (valueEncoding value).length ≤ Fintype.card Value := by
  change (encUnary (index value)).length ≤ Fintype.card Value
  simpa using (index_lt value).le


end KFOL.Complexity.FiniteAlgebraVerifier
