module
public import KFOL.Complexity.FullSparseSemantics
/-! The actual binary two-winner certificate has quadratic length in the
original input, uniformly in the binary role count. -/
@[expose] public section
namespace KFOL.Complexity.FullCertificateSize
open KFOL.FullTermCode
open KFOL.Complexity.FullSparseEvaluation

@[simp] theorem length_pairValues {K : ℕ} (names : List ℕ) (pairs : ℕ → Fin K × Fin K) :
    (pairValues names pairs).length = 2 * names.length := by
  induction names with
  | nil => rfl
  | cons name names ih =>
    change (pairValues names pairs).length + 1 + 1 = 2 * (names.length + 1)
    rw [ih]
    omega

/-- Every guessed winner is encoded by its actual bounded binary role label. -/
theorem dictionary_pairValues_length_le {K : ℕ} (names : List ℕ) (pairs : ℕ → Fin K × Fin K) :
    (Algorithms.LabelDictionary.encode (pairValues names pairs)).length ≤
      4 * names.length * (K.size + 1) := by
  have hs : ∀ role ∈ pairValues names pairs, role.size ≤ K.size :=
    fun role hr => Nat.size_le_size (pairValues_bounded names pairs role hr).le
  have hsum := List.sum_le_sum (l := pairValues names pairs)
    (f := Nat.size) (g := fun _ => K.size) hs
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, length_pairValues] at hsum
  rw [Algorithms.LabelDictionary.length_encode, length_pairValues]
  nlinarith

/-- The framed certificate is physically bounded by the original source
header and tree payloads, with no uncharged enumeration of the role set. -/
theorem framed_pairValues_length_le (input : EquationInput)
    (pairs : ℕ → Fin input.1 × Fin input.1) :
    (Words.delimit (Algorithms.LabelDictionary.encode
      (pairValues (FullTermSize.labels (view input.2.1) ++ FullTermSize.labels (view input.2.2)) pairs))).length ≤
      16 * ((encodeEquationInput input).length + 1)^2 := by
  have hl := FullTermSize.length_labels_le_encode (view input.2.1)
  have hr := FullTermSize.length_labels_le_encode (view input.2.2)
  have hd := dictionary_pairValues_length_le
    (FullTermSize.labels (view input.2.1) ++ FullTermSize.labels (view input.2.2)) pairs
  simp only [List.length_append] at hd
  rw [Words.delimit_length]
  have hin : (encodeEquationInput input).length = 2 * input.1.size + 2 +
      (2 * (encode (view input.2.1)).length + 2 + (encode (view input.2.2)).length) := by
    simp only [encodeEquationInput,Words.pair_length,Words.BinaryNatCode.length_encode]
  have hnames : (FullTermSize.labels (view input.2.1)).length +
      (FullTermSize.labels (view input.2.2)).length ≤ (encodeEquationInput input).length := by omega
  have hK : input.1.size + 1 ≤ (encodeEquationInput input).length + 1 := by omega
  have hm := Nat.mul_le_mul hnames hK
  nlinarith
end KFOL.Complexity.FullCertificateSize
