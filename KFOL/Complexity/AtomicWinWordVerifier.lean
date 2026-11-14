module

public import KFOL.Complexity.AtomicWinVerifier
public import KFOL.Complexity.FullTermDecoding
public import KFOL.Complexity.CoreExtractionValidation

/-! # NP membership of the complete original atomic possible-win word language

The independently specified language contains exactly encodings of original
terms having an atomic winning valuation. Decoding and role-array validation
reject every malformed word before its certificate is evaluated.
-/

@[expose] public section

namespace KFOL.Complexity.AtomicWinVerifier

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FullTermCode

section Positive

variable {K : ℕ} [Nonempty (Fin K)]

noncomputable def rawContext (K : ℕ) [Nonempty (Fin K)]
    (input : Raw × List Bool) : FullSparseEvaluation.Context :=
  (FullTermSize.labels input.1, pairValues K (FullTermSize.labels input.1, input.2))

noncomputable def rawVerifier (winner : Fin K) (input : Raw × List Bool) : Bool :=
  (FullSparseEvaluation.evaluate (rawContext K input) input.1).any
    (fun role => decide (role = winner.val))

theorem rawVerifier_polyTime (winner : Fin K) : ComputableInPolyTime (rawVerifier winner)
    (encPair FullTermMachines.termEncoding encBits) encBool := by
  let input := encPair FullTermMachines.termEncoding encBits
  have hn := FullTermSize.labels_polyTime.comp (fst FullTermMachines.termEncoding encBits)
  have hc := hn.prod ((pairValues_polyTime (K := K)).comp
    (hn.prod (snd FullTermMachines.termEncoding encBits)))
  have he := FullSparseEvaluation.evaluate_polyTime.comp
    (hc.prod (fst FullTermMachines.termEncoding encBits))
  exact anyWithInput (test := fun (_ : Raw × List Bool) role => decide (role = winner.val))
    he (decide_eq' (snd input encNat) (const winner.val))

noncomputable def wordVerifier (winner : Fin K) (input : List Bool × List Bool) : Bool :=
  (decode input.1).elim false
    (fun raw => valid K raw && rawVerifier winner (raw, input.2))

theorem wordVerifier_polyTime (winner : Fin K) : ComputableInPolyTime (wordVerifier winner)
    (encPair encBits encBits) encBool := by
  let input := encPair encBits encBits
  let callback := encPair input FullTermMachines.termEncoding
  have hd := FullTermMachines.decode_polyTime.comp (fst encBits encBits)
  have hr := snd input FullTermMachines.termEncoding
  have hw : ComputableInPolyTime (fun p : (List Bool × List Bool) × Raw => p.1.2)
      callback encBits := by fun_prop
  have hv := CoreExtraction.valid_polyTime.comp ((const K).prod hr)
  have he := (rawVerifier_polyTime winner).comp (hr.prod hw)
  exact hd.optionElimWithInput
    (body := fun (p : List Bool × List Bool) raw => valid K raw && rawVerifier winner (raw, p.2))
    (const false) (bool_and' hv he)

def wordLanguage (winner : Fin K) : Set (List Bool) :=
  {word | ∃ term : Tree K, termEncoding K term = word ∧ term.AtomicPossibleWin winner}

theorem wordVerifier_encode (winner : Fin K) (term : Tree K) (certificate : List Bool) :
    wordVerifier winner (termEncoding K term, certificate) = verifier winner (term, certificate) := by
  change (decode (encode (view term))).elim false
    (fun raw => valid K raw && rawVerifier winner (raw, certificate)) = _
  rw [decode_encode]
  simp only [Option.elim_some, valid_view, Bool.true_and]
  rfl

theorem wordVerifier_sound (winner : Fin K) (word certificate : List Bool)
    (accepted : wordVerifier winner (word, certificate) = true) : word ∈ wordLanguage winner := by
  cases decoded : decode word with
  | none => simp [wordVerifier, decoded] at accepted
  | some raw =>
    have facts : valid K raw = true ∧ rawVerifier winner (raw, certificate) = true := by
      simpa only [wordVerifier, decoded, Option.elim_some, Bool.and_eq_true] using accepted
    obtain ⟨term, original⟩ := exists_original_of_valid facts.1
    have code : termEncoding K term = word := by
      change encode (view term) = word
      rw [original]
      exact encode_of_decode decoded
    refine ⟨term, code, verifier_sound winner term certificate ?_⟩
    change rawVerifier winner (view term, certificate) = true
    rw [original]
    exact facts.2

theorem wordLanguage_mem_NP_of_nonempty (winner : Fin K) :
    wordLanguage winner ∈ Cslib.Complexity.NP encBits := by
  classical
  refine ⟨Polynomial.C K * Polynomial.X, wordVerifier winner, wordVerifier_polyTime winner, ?_⟩
  apply Cslib.Complexity.IsVerifier.of_padding
  · intro word certificate _ accepted
    exact wordVerifier_sound winner word certificate accepted
  · intro word member
    obtain ⟨term, code, valuation, wins⟩ := member
    refine ⟨FiniteAlgebraVerifier.witness (labels term) valuation, ?_, ?_⟩
    · simp only [FiniteAlgebraVerifier.length_witness, Fintype.card_fin,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, encBits_apply]
      rw [← code]
      exact Nat.mul_le_mul_left K (FullTermSize.length_labels_le_encode (view term))
    · intro padding
      rw [← code, wordVerifier_encode]
      exact verifier_complete winner term valuation wins _

end Positive

theorem wordLanguage_mem_NP {K : ℕ} (winner : Fin K) :
    wordLanguage winner ∈ Cslib.Complexity.NP encBits := by
  let _ : Nonempty (Fin K) := ⟨winner⟩
  exact wordLanguage_mem_NP_of_nonempty winner

end KFOL.Complexity.AtomicWinVerifier
