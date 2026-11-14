module

public import KFOL.Algebra.AtomicDecision
public import KFOL.Complexity.AtomicWinWordVerifier
public import KFOL.Complexity.FullPublicReduction
public import Complexity.Computability.Complexity.Classes.P

/-! # Deterministic atomic possible-win checking without role switches -/

@[expose] public section

namespace KFOL.Complexity.AtomicWinPublic

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FullTermCode
open AtomicWinVerifier

variable {K : ℕ}

def values (winner : Fin K) (names : List ℕ) : List ℕ :=
  names.flatMap (fun _ => [winner.val, winner.val])

theorem values_polyTime (winner : Fin K) : ComputableInPolyTime (values winner)
    (encList encNat) (encList encNat) :=
  flatMapWithInput (f := fun (_ : List ℕ) (_ : ℕ) => [winner.val, winner.val])
    id' (const [winner.val, winner.val])

noncomputable def rawCheck (winner : Fin K) (term : Raw) : Bool :=
  let names := FullTermSize.labels term
  (FullSparseEvaluation.evaluate (names, values winner names) term).any
    (fun role => decide (role = winner.val))

theorem rawCheck_polyTime (winner : Fin K) : ComputableInPolyTime (rawCheck winner)
    FullTermMachines.termEncoding encBool := by
  have hn := FullTermSize.labels_polyTime
  have hc := hn.prod ((values_polyTime winner).comp hn)
  have he := FullSparseEvaluation.evaluate_polyTime.comp
    (hc.prod (id' (encIn := FullTermMachines.termEncoding)))
  exact anyWithInput (test := fun (_ : Raw) role => decide (role = winner.val))
    he (decide_eq' (snd FullTermMachines.termEncoding encNat) (const winner.val))

theorem rawCheck_view_iff (winner : Fin K) (term : Tree K) :
    rawCheck winner (view term) = true ↔
      winner ∈ (term.eval (fun _ => WinnerSet.singleton winner)).val := by
  let names := FullTermSize.labels (view term)
  have hr : FullSparseEvaluation.Represents
      (FullSparseEvaluation.evaluate (names, values winner names) (view term))
      (term.eval (fun _ => WinnerSet.singleton winner)) := by
    apply FullSparseEvaluation.evaluate_view_represents
    intro name member
    have hl := FullSparseEvaluation.leaf_pairValues names
      (fun _ => (winner, winner)) name member
    rw [show values winner names = FullSparseEvaluation.pairValues names
      (fun _ => (winner, winner)) from rfl, hl]
    simp only [FullSparseEvaluation.Represents, FullSparseEvaluation.asSet,
      WinnerSet.singleton, Set.image_singleton]
    ext role
    simp
  simp only [rawCheck, List.any_eq_true, decide_eq_true_eq]
  change (∃ role ∈ FullSparseEvaluation.evaluate (names, values winner names) (view term),
    role = winner.val) ↔ _
  rw [show (∃ role ∈ FullSparseEvaluation.evaluate (names, values winner names) (view term),
      role = winner.val) ↔ winner.val ∈
      FullSparseEvaluation.evaluate (names, values winner names) (view term) from by simp]
  change winner.val ∈ FullSparseEvaluation.asSet _ ↔ _
  rw [hr]
  constructor
  · rintro ⟨other, wins, equal⟩
    exact (Fin.val_injective equal) ▸ wins
  · intro wins
    exact ⟨winner, wins, rfl⟩

noncomputable def check (winner : Fin K) (term : Tree K) : Bool :=
  FullPublicReduction.check (view term) && rawCheck winner (view term)

theorem check_polyTime (winner : Fin K) : ComputableInPolyTime (check winner)
    (termEncoding K) encBool :=
  bool_and' (FullPublicReduction.check_polyTime.comp (view_polyTime K))
    ((rawCheck_polyTime winner).comp (view_polyTime K))

theorem check_iff (winner : Fin K) (term : Tree K) : check winner term = true ↔
    term.IsPublic ∧ term.AtomicPossibleWin winner := by
  rw [check, Bool.and_eq_true, FullPublicReduction.check_view_iff, rawCheck_view_iff]
  constructor
  · rintro ⟨publicOnly, wins⟩
    exact ⟨publicOnly, (publicOnly.atomicPossibleWin_iff winner).mpr wins⟩
  · rintro ⟨publicOnly, possible⟩
    exact ⟨publicOnly, (publicOnly.atomicPossibleWin_iff winner).mp possible⟩

/-- The complete typed input problem checks both the public-syntax condition
and atomic possible-win existence in deterministic polynomial time. -/
theorem atomicPossibleWin_mem_P (winner : Fin K) :
    {term : Tree K | term.IsPublic ∧ term.AtomicPossibleWin winner} ∈
      Cslib.Complexity.P (termEncoding K) :=
  ⟨check winner, check_polyTime winner, fun term => (check_iff winner term).symm⟩

noncomputable def checkWord (winner : Fin K) (word : List Bool) : Bool :=
  (decode word).elim false (fun raw =>
    valid K raw && FullPublicReduction.check raw && rawCheck winner raw)

theorem checkWord_polyTime (winner : Fin K) : ComputableInPolyTime (checkWord winner)
    encBits encBool := by
  let callback := encPair encBits FullTermMachines.termEncoding
  have hr := snd encBits FullTermMachines.termEncoding
  have hv := CoreExtraction.valid_polyTime.comp ((const K).prod hr)
  have hp := FullPublicReduction.check_polyTime.comp hr
  have he := (rawCheck_polyTime winner).comp hr
  exact FullTermMachines.decode_polyTime.optionElimWithInput
    (body := fun (_ : List Bool) raw =>
      valid K raw && FullPublicReduction.check raw && rawCheck winner raw)
    (const false) (bool_and' (bool_and' hv hp) he)

def wordLanguage (winner : Fin K) : Set (List Bool) :=
  {word | ∃ term : Tree K, termEncoding K term = word ∧
    term.IsPublic ∧ term.AtomicPossibleWin winner}

theorem checkWord_encode (winner : Fin K) (term : Tree K) :
    checkWord winner (termEncoding K term) = check winner term := by
  change (decode (encode (view term))).elim false (fun raw =>
    valid K raw && FullPublicReduction.check raw && rawCheck winner raw) = _
  rw [decode_encode]
  simp only [Option.elim_some, valid_view, Bool.true_and]
  rfl

theorem checkWord_iff (winner : Fin K) (word : List Bool) :
    checkWord winner word = true ↔ word ∈ wordLanguage winner := by
  constructor
  · intro accepted
    cases hd : decode word with
    | none => simp [checkWord, hd] at accepted
    | some raw =>
      have facts : (valid K raw = true ∧ FullPublicReduction.check raw = true) ∧
          rawCheck winner raw = true := by
        simpa only [checkWord, hd, Option.elim_some, Bool.and_eq_true] using accepted
      obtain ⟨term, original⟩ := exists_original_of_valid facts.1.1
      have code : termEncoding K term = word := by
        change encode (view term) = word
        rw [original]
        exact encode_of_decode hd
      refine ⟨term, code, (check_iff winner term).mp ?_⟩
      change FullPublicReduction.check (view term) && rawCheck winner (view term) = true
      rw [original, Bool.and_eq_true]
      exact ⟨facts.1.2, facts.2⟩
  · rintro ⟨term, code, publicOnly, possible⟩
    rw [← code, checkWord_encode]
    exact (check_iff winner term).mpr ⟨publicOnly, possible⟩

/-- Malformed words, invalid arrays, and terms with role switches are rejected. -/
theorem wordLanguage_mem_P (winner : Fin K) :
    wordLanguage winner ∈ Cslib.Complexity.P encBits :=
  ⟨checkWord winner, checkWord_polyTime winner, fun word => (checkWord_iff winner word).symm⟩

end KFOL.Complexity.AtomicWinPublic
