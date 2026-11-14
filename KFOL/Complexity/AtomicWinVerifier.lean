module

public import KFOL.Definitions.AtomicDecision
public import KFOL.Complexity.FullSparseSemantics
public import KFOL.Complexity.FullTermDictionary
public import KFOL.Complexity.FiniteValueWitness
public import Complexity.Computability.Complexity.Classes.NP

/-! # Native NP certificates for atomic possible winners

The certificate names one role for each original variable occurrence. Arbitrary
certificate bits decode to roles, so every evaluated input is a singleton.
The original full-term encoding retains explicit role-permutation arrays.
-/

@[expose] public section

namespace KFOL.Complexity.AtomicWinVerifier

set_option maxHeartbeats 300000

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FullTermCode

abbrev Tree (K : ℕ) := KFOL.Term (Fin K) ℕ

def termEncoding (K : ℕ) : Tree K ↪ List Bool :=
  ⟨fun term => encode (view term), fun _ _ equal => view_injective (encode_injective equal)⟩

theorem view_polyTime (K : ℕ) : ComputableInPolyTime (@view K)
    (termEncoding K) FullTermMachines.termEncoding := .of_eq (fun _ => rfl)

def labels {K : ℕ} (term : Tree K) : List ℕ := FullTermSize.labels (view term)

theorem labels_polyTime (K : ℕ) : ComputableInPolyTime (@labels K)
    (termEncoding K) (encList encNat) :=
  FullTermSize.labels_polyTime.comp (view_polyTime K)

section Positive

variable {K : ℕ} [Nonempty (Fin K)]

noncomputable def assignment (context : FiniteAlgebraVerifier.Context) : ℕ → Fin K :=
  FiniteAlgebraVerifier.lookup context

noncomputable def pairValues (K : ℕ) [Nonempty (Fin K)]
    (context : FiniteAlgebraVerifier.Context) : List ℕ :=
  context.1.flatMap (fun name => [(assignment (K := K) context name).val,
    (assignment (K := K) context name).val])

theorem pairValues_polyTime : ComputableInPolyTime (pairValues K)
    FiniteAlgebraVerifier.contextEncoding (encList encNat) := by
  let input := FiniteAlgebraVerifier.contextEncoding
  have hrole : ComputableInPolyTime (fun p : FiniteAlgebraVerifier.Context × ℕ =>
      (assignment p.1 p.2).val) (encPair input encNat) encNat :=
    (ComputableInPolyTime.of_finite (fun role : Fin K => role.val)
      (encIn := FiniteAlgebraVerifier.valueEncoding) (encOut := encNat)).comp
      FiniteAlgebraVerifier.lookup_polyTime
  exact flatMapWithInput
    (f := fun context name => [(assignment (K := K) context name).val,
      (assignment (K := K) context name).val])
    (fst (encList encNat) encBits) (cons' hrole (cons' hrole (const [])))

noncomputable def context {K : ℕ} [Nonempty (Fin K)]
    (input : Tree K × List Bool) : FullSparseEvaluation.Context :=
  (labels input.1, pairValues K (labels input.1, input.2))

theorem context_polyTime : ComputableInPolyTime (context (K := K))
    (encPair (termEncoding K) encBits) FullSparseEvaluation.contextEncoding := by
  have hnames := (labels_polyTime K).comp (fst (termEncoding K) encBits)
  have hword := snd (termEncoding K) encBits
  exact hnames.prod (pairValues_polyTime.comp (hnames.prod hword))

noncomputable def verifier (winner : Fin K) (input : Tree K × List Bool) : Bool :=
  (FullSparseEvaluation.evaluate (context input) (view input.1)).any
    (fun role => decide (role = winner.val))

theorem verifier_polyTime (winner : Fin K) : ComputableInPolyTime (verifier winner)
    (encPair (termEncoding K) encBits) encBool := by
  let input := encPair (termEncoding K) encBits
  have ht := (view_polyTime K).comp (fst (termEncoding K) encBits)
  have he := FullSparseEvaluation.evaluate_polyTime.comp (context_polyTime.prod ht)
  exact anyWithInput (test := fun (_ : Tree K × List Bool) role => decide (role = winner.val))
    he (decide_eq' (snd input encNat) (const winner.val))

theorem evaluate_represents (input : Tree K × List Bool) :
    FullSparseEvaluation.Represents
      (FullSparseEvaluation.evaluate (context input) (view input.1))
      (input.1.eval (fun name => WinnerSet.singleton
        (assignment (K := K) (labels input.1, input.2) name))) := by
  apply FullSparseEvaluation.evaluate_view_represents
  intro name hname
  let ass := assignment (K := K) (labels input.1, input.2)
  have hleaf := FullSparseEvaluation.leaf_pairValues (labels input.1)
    (fun name => (ass name, ass name)) name hname
  change FullSparseEvaluation.Represents
    (FullSparseEvaluation.leaf (labels input.1, pairValues K (labels input.1, input.2)) name)
    (WinnerSet.singleton (ass name))
  rw [show pairValues K (labels input.1, input.2) =
      FullSparseEvaluation.pairValues (labels input.1) (fun name => (ass name, ass name)) from rfl,
    hleaf]
  simp only [FullSparseEvaluation.Represents, FullSparseEvaluation.asSet,
    WinnerSet.singleton, Set.image_singleton]
  ext role
  simp

theorem verifier_iff (winner : Fin K) (input : Tree K × List Bool) :
    verifier winner input = true ↔
      winner ∈ (input.1.eval (fun name => WinnerSet.singleton
        (assignment (K := K) (labels input.1, input.2) name))).val := by
  have hr := evaluate_represents input
  simp only [verifier, List.any_eq_true, decide_eq_true_eq]
  change (∃ role ∈ _, role = winner.val) ↔ _
  rw [show (∃ role ∈ FullSparseEvaluation.evaluate (context input) (view input.1),
      role = winner.val) ↔ winner.val ∈
      FullSparseEvaluation.evaluate (context input) (view input.1) from by simp]
  change winner.val ∈ FullSparseEvaluation.asSet _ ↔ _
  rw [hr]
  constructor
  · rintro ⟨other, wins, equal⟩
    exact (Fin.val_injective equal) ▸ wins
  · intro wins
    exact ⟨winner, wins, rfl⟩

theorem verifier_sound (winner : Fin K) (term : Tree K) (certificate : List Bool)
    (accepted : verifier winner (term, certificate) = true) : term.AtomicPossibleWin winner := by
  change ∃ valuation : ℕ → Fin K,
    winner ∈ (term.eval (fun name => WinnerSet.singleton (valuation name))).val
  refine ⟨assignment (K := K) (labels term, certificate), ?_⟩
  exact (verifier_iff winner (term, certificate)).mp accepted

omit [Nonempty (Fin K)] in
private theorem eval_congr_labels (term : Tree K)
    (first second : ℕ → WinnerSet (Fin K))
    (equal : ∀ name ∈ labels term, first name = second name) :
    term.eval first = term.eval second := by
  induction term with
  | var name => exact equal name (by simp [labels, view, FullTermSize.labels])
  | winner => rfl
  | choice owner left right ihl ihr =>
    change WinnerSet.choice owner (left.eval first) (right.eval first) = _
    congr 1
    · apply ihl
      intro name member
      exact equal name (List.mem_cons_of_mem _ (List.mem_append_left _ member))
    · apply ihr
      intro name member
      exact equal name (List.mem_cons_of_mem _ (List.mem_append_right _ member))
  | rename permutation term ih =>
    change WinnerSet.rename permutation (term.eval first) = _
    congr 1
    apply ih
    intro name member
    exact equal name (List.mem_append_right _ member)

theorem verifier_complete (winner : Fin K) (term : Tree K)
    (valuation : ℕ → Fin K) (wins : winner ∈
      (term.eval (fun name => WinnerSet.singleton (valuation name))).val)
    (padding : List Bool) :
    verifier winner (term, FiniteAlgebraVerifier.witness (labels term) valuation ++ padding) = true := by
  apply (verifier_iff winner _).mpr
  have equal : term.eval (fun name => WinnerSet.singleton (assignment (K := K)
        (labels term, FiniteAlgebraVerifier.witness (labels term) valuation ++ padding) name)) =
      term.eval (fun name => WinnerSet.singleton (valuation name)) := by
    apply eval_congr_labels
    intro name hname
    congr 1
    exact FiniteAlgebraVerifier.lookup_witness (labels term) valuation name hname padding
  rw [equal]
  exact wins

theorem atomicPossibleWin_mem_NP_of_nonempty (winner : Fin K) :
    {term : Tree K | term.AtomicPossibleWin winner} ∈
      Cslib.Complexity.NP (termEncoding K) := by
  classical
  refine ⟨Polynomial.C K * Polynomial.X, verifier winner, verifier_polyTime winner, ?_⟩
  apply Cslib.Complexity.IsVerifier.of_padding
  · intro term certificate _ accepted
    exact verifier_sound winner term certificate accepted
  · intro term possible
    obtain ⟨valuation, wins⟩ := possible
    refine ⟨FiniteAlgebraVerifier.witness (labels term) valuation, ?_,
      fun padding => verifier_complete winner term valuation wins _⟩
    simp only [FiniteAlgebraVerifier.length_witness, Fintype.card_fin,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    exact Nat.mul_le_mul_left K (FullTermSize.length_labels_le_encode (view term))

end Positive

/-- The queried role itself supplies the nonempty finite valuation domain. -/
theorem atomicPossibleWin_mem_NP {K : ℕ} (winner : Fin K) :
    {term : Tree K | term.AtomicPossibleWin winner} ∈
      Cslib.Complexity.NP (termEncoding K) := by
  let _ : Nonempty (Fin K) := ⟨winner⟩
  exact atomicPossibleWin_mem_NP_of_nonempty winner

end KFOL.Complexity.AtomicWinVerifier
