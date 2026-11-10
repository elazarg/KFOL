module

public import KFOL.Complexity.CircuitCodec
public import KFOL.Complexity.CircuitEvaluator
public import KFOL.Reductions.Circuits
public import Complexity.Computability.Complexity.Classes.NP

/-! Native finite-algebra countervaluation verifier for original cached graphs. -/

@[expose] public section

namespace KFOL.Complexity.CircuitMachine

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FiniteTermCode KFOL.Complexity.FiniteAlgebraVerifier

variable {σ : ℕ → Type} [Fintype (Operation σ)]
variable {Value : Type} [Fintype Value] [Nonempty Value]
variable [(Equational.language σ).Structure Value]

def names (gates : List (RawGate σ)) : List ℕ :=
  (gates.filter (fun gate => gate.1.isNone)).map (fun gate => gate.2.1)

theorem names_polyTime : ComputableInPolyTime (names (σ := σ)) (encList gateEncoding) (encList encNat) := by
  have ho : ComputableInPolyTime (fun gate : RawGate σ => gate.1)
      gateEncoding (encOption FiniteTermMachines.operationEncoding) := by fun_prop
  have ht := bool_not.comp ho.optionIsSome
  have htest : ComputableInPolyTime (fun gate : RawGate σ => gate.1.isNone) gateEncoding encBool := by
    convert ht using 1
    funext gate
    dsimp only [Function.comp_def]
    cases gate.1 <;> rfl
  have hfilter := ComputableInPolyTime.filter htest
  have hj : ComputableInPolyTime (fun p : List (RawGate σ) × RawGate σ => p.2.2.1)
      (encPair (encList gateEncoding) gateEncoding) encNat := by fun_prop
  exact mapWithInput (f := fun (_ : List (RawGate σ)) gate => gate.2.1) hfilter hj

def sourceNames : List (Circuit.Gate σ ℕ) → List ℕ
  | [] => []
  | .input j :: gates => j :: sourceNames gates
  | .func _ _ :: gates => sourceNames gates

omit [Fintype (Operation σ)] in
theorem names_view (gates : List (Circuit.Gate σ ℕ)) : names (gates.map viewGate) = sourceNames gates := by
  induction gates with
  | nil => rfl
  | cons gate gates ih => cases gate <;> simpa [names, viewGate, sourceNames] using ih

omit [Fintype (Operation σ)] in
theorem length_sourceNames_le (gates : List (Circuit.Gate σ ℕ)) : (sourceNames gates).length ≤ gates.length := by
  induction gates with
  | nil => rfl
  | cons gate gates ih =>
    cases gate with
    | input j => simpa only [sourceNames, List.length_cons] using Nat.succ_le_succ ih
    | func => exact ih.trans (Nat.le_succ _)

omit [Fintype (Operation σ)] [Fintype Value] [Nonempty Value] in
private theorem runFrom_congr (gates : List (Circuit.Gate σ ℕ)) (v w : ℕ → Value)
    (h : ∀ j ∈ sourceNames gates, v j = w j) (cache : List Value) :
    Circuit.runFrom v gates cache = Circuit.runFrom w gates cache := by
  induction gates generalizing cache with
  | nil => rfl
  | cons gate gates ih =>
    have ht : ∀ j ∈ sourceNames gates, v j = w j := by
      intro j hj
      apply h
      cases gate with
      | input i => exact List.mem_cons_of_mem _ hj
      | func => exact hj
    have hg : gate.eval v cache = gate.eval w cache := by
      cases gate with
      | input j => exact congrArg some (h j (List.mem_cons_self ..))
      | func => rfl
    rw [Circuit.runFrom, Circuit.runFrom, hg]
    cases he : gate.eval w cache with
    | none => rfl
    | some value => exact ih ht (cache ++ [value])

omit [Fintype (Operation σ)] [Fintype Value] [Nonempty Value] in
theorem evaluate_congr (equation : Circuit.Equation σ ℕ) (v w : ℕ → Value)
    (h : ∀ j ∈ sourceNames equation.gates, v j = w j) : equation.eval v = equation.eval w := by
  unfold Circuit.Equation.eval
  rw [runFrom_congr equation.gates v w h []]

noncomputable def unequal (result : Value × Value) : Bool := by
  classical
  exact decide (result.1 ≠ result.2)

omit [Fintype (Operation σ)] [Fintype Value] [Nonempty Value] in
@[simp] theorem unequal_eq_true (result : Value × Value) : unequal result = true ↔ result.1 ≠ result.2 := by
  classical
  simp only [unequal, decide_eq_true_eq]

noncomputable def verifier (input : RawEquation σ × List Bool) : Bool := by
  classical
  exact (evaluate (names input.1.1, input.2) input.1 : Option (Value × Value)).elim true
    unequal

theorem verifier_polyTime : ComputableInPolyTime (verifier (σ := σ) (Value := Value))
    (encPair dataEncoding encBits) encBool := by
  classical
  have hg : ComputableInPolyTime (fun p : RawEquation σ × List Bool => p.1.1)
      (encPair dataEncoding encBits) (encList gateEncoding) := by fun_prop
  have hn := names_polyTime.comp hg
  have hw := snd (dataEncoding (σ := σ)) encBits
  have hd := fst (dataEncoding (σ := σ)) encBits
  have he := (evaluate_polyTime (σ := σ) (Value := Value)).comp ((hn.prod hw).prod hd)
  have hdec : ComputableInPolyTime (fun p : (RawEquation σ × List Bool) × (Value × Value) => unequal p.2)
      (encPair (encPair dataEncoding encBits) (encPair valueEncoding valueEncoding)) encBool :=
    (ComputableInPolyTime.of_finite (unequal (Value := Value))).comp (snd _ _)
  exact he.optionElimWithInput (body := fun (_ : RawEquation σ × List Bool) p => unequal p) (const true) hdec

omit [Fintype (Operation σ)] in
private theorem verifier_source_eq (equation : Circuit.Equation σ ℕ) (word : List Bool) :
    verifier (view equation, word) (Value := Value) =
      (equation.eval (lookup (sourceNames equation.gates, word) : ℕ → Value)).elim true
        unequal := by
  classical
  unfold verifier
  rw [show (view equation).1 = equation.gates.map viewGate from rfl, names_view, evaluate_view]

omit [Fintype (Operation σ)] in
theorem verifier_sound (equation : Circuit.Equation σ ℕ) (word : List Bool)
    (h : verifier (view equation, word) (Value := Value) = true) : ¬equation.Holds Value := by
  classical
  intro hh
  obtain ⟨value, hv⟩ := hh.2 (lookup (sourceNames equation.gates, word))
  rw [verifier_source_eq, hv, Option.elim_some] at h
  exact (unequal_eq_true _).mp h rfl

omit [Fintype (Operation σ)] in
theorem verifier_complete (equation : Circuit.Equation σ ℕ) (h : ¬equation.Holds Value) :
    ∃ word : List Bool, word.length ≤ Fintype.card Value * (sourceNames equation.gates).length ∧
      ∀ padding, verifier (view equation, word ++ padding) (Value := Value) = true := by
  classical
  by_cases hwf : equation.WellFormed
  · have hn : ¬∀ v : ℕ → Value, ∃ value, equation.eval v = some (value, value) := fun hv => h ⟨hwf, hv⟩
    obtain ⟨valuation, hv⟩ := not_forall.mp hn
    obtain ⟨left, right, he⟩ := equation.eval_some_of_wellFormed hwf valuation
    have hne : left ≠ right := by
      intro heq
      exact hv ⟨right, heq ▸ he⟩
    refine ⟨witness (sourceNames equation.gates) valuation, by simp, fun padding => ?_⟩
    rw [verifier_source_eq, evaluate_congr equation _ valuation
      (fun j hj => lookup_witness (sourceNames equation.gates) valuation j hj padding), he]
    exact (unequal_eq_true _).mpr hne
  · refine ⟨[], by simp, fun padding => ?_⟩
    rw [verifier_source_eq, equation.eval_eq_none_of_not_wellFormed hwf]
    rfl


noncomputable def wordVerifier (input : List Bool × List Bool) : Bool :=
  (decodeData (σ := σ) input.1).elim true (fun data => verifier (data, input.2) (Value := Value))

theorem wordVerifier_polyTime : ComputableInPolyTime (wordVerifier (σ := σ) (Value := Value))
    (encPair encBits encBits) encBool := by
  have hd := (decodeData_polyTime (σ := σ)).comp (fst encBits encBits)
  have hdata := snd (encPair encBits encBits) (dataEncoding (σ := σ))
  have hw : ComputableInPolyTime (fun p : (List Bool × List Bool) × RawEquation σ => p.1.2)
      (encPair (encPair encBits encBits) dataEncoding) encBits := by fun_prop
  have hbody := (verifier_polyTime (σ := σ) (Value := Value)).comp (hdata.prod hw)
  exact hd.optionElimWithInput (body := fun (p : List Bool × List Bool) data => verifier (data, p.2) (Value := Value))
    (const true) hbody

private theorem wordVerifier_sound (word certificate : List Bool)
    (h : wordVerifier (word, certificate) (σ := σ) (Value := Value) = true) :
    word ∉ Circuit.Code.Language σ Value := by
  rintro ⟨equation, rfl, hh⟩
  unfold wordVerifier at h
  rw [decodeData_eq, Circuit.Code.decode_encode, Option.map_some, Option.elim_some] at h
  exact verifier_sound equation certificate h hh

private theorem wordVerifier_complete (word : List Bool) (h : word ∉ Circuit.Code.Language σ Value) :
    ∃ certificate : List Bool, certificate.length ≤ Fintype.card Value * word.length ∧
      ∀ padding, wordVerifier (word, certificate ++ padding) (σ := σ) (Value := Value) = true := by
  classical
  cases hd : Circuit.Code.decode σ word with
  | none =>
    refine ⟨[], by simp, fun padding => ?_⟩
    unfold wordVerifier
    rw [decodeData_eq, hd]
    rfl
  | some equation =>
    have hnot : ¬equation.Holds Value := fun hh => h ⟨equation, Circuit.Code.encode_of_decode σ hd, hh⟩
    obtain ⟨certificate, hsize, haccept⟩ := verifier_complete equation hnot
    refine ⟨certificate, ?_, fun padding => ?_⟩
    · have hnames := (length_sourceNames_le equation.gates).trans (Circuit.Code.gates_length_le_encode σ equation)
      rw [Circuit.Code.encode_of_decode σ hd] at hnames
      exact hsize.trans (Nat.mul_le_mul_left _ hnames)
    · unfold wordVerifier
      rw [decodeData_eq, hd, Option.map_some, Option.elim_some]
      exact haccept padding

/-- Complete native word-language coNP bound for every fixed finite algebra
and fixed finite signature, using original cached nodes and a physical-input
countervaluation certificate. No graph is unfolded by this verifier. -/
theorem language_mem_coNP : Circuit.Code.Language σ Value ∈ Cslib.Complexity.coNP encBits := by
  classical
  change (Circuit.Code.Language σ Value)ᶜ ∈ Cslib.Complexity.NP encBits
  refine ⟨Polynomial.C (Fintype.card Value) * Polynomial.X,
    wordVerifier (σ := σ) (Value := Value), wordVerifier_polyTime (σ := σ) (Value := Value), ?_⟩
  apply Cslib.Complexity.IsVerifier.of_padding
  · intro word certificate _ h
    exact wordVerifier_sound word certificate h
  · intro word h
    obtain ⟨certificate, hsize, hpadding⟩ := wordVerifier_complete word h
    refine ⟨certificate, ?_, fun n => hpadding (List.replicate n false)⟩
    simpa only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, encBits_apply] using hsize

end KFOL.Complexity.CircuitMachine
