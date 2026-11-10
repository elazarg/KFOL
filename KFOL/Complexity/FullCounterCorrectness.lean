module
public import KFOL.Complexity.FullCounterVerifier
public import Complexity.Computability.Complexity.Classes.NP
public import KFOL.Algebra.PairTests
public import KFOL.Complexity.FullCertificateSize
public import Mathlib.Data.Nat.Size
@[expose] public section
namespace KFOL.Complexity.FullCounterVerifier
open KFOL.FullTermCode
open FullSparseEvaluation

private def rawView (input : EquationInput) : RawInput :=
  (input.1,(view input.2.1,view input.2.2))
private def GoodInput (coreOnly : Bool) (input : EquationInput) : Prop :=
  3 ≤ input.1 ∧ (if coreOnly then input.2.1.IsCore ∧ input.2.2.IsCore else True)

private theorem encode_rawView (input : EquationInput) :
    FullInputMachines.encodeRawInput (rawView input) = encodeEquationInput input := rfl
private theorem decode_original (input : EquationInput) :
    FullInputMachines.decodeInput (encodeEquationInput input) = some (rawView input) := by
  rw [← encode_rawView input]
  exact FullInputMachines.decodeInput_encodeRawInput (rawView input)

private theorem mode_membership (coreOnly : Bool) (word : List Bool) :
    word ∈ (if coreOnly then CoreLanguage else FullLanguage) ↔
      ∃ input : EquationInput, GoodInput coreOnly input ∧ encodeEquationInput input = word ∧
        ∀ valuation : ℕ → WinnerSet (Fin input.1), input.2.1.eval valuation = input.2.2.eval valuation := by
  cases coreOnly
  · simp only [Bool.false_eq_true,ite_false,FullLanguage,Set.mem_ofPred_eq,GoodInput,and_true]
  · simp only [ite_true,CoreLanguage,Set.mem_ofPred_eq,GoodInput]
    constructor
    · rintro ⟨input,hs,hcode,hl,hr,he⟩
      exact ⟨input,⟨hs,hl,hr⟩,hcode,he⟩
    · rintro ⟨input,⟨hs,hl,hr⟩,hcode,he⟩
      exact ⟨input,hs,hcode,hl,hr,he⟩

private theorem sourceOk_original (coreOnly : Bool) (input : EquationInput) :
    sourceOk coreOnly (rawView input) = true ↔ GoodInput coreOnly input := by
  cases coreOnly <;> simp [sourceOk,rawView,GoodInput,FullCorePredicate.check_view_iff]
  · exact ⟨fun h => of_decide_eq_true h,fun h => decide_eq_true h⟩
  · intro _ _
    exact ⟨fun h => of_decide_eq_true h,fun h => decide_eq_true h⟩

private theorem decoded_false_of_valid (coreOnly : Bool) (input : EquationInput) (good : GoodInput coreOnly input)
    (equation : ∀ valuation : ℕ → WinnerSet (Fin input.1), input.2.1.eval valuation = input.2.2.eval valuation)
    (certificate : List Bool) : decodedVerifier coreOnly (rawView input,certificate) = false := by
  have hok := (sourceOk_original coreOnly input).mpr good
  simp only [decodedVerifier,hok,ite_true]
  cases hd : decodeWitness certificate with
  | none => rfl
  | some values =>
    simp only [Option.elim_some]
    change (if values.all (fun role => decide (role < input.1)) then failure (rawView input) values else false) = false
    by_cases hrange : values.all (fun role => decide (role < input.1)) = true
    · rw [ite_eq_left hrange]
      have hb : ∀ role ∈ values, role < input.1 := by simpa only [List.all_eq_true,decide_eq_true_eq] using hrange
      have hpositive : 0 < input.1 := by have h := good.1; omega
      let context : Context := (dictionary (rawView input),values)
      have hleft := evaluate_view_contextValuation hpositive context hb input.2.1
      have hright := evaluate_view_contextValuation hpositive context hb input.2.2
      have he := (represents_equal_iff hleft hright).mpr (equation _)
      have heq := (setEqB_iff _ _).mpr he
      change (Bool.not (setEqB (evaluate context (view input.2.1)) (evaluate context (view input.2.2)))) = false
      rw [heq]
      rfl
    · rw [ite_eq_right hrange]

/-- Every accepted countercertificate refutes the independent original-input
language. Malformed original words are outside the existential encoding image. -/
theorem verifier_sound (coreOnly : Bool) (word certificate : List Bool)
    (h : verifier coreOnly (word,certificate) = true) : word ∉ (if coreOnly then CoreLanguage else FullLanguage) := by
  intro hm
  obtain ⟨input,good,hcode,equation⟩ := (mode_membership coreOnly word).mp hm
  have hd : FullInputMachines.decodeInput word = some (rawView input) := by rw [← hcode]; exact decode_original input
  simp only [verifier,hd,Option.elim_some] at h
  have hf := decoded_false_of_valid coreOnly input good equation certificate
  rw [hf] at h
  contradiction

private theorem represents_pair {K : ℕ} (A : WinnerSet (Fin K)) (a b : Fin K) (h : A.val = {a,b}) :
    Represents [a.val,b.val] A := by
  change asSet [a.val,b.val] = Fin.val '' A.val
  rw [h]
  ext role
  simp [asSet]

private theorem failure_iff (input : RawInput) (values : List ℕ) : failure input values = true ↔
    asSet (evaluate (dictionary input,values) input.2.1) ≠ asSet (evaluate (dictionary input,values) input.2.2) := by
  change (Bool.not (setEqB _ _)) = true ↔ _
  constructor
  · intro h he
    have ht := (setEqB_iff _ _).mpr he
    rw [ht] at h
    contradiction
  · intro h
    cases hb : setEqB (evaluate (dictionary input,values) input.2.1) (evaluate (dictionary input,values) input.2.2) with
    | false => rfl
    | true => exact False.elim (h ((setEqB_iff _ _).mp hb))

private theorem failure_pairValues (input : EquationInput) (valuation : ℕ → WinnerSet (Fin input.1))
    (pairs : ℕ → Fin input.1 × Fin input.1)
    (hpairs : ∀ j, (valuation j).val = {(pairs j).1,(pairs j).2})
    (hne : input.2.1.eval valuation ≠ input.2.2.eval valuation) :
    failure (rawView input) (pairValues (dictionary (rawView input)) pairs) = true := by
  let names := dictionary (rawView input)
  let context : Context := (names,pairValues names pairs)
  have hleaf : ∀ j ∈ names, Represents (leaf context j) (valuation j) := by
    intro j hj
    rw [leaf_pairValues names pairs j hj]
    exact represents_pair _ _ _ (hpairs j)
  have hl := evaluate_view_represents context input.2.1 valuation (fun j hj => hleaf j (List.mem_append_left _ hj))
  have hr := evaluate_view_represents context input.2.2 valuation (fun j hj => hleaf j (List.mem_append_right _ hj))
  apply (failure_iff _ _).mpr
  intro he
  exact hne ((represents_equal_iff hl hr).mp he)


private theorem original_of_sourceOk (coreOnly : Bool) (input : RawInput) (h : sourceOk coreOnly input = true) :
    ∃ original : EquationInput, rawView original = input ∧ GoodInput coreOnly original := by
  have hflags : 3 ≤ input.1 ∧ valid input.1 input.2.1 = true ∧ valid input.1 input.2.2 = true ∧
      (if coreOnly then FullCorePredicate.check input.2.1 && FullCorePredicate.check input.2.2 else true) = true := by
    simpa only [sourceOk,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using h
  obtain ⟨left,hleft⟩ := exists_original_of_valid hflags.2.1
  obtain ⟨right,hright⟩ := exists_original_of_valid hflags.2.2.1
  let original : EquationInput := ⟨input.1,left,right⟩
  have hv : rawView original = input := Prod.ext rfl (Prod.ext hleft hright)
  refine ⟨original,hv,(sourceOk_original coreOnly original).mp ?_⟩
  rw [hv]
  exact h

private theorem typed_countercertificate (coreOnly : Bool) (input : EquationInput) (good : GoodInput coreOnly input)
    (failure : ∃ valuation : ℕ → WinnerSet (Fin input.1), input.2.1.eval valuation ≠ input.2.2.eval valuation) :
    ∃ certificate : List Bool, certificate.length ≤ 16*((encodeEquationInput input).length+1)^2 ∧
      ∀ padding : List Bool, verifier coreOnly (encodeEquationInput input,certificate ++ padding) = true := by
  classical
  obtain ⟨valuation,hpairs,hne⟩ := KFOL.Term.exists_pair_countervaluation input.2.1 input.2.2 failure
  choose first second hpair using hpairs
  let pairs := fun j => (first j,second j)
  let values := pairValues (dictionary (rawView input)) pairs
  have hbounded : ∀ role ∈ values, role < input.1 := pairValues_bounded _ _
  have hroles : values.all (fun role => decide (role < input.1)) = true :=
    List.all_eq_true.mpr (fun role hr => decide_eq_true (hbounded role hr))
  have hf : FullCounterVerifier.failure (rawView input) values = true :=
    failure_pairValues input valuation pairs hpair hne
  refine ⟨witnessWord values,?_,?_⟩
  · exact FullCertificateSize.framed_pairValues_length_le input pairs
  · intro padding
    have hok := (sourceOk_original coreOnly input).mpr good
    simp only [verifier,decode_original,Option.elim_some,decodedVerifier,hok,ite_true,
      decodeWitness_witnessWord_append]
    change (if values.all (fun role => decide (role < input.1)) then FullCounterVerifier.failure (rawView input) values else false) = true
    rw [ite_eq_left hroles]
    exact hf

/-- Every word outside the original language has a physically bounded
countercertificate stable under arbitrary trailing certificate padding. -/
theorem verifier_complete (coreOnly : Bool) (word : List Bool)
    (outside : word ∉ (if coreOnly then CoreLanguage else FullLanguage)) :
    ∃ certificate : List Bool, certificate.length ≤ 16*(word.length+1)^2 ∧
      ∀ padding : List Bool, verifier coreOnly (word,certificate ++ padding) = true := by
  classical
  cases hd : FullInputMachines.decodeInput word with
  | none =>
    exact ⟨[],by simp,fun _ => by simp only [verifier,hd,Option.elim_none]⟩
  | some input =>
    by_cases hok : sourceOk coreOnly input = true
    · obtain ⟨original,hview,good⟩ := original_of_sourceOk coreOnly input hok
      have hcode : encodeEquationInput original = word := by
        rw [← encode_rawView original,hview]
        exact FullInputMachines.encodeRawInput_of_decodeInput hd
      have hfail : ∃ valuation : ℕ → WinnerSet (Fin original.1), original.2.1.eval valuation ≠ original.2.2.eval valuation := by
        by_contra hn
        have he : ∀ valuation : ℕ → WinnerSet (Fin original.1), original.2.1.eval valuation = original.2.2.eval valuation := by
          simpa only [not_exists,not_not] using hn
        exact outside ((mode_membership coreOnly word).mpr ⟨original,good,hcode,he⟩)
      obtain ⟨certificate,hsize,hvalid⟩ := typed_countercertificate coreOnly original good hfail
      refine ⟨certificate,?_,?_⟩
      · simpa only [hcode] using hsize
      · simpa only [hcode] using hvalid
    · exact ⟨[],by simp,fun _ => by simp only [verifier,hd,Option.elim_some,decodedVerifier,hok,Bool.false_eq_true,ite_false]⟩


/-- One genuine binary-input coNP verifier works uniformly in the role count.
Every source array and every guessed role label contributes to its input size. -/
theorem language_mem_coNP (coreOnly : Bool) :
    (if coreOnly then CoreLanguage else FullLanguage) ∈ Cslib.Complexity.coNP Turing.MultiTapeTM.encBits := by
  classical
  change (if coreOnly then CoreLanguage else FullLanguage)ᶜ ∈ Cslib.Complexity.NP Turing.MultiTapeTM.encBits
  refine ⟨Polynomial.C 16 * (Polynomial.X + Polynomial.C 1)^2,verifier coreOnly,verifier_polyTime coreOnly,?_⟩
  apply Cslib.Complexity.IsVerifier.of_padding
  · intro word certificate _ h
    exact verifier_sound coreOnly word certificate h
  · intro word h
    obtain ⟨certificate,hsize,hpadding⟩ := verifier_complete coreOnly word h
    refine ⟨certificate,?_,fun padding => hpadding (List.replicate padding false)⟩
    simpa only [Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_X,
      Turing.MultiTapeTM.encBits_apply] using hsize

theorem full_mem_coNP : FullLanguage ∈ Cslib.Complexity.coNP Turing.MultiTapeTM.encBits := by
  simpa only [Bool.false_eq_true,ite_false] using language_mem_coNP false

theorem core_mem_coNP : CoreLanguage ∈ Cslib.Complexity.coNP Turing.MultiTapeTM.encBits := by
  simpa only [ite_true] using language_mem_coNP true
end KFOL.Complexity.FullCounterVerifier
