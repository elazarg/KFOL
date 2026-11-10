module

public import KFOL.Definitions.Complexity
public import KFOL.Results.Certificates

/-! # Complexity results for the mathematical decision-problem interface

The original typed, machine and codec certificates remain in Certificates.
These statements consolidate the main paper's signatures and algorithms.
-/

@[expose] public section
namespace KFOL.Results.Complexity

open Problems
universe u

/-- Fixed-instance and binary-K complexity for C, A and A^sym. -/
theorem equational_complexity (signature : PublicSignature) :
    (∀ K : ℕ, 3 ≤ K → Cslib.Complexity.coNPComplete (fullEquationEncoding K) (fullEquations signature K)) ∧
    Cslib.Complexity.coNPComplete wordEncoding (uniformFullLanguage signature) := by
  cases signature with
  | core =>
    constructor
    · intro K hK
      exact (_root_.KFOL.Results.fixed_equational_complexity K hK).2.2
    · simpa only [uniformFullLanguage,encodedLanguage,fullEquations,PublicSignature.Admissible,
        Function.Embedding.coeFn_mk,Set.mem_ofPred_eq,and_left_comm] using (_root_.KFOL.Results.uniform_equational_complexity).2.2
  | publicLanguage =>
    constructor
    · intro K hK
      exact (_root_.KFOL.Results.fixed_equational_complexity K hK).2.1
    · simpa only [uniformFullLanguage,encodedLanguage,fullEquations,PublicSignature.Admissible,
        Function.Embedding.coeFn_mk,Set.mem_ofPred_eq,and_left_comm] using (_root_.KFOL.Results.uniform_equational_complexity).2.1
  | symmetric =>
    constructor
    · intro K hK
      simpa only [fullEquations,PublicSignature.Admissible,true_and,fullEquationEncoding,
        _root_.KFOL.Complexity.FullHardness.originalEquationEncoding] using
        (_root_.KFOL.Results.fixed_equational_complexity K hK).1
    · simpa only [uniformFullLanguage,encodedLanguage,fullEquations,PublicSignature.Admissible,
        Function.Embedding.coeFn_mk,Set.mem_ofPred_eq,true_and,and_left_comm] using (_root_.KFOL.Results.uniform_equational_complexity).1

theorem raw_pair_dichotomy {Role : Type} [Fintype Role] (three : Fin 3 ↪ Role)
    (selected : Finset (Raw.Operation Role)) :
    (selected.card ≤ 1 → rawLanguage selected ∈ Cslib.Complexity.P wordEncoding) ∧
    (1 < selected.card → Cslib.Complexity.coNPComplete wordEncoding (rawLanguage selected)) :=
  _root_.KFOL.Results.raw_signature_dichotomy three selected

theorem owner_count_dichotomy {Role : Type} [Fintype Role] [DecidableEq Role]
    (three : Fin 3 ↪ Role) (owners : Finset Role) :
    (owners.card ≤ 1 → ownerLanguage owners Eq ∈ Cslib.Complexity.P wordEncoding) ∧
    (1 < owners.card → Cslib.Complexity.coNPComplete wordEncoding (ownerLanguage owners Eq)) ∧
    ∀ observer : Role,
      ((owners.erase observer).card ≤ 1 →
        ownerLanguage owners (fun x y => observer ∈ x.val → observer ∈ y.val) ∈ Cslib.Complexity.P wordEncoding ∧
        ownerLanguage owners (fun x y => observer ∈ x.val ↔ observer ∈ y.val) ∈ Cslib.Complexity.P wordEncoding) ∧
      (1 < (owners.erase observer).card →
        Cslib.Complexity.coNPComplete wordEncoding
          (ownerLanguage owners (fun x y => observer ∈ x.val → observer ∈ y.val)) ∧
        Cslib.Complexity.coNPComplete wordEncoding
          (ownerLanguage owners (fun x y => observer ∈ x.val ↔ observer ∈ y.val))) :=
  _root_.KFOL.Results.owner_count_dichotomy three owners

theorem policy_family_dichotomy {Role Label : Type}
    [Fintype Role] [Fintype Label] [DecidableEq Role] [DecidableEq Label]
    (policies : Label → Finset Role) (three : Fin 3 ↪ Role) :
    (Policies.FamilyEasy (policySets policies) → policyLanguage policies ∈ Cslib.Complexity.P wordEncoding) ∧
    (¬Policies.FamilyEasy (policySets policies) →
      Cslib.Complexity.coNPComplete wordEncoding (policyLanguage policies)) :=
  _root_.KFOL.Results.policy_family_dichotomy policies three

/-- The two-owner selective operation is exactly the singleton policy-family
extension, whose passing patterns form a chain. -/
theorem two_owner_selective {Role : Type} [Fintype Role] [DecidableEq Role]
    (three : Fin 3 ↪ Role) (a b : Role) (hab : a ≠ b) :
    (∀ X Y Z : WinnerSet Role,
      WinnerSet.twoOwnerSelective a b X Y Z = WinnerSet.policyReset {a,b} X Y Z) ∧
    policyLanguage (fun _ : Unit => ({a,b} : Finset Role)) ∈ Cslib.Complexity.P wordEncoding := by
  constructor
  · exact WinnerSet.twoOwnerSelective_eq_policyReset a b hab
  · apply (policy_family_dichotomy (fun _ : Unit => ({a,b} : Finset Role)) three).1
    left
    apply (Policies.patternChain_iff_policies_chain _).2
    intro i j
    exact Or.inl (by simp [policySets])

theorem guarded_pair_complexity {Role : Type} [Fintype Role] (first second marker : Role)
    (different : first ≠ second) (outside_first : first ≠ marker) (outside_second : second ≠ marker) :
    Cslib.Complexity.coNPComplete wordEncoding (guardedLanguage first second) :=
  (_root_.KFOL.Results.guarded_pair_complexity first second marker different outside_first outside_second).2.1

theorem reset_circuit_complexity {Role : Type u} (three : Fin 3 ↪ Role) :
    Cslib.Complexity.coNPComplete wordEncoding (resetCircuitLanguage Role) ∧
    Cslib.Complexity.coNPComplete wordEncoding resetChainCircuitLanguage :=
  ⟨_root_.KFOL.Results.reset_circuit_complexity three,_root_.KFOL.Results.reset_chain_circuit_complexity⟩

/-- A canonicalizer with any polynomial-time comparison procedure would
collapse P and NP; correctness is required only on original core terms. -/
theorem canonicalization_collapse {K : ℕ} (three : Fin 3 ↪ Fin K)
    (canonicalize : CoreTerm K → List Bool) (runtime : PolynomialTime canonicalize (coreTermEncoding K) wordEncoding)
    (compare : List Bool × List Bool → Bool)
    (comparison : PolynomialTime compare pairWordEncoding booleanEncoding)
    (correct : ∀ s t : CoreTerm K, compare (canonicalize s,canonicalize t) = true ↔ s.val.Equivalent t.val) :
    Cslib.Complexity.P wordEncoding = Cslib.Complexity.NP wordEncoding :=
  _root_.KFOL.Results.core_canonicalization_collapse three canonicalize runtime compare comparison correct

private theorem reset_word_correct {Role : Type u} (three : Fin 3 ↪ Role) (word : List Bool) :
    Algorithms.ResetEquation.checkWord word = true ↔ word ∈ resetLanguage Role := by
  rw [(_root_.KFOL.Results.reset_binary_equation_checker three).2.1 word]
  constructor
  · rintro ⟨s,t,hcode,hvalid⟩
    exact ⟨(s,t),hcode.symm,hvalid⟩
  · rintro ⟨⟨s,t⟩,hcode,hvalid⟩
    exact ⟨s,t,hcode.symm,hvalid⟩

private theorem owner_word_correct {Role : Type u} [DecidableEq Role]
    (three : Fin 3 ↪ Role) (owner : Role) (word : List Bool) :
    _root_.KFOL.Complexity.OwnerTermFrontend.checkWord word = true ↔ word ∈ oneOwnerLanguage owner := by
  obtain ⟨observer,different,_⟩ := exists_role_outside_pair three owner owner
  rw [(_root_.KFOL.Results.owner_original_word_checker three owner observer different).2 word]
  constructor
  · rintro ⟨s,t,hcode,hvalid⟩
    exact ⟨(s,t),hcode,hvalid⟩
  · rintro ⟨⟨s,t⟩,hcode,hvalid⟩
    exact ⟨s,t,hcode,hvalid⟩

theorem reset_equality_polynomial {Role : Type u} (three : Fin 3 ↪ Role) :
    resetLanguage Role ∈ Cslib.Complexity.P wordEncoding :=
  ⟨Algorithms.ResetEquation.checkWord,(_root_.KFOL.Results.reset_binary_equation_checker three).2.2.2,
    fun word => (reset_word_correct three word).symm⟩

theorem one_owner_equality_polynomial {Role : Type u} [DecidableEq Role]
    (three : Fin 3 ↪ Role) (owner : Role) : oneOwnerLanguage owner ∈ Cslib.Complexity.P wordEncoding := by
  obtain ⟨observer,different,_⟩ := exists_role_outside_pair three owner owner
  exact ⟨_root_.KFOL.Complexity.OwnerTermFrontend.checkWord,
    (_root_.KFOL.Results.owner_original_word_checker three owner observer different).1,
    fun word => (owner_word_correct three owner word).symm⟩

/-- The SAME two word algorithms work for every ambient role carrier and
owner interpretation; their polynomial clocks do not depend on K. -/
theorem uniform_equality_algorithms :
    ∃ resetCheck ownerCheck : List Bool → Bool,
      PolynomialTime resetCheck wordEncoding booleanEncoding ∧
      PolynomialTime ownerCheck wordEncoding booleanEncoding ∧
      ∀ (Role : Type u) [DecidableEq Role] (_three : Fin 3 ↪ Role),
        (∀ word, resetCheck word = true ↔ word ∈ resetLanguage Role) ∧
        (∀ owner word, ownerCheck word = true ↔ word ∈ oneOwnerLanguage (Role := Role) owner) := by
  refine ⟨Algorithms.ResetEquation.checkWord,_root_.KFOL.Complexity.OwnerTermFrontend.checkWord,
    (_root_.KFOL.Results.reset_binary_equation_checker (Function.Embedding.refl (Fin 3))).2.2.2,
    (_root_.KFOL.Results.owner_original_word_checker (Function.Embedding.refl (Fin 3)) 0 1 (by decide)).1,?_⟩
  intro Role _ three
  exact ⟨fun word => reset_word_correct three word,fun owner word => owner_word_correct three owner word⟩

private theorem reset_check_iff_realizable (table : Algorithms.GuardDescriptor) :
    table.check = true ↔ ResetTableRealizable table := by
  constructor
  · intro accepted
    obtain ⟨term,realizes,_⟩ := table.check_iff_bounded_realization.mp accepted
    exact ⟨term,realizes⟩
  · rintro ⟨term,realizes⟩
    apply table.check_eq_true.mpr
    refine ⟨term.root,?_⟩
    change (Reset.GuardTable.mk term.root table.guards).WellFormed
    rw [← realizes]
    exact term.guardTable_wellFormed

private theorem reset_recognize_iff (word : List Bool) :
    Algorithms.GuardDescriptor.recognize word = true ↔ word ∈ resetTableLanguage := by
  constructor
  · intro accepted
    obtain ⟨table,term,hcode,realizes,_⟩ := Algorithms.GuardDescriptor.recognize_eq_true word |>.mp accepted
    exact ⟨table,hcode.symm,term,realizes⟩
  · rintro ⟨table,hcode,realizes⟩
    change table.encode = word at hcode
    rw [← hcode]
    simp only [Algorithms.GuardDescriptor.recognize,Algorithms.GuardDescriptor.decode_encode]
    exact (reset_check_iff_realizable table).mpr realizes

theorem reset_table_recognition_polynomial : resetTableLanguage ∈ Cslib.Complexity.P wordEncoding :=
  ⟨Algorithms.GuardDescriptor.recognize,
    (_root_.KFOL.Results.reset_encoded_table_recognition).2.2.2.2,fun word => (reset_recognize_iff word).symm⟩

/-- A polynomial-time partial synthesis map, specified by realizability and
exact output syntax/table/size rather than by its internal saturation state. -/
private theorem reset_table_synthesis_descriptors :
    ∃ synthesize : List Bool → Option (List Bool), PolynomialTime synthesize wordEncoding partialWordEncoding ∧
      (∀ word, (synthesize word).isSome = true ↔ word ∈ resetTableLanguage) ∧
      ∀ table : Algorithms.GuardDescriptor, ResetTableRealizable table →
        ∃ word, synthesize table.encode = some word ∧ ResetSynthesisOutput table word := by
  refine ⟨_root_.KFOL.Complexity.ResetSynthesis.synthesizeCode,_root_.KFOL.Results.reset_synthesis_runtime,?_,?_⟩
  · intro word
    rw [_root_.KFOL.Results.reset_synthesis_recognition]
    exact reset_recognize_iff word
  · intro table realizable
    have accepted := (reset_check_iff_realizable table).mpr realizable
    obtain ⟨root,term,output,_,realizes,size⟩ := _root_.KFOL.Results.reset_synthesis_table table accepted
    refine ⟨Algorithms.TermCode.encode (term.relabel table.labels.get),?_,term,realizes,size,rfl⟩
    rw [_root_.KFOL.Complexity.ResetSynthesis.synthesizeCode_encode,output]
    rfl

/-- The public synthesis specification concerns arbitrary input/output words,
without exposing the internal descriptor representation. -/
theorem reset_table_synthesis_polynomial :
    ∃ synthesize : List Bool → Option (List Bool), PolynomialTime synthesize wordEncoding partialWordEncoding ∧
      (∀ input, (synthesize input).isSome = true ↔ input ∈ resetTableLanguage) ∧
      ∀ input output, synthesize input = some output → ResetSynthesis input output := by
  obtain ⟨synthesize,runtime,accepted,typed⟩ := reset_table_synthesis_descriptors
  refine ⟨synthesize,runtime,accepted,?_⟩
  intro input output produced
  have success := Option.isSome_iff_exists.mpr ⟨output,produced⟩
  obtain ⟨table,hcode,realizable⟩ := (accepted input).mp success
  change table.encode = input at hcode
  obtain ⟨word,emitted,spec⟩ := typed table realizable
  rw [hcode] at emitted
  have equal := Option.some.inj (emitted.symm.trans produced)
  subst word
  exact ⟨table,hcode,spec⟩

private theorem owner_check_iff_realizable {Role : Type} [DecidableEq Role]
    (three : Fin 3 ↪ Role) (owner : Role) (input : OwnerTableInput) :
    input.2.check (List.finRange input.1) = true ↔ OwnerTableRealizable owner input := by
  obtain ⟨observer,different,_⟩ := exists_role_outside_pair three owner owner
  obtain ⟨background,hbo,hbk⟩ := exists_role_outside_pair three owner observer
  have listed : input.2.Listed (List.finRange input.1) := by
    constructor
    · exact List.mem_finRange _
    · intro p _ j _
      exact List.mem_toFinset.mpr (List.mem_finRange j)
  constructor
  · intro accepted
    have canonical := ((input.2.check_iff _).mp accepted).1
    exact ⟨canonical,(input.2.check_iff_realizable owner observer background different hbk.symm hbo.symm
      _ canonical listed).mp accepted⟩
  · rintro ⟨canonical,realizes⟩
    exact (input.2.check_iff_realizable owner observer background different hbk.symm hbo.symm
      _ canonical listed).mpr realizes

/-- Actual canonical-table recognition and expanded primitive-tree synthesis,
with their original dimension/bitset input encoding and O(nM) output bound. -/
theorem owner_table_algorithms {Role : Type} [Fintype Role] [DecidableEq Role]
    (three : Fin 3 ↪ Role) (owner : Role) :
    {input : OwnerTableInput | OwnerTableRealizable owner input} ∈ Cslib.Complexity.P ownerTableEncoding ∧
    ∃ synthesize : OwnerTableInput → Option (OwnerTableOutput Role),
      PolynomialTime synthesize ownerTableEncoding (ownerTableOutputEncoding Role) ∧
      (∀ input, (synthesize input).isSome = true ↔ OwnerTableRealizable owner input) ∧
      ∀ input output, synthesize input = some output → OwnerSynthesisOutput owner input output := by
  constructor
  · exact ⟨fun input => input.2.check (List.finRange input.1),_root_.KFOL.Results.owner_table_runtime,
      fun input => (owner_check_iff_realizable three owner input).symm⟩
  · refine ⟨fun input => (input.2.synthesize owner (List.finRange input.1)).map
      (fun term => (⟨input.1,term⟩ : OwnerTableOutput Role)),
      _root_.KFOL.Results.owner_synthesis_runtime owner,?_,?_⟩
    · intro input
      rw [Option.isSome_map,input.2.synthesize_isSome]
      exact owner_check_iff_realizable three owner input
    · intro input output produced
      obtain ⟨term,ht,hcode⟩ := Option.map_eq_some_iff.mp produced
      obtain ⟨realizes,size⟩ := input.2.synthesize_spec owner (List.finRange input.1) ht
      exact ⟨term,hcode.symm,realizes,by simpa using size⟩

theorem core_extraction_polynomial :
    ∃ extract : List Bool → Option (List Bool), PolynomialTime extract wordEncoding partialWordEncoding ∧
      ∀ (K : ℕ) (_large : 3 ≤ K) (term : Term (Fin K) ℕ),
        ((extract (termCode K term)).isSome = true ↔ term.Idempotent) ∧
        ∀ word, extract (termCode K term) = some word → CoreExtractionOutput K term word := by
  have certificate := _root_.KFOL.Results.uniform_core_extraction_runtime
  refine ⟨FullTermCode.extractWord,certificate.1,?_⟩
  intro K large term
  let three : Fin 3 ↪ Fin K :=
    ⟨fun i => ⟨i.val,lt_of_lt_of_le i.isLt large⟩,fun _ _ h => Fin.ext (congrArg (fun i : Fin K => i.val) h)⟩
  have checked := _root_.KFOL.Results.checked_core_extraction three term
  constructor
  · rw [termCode,certificate.2 K term,Option.isSome_map]
    exact Option.isSome_iff_exists.trans checked.1
  · intro word output
    rw [termCode,certificate.2 K term] at output
    obtain ⟨core,hcore,hcode⟩ := Option.map_eq_some_iff.mp output
    obtain ⟨isCore,equal,size⟩ := checked.2 core hcore
    exact ⟨core,isCore,equal,size,hcode.symm⟩

end KFOL.Results.Complexity
