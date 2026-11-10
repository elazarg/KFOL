module
public import KFOL.Complexity.FullHardnessMachine
public import KFOL.Complexity.RawPairCompleteness
public import KFOL.Complexity.FullInputMachines
/-! Native hardness reductions into the actual original explicit-array full
syntax and its core restriction. The reduction uses only two owned choices. -/
@[expose] public section
namespace KFOL.Complexity.FullHardness
open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FullTermCode

/-- The original full term word at a fixed role type, including explicit
permutation arrays whenever such a source node actually occurs. -/
def originalTermEncoding (K : ℕ) : KFOL.Term (Fin K) ℕ ↪ List Bool :=
  ⟨fun t => encode (view t),fun _ _ h => view_injective (encode_injective h)⟩

/-- The original core is a subtype of the same full syntax. -/
abbrev CoreTerm (K : ℕ) := {t : KFOL.Term (Fin K) ℕ // t.IsCore}

def originalCoreTermEncoding (K : ℕ) : CoreTerm K ↪ List Bool :=
  ⟨fun t => originalTermEncoding K t.val,
    fun _ _ h => Subtype.ext ((originalTermEncoding K).injective h)⟩

/-- The fixed-role instance of the same uniform original equation encoding. -/
def originalEquationEncoding (K : ℕ) :
    (KFOL.Term (Fin K) ℕ × KFOL.Term (Fin K) ℕ) ↪ List Bool :=
  ⟨fun e => encodeEquationInput ⟨K,e⟩,fun _ _ h => by
    have he := encodeEquationInput_injective h
    cases he
    rfl⟩

@[fun_prop] theorem ofPair_polyTime {K : ℕ} (a b : Fin K) :
    ComputableInPolyTime (ofPair a b) RawPairMachines.termEncoding (originalTermEncoding K) :=
  (rawPair_polyTime a.val b.val).of_enc_eq (fun t => congrArg encode (view_ofPair a b t))

@[fun_prop] theorem ofPair_core_polyTime {K : ℕ} (a b : Fin K) :
    ComputableInPolyTime (fun t => (⟨ofPair a b t,ofPair_isCore a b t⟩ : CoreTerm K))
      RawPairMachines.termEncoding (originalCoreTermEncoding K) :=
  (ofPair_polyTime a b).of_enc_eq (fun _ => rfl)

@[fun_prop] theorem equationWord_polyTime {K : ℕ} (a b : Fin K) :
    ComputableInPolyTime
      (fun e : RawPairMachines.Tree × RawPairMachines.Tree =>
        encodeEquationInput ⟨K,(ofPair a b e.1,ofPair a b e.2)⟩)
      RawPairMachines.equationEncoding encBits := by
  have ha := FiniteTermMachines.arguments_polyTime (σ := RawPair.Symbol)
  have hl := (rawPair_polyTime a.val b.val).comp ((fst _ _).comp ha)
  have hr := (rawPair_polyTime a.val b.val).comp ((snd _ _).comp ha)
  have h := FullInputMachines.encodeRawInput_polyTime.comp ((const K).prod (hl.prod hr))
  convert h using 1
  funext e
  simp only [encodeEquationInput,FullInputMachines.encodeRawInput,FullInputMachines.encodePair,
    view_ofPair,Function.comp_def,id_eq]

@[simp] theorem fullLanguage_encode (input : EquationInput) :
    encodeEquationInput input ∈ FullLanguage ↔
      3 ≤ input.1 ∧ ∀ v : ℕ → WinnerSet (Fin input.1), input.2.1.eval v = input.2.2.eval v := by
  constructor
  · rintro ⟨other,hK,he,hvalid⟩
    have hh := encodeEquationInput_injective he
    cases hh
    exact ⟨hK,hvalid⟩
  · rintro ⟨hK,hvalid⟩
    exact ⟨input,hK,rfl,hvalid⟩

@[simp] theorem coreLanguage_encode (input : EquationInput) :
    encodeEquationInput input ∈ CoreLanguage ↔
      3 ≤ input.1 ∧ input.2.1.IsCore ∧ input.2.2.IsCore ∧
        ∀ v : ℕ → WinnerSet (Fin input.1), input.2.1.eval v = input.2.2.eval v := by
  constructor
  · rintro ⟨other,hK,he,hleft,hright,hvalid⟩
    have hh := encodeEquationInput_injective he
    cases hh
    exact ⟨hK,hleft,hright,hvalid⟩
  · rintro ⟨hK,hleft,hright,hvalid⟩
    exact ⟨input,hK,rfl,hleft,hright,hvalid⟩

/-- Hardness on the original full syntax for each role type containing three
roles; the original word encoding retains all other operations too. -/
theorem fixed_full_coNPHard {K : ℕ} (a b d : Fin K)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    Cslib.Complexity.coNPHard (originalEquationEncoding K)
      {e | ∀ v : ℕ → WinnerSet (Fin K), e.1.eval v = e.2.eval v} := by
  apply Cslib.Complexity.coNPHard.trans
    (RawPairCompleteness.twoOwners_coNPHard a b d hab had hbd)
  refine ⟨fun e => (ofPair a b e.1,ofPair a b e.2),
    (equationWord_polyTime a b).of_enc_eq (fun _ => rfl),?_⟩
  intro e
  simp only [RawPairCompleteness.Theory,Set.mem_ofPred_eq,eval_ofPair]

/-- Hardness already occurs inside the actual constant-free, switch-free core
of the original syntax, without a separately encoded surrogate signature. -/
theorem fixed_core_coNPHard {K : ℕ} (a b d : Fin K)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    Cslib.Complexity.coNPHard (originalEquationEncoding K)
      {e | e.1.IsCore ∧ e.2.IsCore ∧
        ∀ v : ℕ → WinnerSet (Fin K), e.1.eval v = e.2.eval v} := by
  apply Cslib.Complexity.coNPHard.trans
    (RawPairCompleteness.twoOwners_coNPHard a b d hab had hbd)
  refine ⟨fun e => (ofPair a b e.1,ofPair a b e.2),
    (equationWord_polyTime a b).of_enc_eq (fun _ => rfl),?_⟩
  intro e
  simp only [RawPairCompleteness.Theory,Set.mem_ofPred_eq,ofPair_isCore,eval_ofPair,true_and]

/-- Every fixed role count at least three supplies a hardness reduction to the
complete uniform full language, using its original bytes and actual semantics. -/
theorem full_coNPHard_at {K : ℕ} (hK : 3 ≤ K)
    (a b d : Fin K) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    Cslib.Complexity.coNPHard encBits FullLanguage := by
  apply Cslib.Complexity.coNPHard.trans
    (RawPairCompleteness.twoOwners_coNPHard a b d hab had hbd)
  refine ⟨fun e => encodeEquationInput ⟨K,(ofPair a b e.1,ofPair a b e.2)⟩,
    equationWord_polyTime a b,?_⟩
  intro e
  simp only [fullLanguage_encode,RawPairCompleteness.Theory,Set.mem_ofPred_eq,hK,true_and,
    eval_ofPair]

/-- The same actual words contain no constants or switches. -/
theorem core_coNPHard_at {K : ℕ} (hK : 3 ≤ K)
    (a b d : Fin K) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    Cslib.Complexity.coNPHard encBits CoreLanguage := by
  apply Cslib.Complexity.coNPHard.trans
    (RawPairCompleteness.twoOwners_coNPHard a b d hab had hbd)
  refine ⟨fun e => encodeEquationInput ⟨K,(ofPair a b e.1,ofPair a b e.2)⟩,
    equationWord_polyTime a b,?_⟩
  intro e
  simp only [coreLanguage_encode,RawPairCompleteness.Theory,Set.mem_ofPred_eq,hK,true_and,
    ofPair_isCore,eval_ofPair]

theorem full_coNPHard : Cslib.Complexity.coNPHard encBits FullLanguage :=
  full_coNPHard_at (K := 3) (by omega) 0 1 2 (by decide) (by decide) (by decide)
theorem core_coNPHard : Cslib.Complexity.coNPHard encBits CoreLanguage :=
  core_coNPHard_at (K := 3) (by omega) 0 1 2 (by decide) (by decide) (by decide)
end KFOL.Complexity.FullHardness
