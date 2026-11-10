module
public import KFOL.Complexity.FullHardness
/-! The intermediate original signature allows winner leaves and owned
choices, while forbidding internal role permutations. The same actual core
words supply its lower bound. -/
@[expose] public section
namespace KFOL.Complexity.FullHardness
open Turing.MultiTapeTM
open KFOL.FullTermCode

@[simp] theorem publicLanguage_encode (input : EquationInput) :
    encodeEquationInput input ∈ PublicLanguage ↔
      3 ≤ input.1 ∧ input.2.1.IsPublic ∧ input.2.2.IsPublic ∧
        ∀ v : ℕ → WinnerSet (Fin input.1), input.2.1.eval v = input.2.2.eval v := by
  constructor
  · rintro ⟨other,hK,he,hleft,hright,hvalid⟩
    have hh := encodeEquationInput_injective he
    cases hh
    exact ⟨hK,hleft,hright,hvalid⟩
  · rintro ⟨hK,hleft,hright,hvalid⟩
    exact ⟨input,hK,rfl,hleft,hright,hvalid⟩

/-- The original signature without role switches is hard for every fixed role
type containing three roles, under the same actual original word embedding. -/
theorem fixed_public_coNPHard {K : ℕ} (a b d : Fin K)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    Cslib.Complexity.coNPHard (originalEquationEncoding K)
      {e | e.1.IsPublic ∧ e.2.IsPublic ∧
        ∀ v : ℕ → WinnerSet (Fin K), e.1.eval v = e.2.eval v} := by
  apply Cslib.Complexity.coNPHard.trans
    (RawPairCompleteness.twoOwners_coNPHard a b d hab had hbd)
  refine ⟨fun e => (ofPair a b e.1,ofPair a b e.2),
    (equationWord_polyTime a b).of_enc_eq (fun _ => rfl),?_⟩
  intro e
  have hl := (ofPair_isCore a b e.1).isPublic
  have hr := (ofPair_isCore a b e.2).isPublic
  simp only [RawPairCompleteness.Theory,Set.mem_ofPred_eq,hl,hr,eval_ofPair,true_and]

theorem public_coNPHard_at {K : ℕ} (hK : 3 ≤ K)
    (a b d : Fin K) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    Cslib.Complexity.coNPHard encBits PublicLanguage := by
  apply Cslib.Complexity.coNPHard.trans
    (RawPairCompleteness.twoOwners_coNPHard a b d hab had hbd)
  refine ⟨fun e => encodeEquationInput ⟨K,(ofPair a b e.1,ofPair a b e.2)⟩,
    equationWord_polyTime a b,?_⟩
  intro e
  have hl := (ofPair_isCore a b e.1).isPublic
  have hr := (ofPair_isCore a b e.2).isPublic
  simp only [publicLanguage_encode,RawPairCompleteness.Theory,Set.mem_ofPred_eq,hK,true_and,
    hl,hr,eval_ofPair]

theorem public_coNPHard : Cslib.Complexity.coNPHard encBits PublicLanguage :=
  public_coNPHard_at (K := 3) (by omega) 0 1 2 (by decide) (by decide) (by decide)
end KFOL.Complexity.FullHardness
