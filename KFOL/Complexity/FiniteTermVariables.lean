module
public import KFOL.Complexity.FiniteTermDecoding
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
@[expose] public section
namespace KFOL.Complexity.FiniteTermVariables
open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FiniteTermCode
variable {σ : ℕ → Type} [Fintype (Operation σ)]

/-- Original left-to-right variable occurrences, retaining repeats and sparse names. -/
def names : Equational.Term σ ℕ → List ℕ
  | .var j => [j]
  | .func _ children => (List.ofFn (fun i => names (children i))).flatten

private theorem names_list_bound (terms : List (Equational.Term σ ℕ))
    (hyp : ∀ term ∈ terms, (encList encNat (names term)).length ≤ (encode σ term).length) :
    (encList encNat ((terms.map names).flatten)).length ≤
      (terms.map (fun term => (encode σ term).length)).sum := by
  induction terms with
  | nil => rfl
  | cons term terms ih =>
    have ht := hyp term (List.mem_cons_self ..)
    have hs := ih (fun t ht => hyp t (List.mem_cons_of_mem _ ht))
    simp only [List.map_cons, List.flatten_cons, encList_append, List.length_append, List.sum_cons]
    omega

theorem encoded_names_length_le (term : Equational.Term σ ℕ) :
    (encList encNat (names term)).length ≤ (encode σ term).length := by
  induction term with
  | var j =>
    simp [names, encode_var, encNat_apply, Words.BinaryNatCode.encode]
  | @func n function children ih =>
    have hs := names_list_bound (List.ofFn children) (by
      intro t ht; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht; exact ih i)
    simp only [List.map_ofFn, Function.comp_def] at hs
    simp only [names, encode_func, List.length_cons, List.length_append, List.length_flatten,
      List.map_ofFn, Function.comp_def]
    omega

theorem names_length_le (term : Equational.Term σ ℕ) : (names term).length ≤ (encode σ term).length :=
  (length_le_length_encList encNat (names term)).trans (encoded_names_length_le term)

private def leaf (_ : Unit) (j : ℕ) : List ℕ := [j]
private def node (_ : Unit) (_ : Operation σ) (children : List (List ℕ)) : List ℕ := children.flatten

omit [Fintype (Operation σ)] in
private theorem fold_names (term : Equational.Term σ ℕ) :
    FiniteFoldMachine.fold leaf node () term = names term := by
  induction term with
  | var j => rfl
  | @func n function children ih =>
    simp only [FiniteFoldMachine.fold, node, names]
    congr 1
    apply congrArg List.ofFn
    funext i
    exact ih i

theorem names_polyTime : ComputableInPolyTime (@names σ)
    FiniteTermMachines.termEncoding (encList encNat) := by
  have hleaf : ComputableInPolyTime (fun p : Unit × ℕ => leaf p.1 p.2)
      (encPair encUnit encNat) (encList encNat) := cons' (snd encUnit encNat) (const [])
  have hchildren : ComputableInPolyTime
      (fun p : Unit × (Operation σ × List (List ℕ)) => p.2.2)
      (encPair encUnit (encPair FiniteTermMachines.operationEncoding (encList (encList encNat))))
      (encList (encList encNat)) := by fun_prop
  have hnode : ComputableInPolyTime (fun p : Unit × (Operation σ × List (List ℕ)) => node p.1 p.2.1 p.2.2)
      (encPair encUnit (encPair FiniteTermMachines.operationEncoding (encList (encList encNat))))
      (encList encNat) :=
    (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.flatten encNat)).comp hchildren
  have he := FiniteFoldMachine.fold_polyTime (contextEncoding := encUnit) (valueEncoding := encList encNat)
    leaf node hleaf hnode 1 1 (by
      intro context term; cases context
      rw [fold_names]
      have ht := encoded_names_length_le term
      simp only [Nat.pow_one, Nat.one_mul]
      omega) []
  have hp : ComputableInPolyTime (fun term : Equational.Term σ ℕ => ((), term))
      FiniteTermMachines.termEncoding (encPair encUnit FiniteTermMachines.termEncoding) := (const ()).prod id'
  have h := he.comp hp
  convert h using 1
  funext term
  exact (fold_names term).symm

def equationNames (equation : Equational.Term σ ℕ × Equational.Term σ ℕ) : List ℕ :=
  names equation.1 ++ names equation.2

theorem equationNames_polyTime : ComputableInPolyTime (@equationNames σ)
    FiniteTermMachines.equationEncoding (encList encNat) := by
  have hpair := FiniteTermMachines.arguments_polyTime (σ := σ)
  exact listAppend' (names_polyTime.comp ((fst _ _).comp hpair))
    (names_polyTime.comp ((snd _ _).comp hpair))

theorem length_equationNames_le (equation : Equational.Term σ ℕ × Equational.Term σ ℕ) :
    (equationNames equation).length ≤ (encodeEquation σ equation).length := by
  have hl := names_length_le equation.1
  have hr := names_length_le equation.2
  simp only [equationNames, List.length_append, encodeEquation, Words.pair_length]
  omega

omit [Fintype (Operation σ)] in
theorem realize_congr {Value : Type} [(Equational.language σ).Structure Value]
    (term : Equational.Term σ ℕ) (v w : ℕ → Value) (h : ∀ j ∈ names term, v j = w j) :
    term.realize v = term.realize w := by
  induction term with
  | var j => exact h j (List.mem_cons_self ..)
  | @func n function children ih =>
    simp only [FirstOrder.Language.Term.realize_func]
    congr 1
    funext i
    apply ih i
    intro j hj
    exact h j (List.mem_flatten.mpr ⟨names (children i), List.mem_ofFn.mpr ⟨i, rfl⟩, hj⟩)
end KFOL.Complexity.FiniteTermVariables
