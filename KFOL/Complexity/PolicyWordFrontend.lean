module
public import KFOL.Complexity.PolicyTermFrontend
public import KFOL.Complexity.PolicyCompleteness
public import KFOL.Complexity.FiniteTermDecoding
@[expose] public section
namespace KFOL.Complexity.PolicyTermFrontend
open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.Policies KFOL.FiniteTermCode
variable {Role Label : Type} [Fintype Role] [Fintype Label] [DecidableEq Role] [DecidableEq Label]

noncomputable def checkWord (D : Label → Finset Role) (roles : List Role) (labels : List Label) (word : List Bool) : Bool :=
  ((decodeEquation (Symbol Label) word).map (fun equation => Term.familyEquationB D roles labels equation.1 equation.2)).getD false

theorem checkWord_polyTime (D : Label → Finset Role) (roles : List Role) (labels : List Label) :
    ComputableInPolyTime (checkWord D roles labels) encBits encBool := by
  have hd := FiniteTermMachines.decodeEquation_polyTime (σ := Symbol Label)
  have he : ComputableInPolyTime (fun p : List Bool × (Tree (Label := Label) × Tree (Label := Label)) =>
      Term.familyEquationB D roles labels p.2.1 p.2.2)
      (encPair encBits (encPair termEncoding termEncoding)) encBool := (equation_polyTime D roles labels).comp (snd _ _)
  exact (hd.optionMapWithInput (f := fun (_ : List Bool) equation =>
    Term.familyEquationB D roles labels equation.1 equation.2) he).optionGetDWithInput (const false)

omit [Fintype Role] in
theorem checkWord_iff (three : Fin 3 ↪ Role) (D : Label → Finset Role) (roles : List Role) (labels : List Label)
    (hroles : ∀ r, r ∈ roles) (hlabels : ∀ d, d ∈ labels) (heasy : FamilyEasy (fun d => (D d : Set Role)))
    (word : List Bool) : checkWord D roles labels word = true ↔ word ∈ PolicyCompleteness.Language (fun d => (D d : Set Role)) := by
  cases hd : decodeEquation (Symbol Label) word with
  | none =>
    simp only [checkWord, hd, Option.map_none, Option.getD_none, Bool.false_eq_true, false_iff]
    rintro ⟨equation, hw, _⟩
    have hp := decodeEquation_encodeEquation (σ := Symbol Label) equation
    rw [hw, hd] at hp
    contradiction
  | some equation =>
    simp only [checkWord, hd, Option.map_some, Option.getD_some]
    constructor
    · intro he
      exact ⟨equation, encodeEquation_of_decodeEquation hd,
        (Term.familyEquationB_correct three D roles labels hroles hlabels heasy equation.1 equation.2).mp he⟩
    · rintro ⟨other, hw, he⟩
      have hp := decodeEquation_encodeEquation (σ := Symbol Label) other
      rw [hw, hd] at hp
      cases Option.some.inj hp
      exact (Term.familyEquationB_correct three D roles labels hroles hlabels heasy equation.1 equation.2).mpr he

theorem language_mem_P (three : Fin 3 ↪ Role) (D : Label → Finset Role)
    (heasy : FamilyEasy (fun d => (D d : Set Role))) :
    PolicyCompleteness.Language (fun d => (D d : Set Role)) ∈ Cslib.Complexity.P encBits := by
  let roles : List Role := Finset.univ.toList
  let labels : List Label := Finset.univ.toList
  refine ⟨checkWord D roles labels, checkWord_polyTime D roles labels, ?_⟩
  intro word
  exact (checkWord_iff three D roles labels (by simp [roles]) (by simp [labels]) heasy word).symm


theorem theory_mem_P (three : Fin 3 ↪ Role) (D : Label → Finset Role)
    (heasy : FamilyEasy (fun d => (D d : Set Role))) :
    PolicyCompleteness.Theory (fun d => (D d : Set Role)) ∈
      Cslib.Complexity.P PolicyReductionMachines.equationEncoding := by
  let roles : List Role := Finset.univ.toList
  let labels : List Label := Finset.univ.toList
  refine ⟨fun p => Term.familyEquationB D roles labels p.1 p.2, (equation_polyTime D roles labels).comp FiniteTermMachines.arguments_polyTime, ?_⟩
  intro equation
  exact (Term.familyEquationB_correct three D roles labels (by simp [roles]) (by simp [labels])
    heasy equation.1 equation.2).symm

/-- The complete fixed-family binary-language dichotomy, with actual native
machines on both branches and an independent passing-pattern criterion. -/
theorem language_dichotomy (three : Fin 3 ↪ Role) (D : Label → Finset Role) (code : Role ↪ ℕ) :
    (FamilyEasy (fun d => (D d : Set Role)) →
      PolicyCompleteness.Language (fun d => (D d : Set Role)) ∈ Cslib.Complexity.P encBits) ∧
    (¬FamilyEasy (fun d => (D d : Set Role)) →
      Cslib.Complexity.coNPComplete encBits (PolicyCompleteness.Language (fun d => (D d : Set Role)))) :=
  ⟨language_mem_P three D, PolicyCompleteness.language_coNPComplete _ three code⟩
end KFOL.Complexity.PolicyTermFrontend
