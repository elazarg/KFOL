module

public import KFOL.Complexity.OwnerObservationCompiler
public import KFOL.Complexity.FiniteSignatureVerifier
public import KFOL.Definitions.Reductions
public import Complexity.Computability.Complexity.Classes.NP.Closure
public import Complexity.Computability.Complexity.Reduction

/-! # Original owner-signature word languages and legal-owner checking -/
@[expose] public section
namespace KFOL.Complexity.OwnerLanguage
open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FiniteTermCode
variable {Role : Type} [Fintype Role] [DecidableEq Role]
noncomputable abbrev termEncoding := OwnerTermMachines.termEncoding (Role := Role)
noncomputable abbrev equationEncoding := FiniteTermMachines.equationEncoding (σ := Owner.Symbol Role)

def leaf (_ : Unit) (_ : ℕ) : Bool := true
def node (owners : Finset Role) (_ : Unit) (operation : Operation (Owner.Symbol Role))
    (children : List Bool) : Bool :=
  children.all id && match operation with
    | ⟨_,.reset⟩ => true
    | ⟨_,.guarded r⟩ => decide (r ∈ owners)

/-- A Boolean traversal rejects every occurrence of an unselected owner. -/
def ownersB (owners : Finset Role) (term : Owner.Term Role ℕ) : Bool :=
  FiniteFoldMachine.fold leaf (node owners) () term

omit [Fintype Role] in
theorem ownersB_iff (owners : Finset Role) (term : Owner.Term Role ℕ) :
    ownersB owners term = true ↔ term.OwnersIn (fun r => r ∈ owners) := by
  induction term using Owner.Term.induction_owner with
  | var => simp [ownersB,FiniteFoldMachine.fold,leaf,Owner.Term.OwnersIn]
  | step s t hs ht =>
    simpa [ownersB,FiniteFoldMachine.fold,node,Owner.Term.step,Owner.Term.OwnersIn,List.ofFn_succ]
      using and_congr hs ht
  | guarded r x y z hx hy hz =>
    simp [ownersB,FiniteFoldMachine.fold,node,Owner.Term.guarded,Owner.Term.OwnersIn,
      List.ofFn_succ] at hx hy hz ⊢
    tauto

theorem ownersB_polyTime (owners : Finset Role) : ComputableInPolyTime
    (ownersB owners) termEncoding encBool := by
  have hl : ComputableInPolyTime (fun p : Unit × ℕ => leaf p.1 p.2)
      (encPair encUnit encNat) encBool := const true
  let input := encPair encUnit (encPair
    (FiniteTermMachines.operationEncoding (σ := Owner.Symbol Role)) (encList encBool))
  have hop : ComputableInPolyTime (fun p : Unit × (Operation (Owner.Symbol Role) × List Bool) => p.2.1)
      input FiniteTermMachines.operationEncoding := by fun_prop
  have hc : ComputableInPolyTime (fun p : Unit × (Operation (Owner.Symbol Role) × List Bool) => p.2.2)
      input (encList encBool) := by fun_prop
  have ha := allWithInput (test := fun (_ : Unit × (Operation (Owner.Symbol Role) × List Bool)) b => b)
    hc (snd input encBool)
  have hn : ComputableInPolyTime
      (fun p : Unit × (Operation (Owner.Symbol Role) × List Bool) => node owners p.1 p.2.1 p.2.2)
      input encBool := by
    apply hop.finite_cases (branch := fun operation p => node owners p.1 operation p.2.2)
    rintro ⟨arity,operation⟩
    cases operation with
    | reset => exact bool_and' ha (const true)
    | guarded r => exact bool_and' ha (const (decide (r ∈ owners)))
  have hf := FiniteFoldMachine.fold_polyTime (contextEncoding := encUnit) (valueEncoding := encBool)
    leaf (node owners) hl hn 1 0 (by intro context term; simp) false
  change ComputableInPolyTime
    (fun term : Equational.Term (Owner.Symbol Role) ℕ => FiniteFoldMachine.fold leaf (node owners) () term)
    FiniteTermMachines.termEncoding encBool
  exact hf.comp ((const ()).prod id')

noncomputable def checkWordWith (test : Owner.Term Role ℕ × Owner.Term Role ℕ → Bool)
    (word : List Bool) : Bool :=
  ((decodeEquation (Owner.Symbol Role) word).map test).getD false

omit [DecidableEq Role] in
theorem checkWordWith_polyTime (test : Owner.Term Role ℕ × Owner.Term Role ℕ → Bool)
    (runtime : ComputableInPolyTime test equationEncoding encBool) :
    ComputableInPolyTime (checkWordWith test) encBits encBool := by
  have ht := (runtime.comp (FiniteTermMachines.equationRecode_polyTime (σ := Owner.Symbol Role))).comp
    (snd encBits (encPair termEncoding termEncoding))
  exact ((FiniteTermMachines.decodeEquation_polyTime (σ := Owner.Symbol Role)).optionMapWithInput
    (f := fun (_ : List Bool) equation => test equation) ht).optionGetDWithInput (const false)

omit [DecidableEq Role] in
theorem checkWordWith_iff (predicate : Owner.Term Role ℕ × Owner.Term Role ℕ → Prop)
    (test : Owner.Term Role ℕ × Owner.Term Role ℕ → Bool)
    (correct : ∀ equation, test equation = true ↔ predicate equation) (word : List Bool) :
    checkWordWith test word = true ↔ ∃ equation,
      encodeEquation (Owner.Symbol Role) equation = word ∧ predicate equation := by
  cases hd : decodeEquation (Owner.Symbol Role) word with
  | none =>
    simp only [checkWordWith,hd,Option.map_none,Option.getD_none,Bool.false_eq_true,false_iff]
    rintro ⟨equation,he,_⟩
    have hp := decodeEquation_encodeEquation (σ := Owner.Symbol Role) equation
    rw [he,hd] at hp
    contradiction
  | some equation =>
    simp only [checkWordWith,hd,Option.map_some,Option.getD_some]
    constructor
    · intro ht
      exact ⟨equation,encodeEquation_of_decodeEquation hd,(correct equation).mp ht⟩
    · rintro ⟨other,he,valid⟩
      have hp := decodeEquation_encodeEquation (σ := Owner.Symbol Role) other
      rw [he,hd] at hp
      cases Option.some.inj hp
      exact (correct equation).mpr valid

def legalB (owners : Finset Role) (equation : Owner.Term Role ℕ × Owner.Term Role ℕ) : Bool :=
  ownersB owners equation.1 && ownersB owners equation.2

theorem legalB_polyTime (owners : Finset Role) : ComputableInPolyTime
    (legalB owners) equationEncoding encBool := by
  have ha := FiniteTermMachines.arguments_polyTime (σ := Owner.Symbol Role)
  exact bool_and' ((ownersB_polyTime owners).comp ((fst _ _).comp ha))
    ((ownersB_polyTime owners).comp ((snd _ _).comp ha))

theorem legal_language_mem_P (owners : Finset Role) :
    {word | ∃ equation : Owner.Term Role ℕ × Owner.Term Role ℕ,
      encodeEquation (Owner.Symbol Role) equation = word ∧
      equation.1.OwnersIn (fun r => r ∈ owners) ∧ equation.2.OwnersIn (fun r => r ∈ owners)} ∈
      Cslib.Complexity.P encBits :=
  ⟨checkWordWith (legalB owners),checkWordWith_polyTime _ (legalB_polyTime owners),fun word =>
    (checkWordWith_iff _ _ (fun equation => by simp [legalB,ownersB_iff]) word).symm⟩

/-- Any fixed finite relation on actual winner values has a coNP upper bound
on the selected-owner original-word language, including malformed-word rejection. -/
theorem language_mem_coNP (owners : Finset Role) (inhabitant : Role)
    (relation : WinnerSet Role → WinnerSet Role → Prop) :
    Owner.Language owners relation ∈ Cslib.Complexity.coNP encBits := by
  classical
  let : Fintype (WinnerSet Role) := Fintype.ofFinite _
  let : Nonempty (WinnerSet Role) := ⟨WinnerSet.singleton inhabitant⟩
  let : (Equational.language (Owner.Symbol Role)).Structure (WinnerSet Role) := Owner.structureOf
  have h := Cslib.Complexity.inter_mem_coNP
    (Cslib.Complexity.P_subset_coNP (legal_language_mem_P owners))
    (FiniteSignatureVerifier.language_mem_coNP (σ := Owner.Symbol Role) relation)
  convert h using 1
  ext word
  constructor
  · rintro ⟨equation,he,hl,hr,hvalid⟩
    exact ⟨⟨equation,he,hl,hr⟩,⟨equation,he,hvalid⟩⟩
  · rintro ⟨⟨left,hl,hl₁,hl₂⟩,⟨right,hr,hvalid⟩⟩
    have he : left = right := encodeEquation_injective (hl.trans hr.symm)
    subst right
    exact ⟨left,hl,hl₁,hl₂,hvalid⟩

end KFOL.Complexity.OwnerLanguage
