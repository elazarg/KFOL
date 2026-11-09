module

public import KFOL.Reductions.RawSubsignature
public import Complexity.Computability.Complexity.Classes.P
public import KFOL.Complexity.Language
public import KFOL.Complexity.FiniteTermVariables
public import KFOL.Complexity.FiniteTermDecoding

/-! # Native sparse-support checking for raw singleton semilattice signatures -/
@[expose] public section
namespace KFOL.Complexity.RawSmallSignature
open Turing.MultiTapeTM ComputableInPolyTime

/-- Lists are compared as sets, so repeated occurrences need no sorting. -/
def subsetB (p : List ℕ × List ℕ) : Bool :=
  p.1.all (fun x => p.2.any (fun y => decide (x = y)))

theorem subsetB_polyTime : ComputableInPolyTime subsetB
    (encPair (encList encNat) (encList encNat)) encBool := by
  have he : ComputableInPolyTime
      (fun p : ((List ℕ × List ℕ) × ℕ) × ℕ => decide (p.1.2 = p.2))
      (encPair (encPair (encPair (encList encNat) (encList encNat)) encNat) encNat) encBool := by
    apply decide_eq' <;> fun_prop
  have hi := anyWithInput (test := fun p : (List ℕ × List ℕ) × ℕ => fun y => decide (p.2 = y))
    (by fun_prop : ComputableInPolyTime (fun p : (List ℕ × List ℕ) × ℕ => p.1.2)
      (encPair (encPair (encList encNat) (encList encNat)) encNat) (encList encNat)) he
  exact allWithInput (test := fun p : List ℕ × List ℕ => fun x => p.2.any (fun y => decide (x = y)))
    (fst _ _) hi

theorem subsetB_iff (xs ys : List ℕ) : subsetB (xs,ys) = true ↔ ∀ x ∈ xs, x ∈ ys := by
  simp [subsetB,List.all_eq_true,List.any_eq_true]

variable {Role : Type} (selected : Finset (Raw.Operation Role))

noncomputable abbrev termEncoding := FiniteTermMachines.termEncoding (σ := Raw.Symbol selected)
noncomputable abbrev equationEncoding := FiniteTermMachines.equationEncoding (σ := Raw.Symbol selected)

/-- The generic original traversal has exactly the independently defined raw
term support, without inspecting numeric variable-label maxima. -/
theorem names_support (term : Raw.Term selected ℕ) :
    (FiniteTermVariables.names term).toFinset = term.support := by
  induction term with
  | var j => simp [FiniteTermVariables.names,Raw.Term.support]
  | @func n symbol args ih =>
    cases symbol
    simp [FiniteTermVariables.names,Raw.Term.support,List.ofFn_succ,ih]

/-- The actual native checker compares only original sparse variable names. -/
def check (equation : Raw.Term selected ℕ × Raw.Term selected ℕ) : Bool :=
  let left := FiniteTermVariables.names equation.1
  let right := FiniteTermVariables.names equation.2
  subsetB (left,right) && subsetB (right,left)

theorem check_polyTime : ComputableInPolyTime (check selected) (equationEncoding selected) encBool := by
  have ha := FiniteTermMachines.arguments_polyTime (σ := Raw.Symbol selected)
  have hl := FiniteTermVariables.names_polyTime.comp ((fst _ _).comp ha)
  have hr := FiniteTermVariables.names_polyTime.comp ((snd _ _).comp ha)
  exact bool_and' (subsetB_polyTime.comp (hl.prod hr)) (subsetB_polyTime.comp (hr.prod hl))

theorem check_iff_support (s t : Raw.Term selected ℕ) :
    check selected (s,t) = true ↔ s.support = t.support := by
  simp only [check,Bool.and_eq_true,subsetB_iff]
  rw [← names_support selected s,← names_support selected t]
  exact ⟨fun h => Finset.ext (fun i => by simpa only [List.mem_toFinset] using ⟨h.1 i,h.2 i⟩),
    fun h => ⟨fun i hi => List.mem_toFinset.mp (h ▸ List.mem_toFinset.mpr hi),
      fun i hi => List.mem_toFinset.mp (h.symm ▸ List.mem_toFinset.mpr hi)⟩⟩

/-- The complete word wrapper rejects every failed original-tree decode. -/
noncomputable def checkWordWith
    (test : Raw.Term selected ℕ × Raw.Term selected ℕ → Bool) (word : List Bool) : Bool :=
  ((FiniteTermCode.decodeEquation (Raw.Symbol selected) word).map test).getD false

theorem checkWordWith_polyTime (test : Raw.Term selected ℕ × Raw.Term selected ℕ → Bool)
    (runtime : ComputableInPolyTime test (equationEncoding selected) encBool) :
    ComputableInPolyTime (checkWordWith selected test) encBits encBool := by
  have htest : ComputableInPolyTime
      (fun p : List Bool × (Raw.Term selected ℕ × Raw.Term selected ℕ) => test p.2)
      (encPair encBits (encPair (termEncoding selected) (termEncoding selected))) encBool :=
    (runtime.comp (FiniteTermMachines.equationRecode_polyTime (σ := Raw.Symbol selected))).comp (snd _ _)
  exact ((FiniteTermMachines.decodeEquation_polyTime (σ := Raw.Symbol selected)).optionMapWithInput
    (f := fun (_ : List Bool) equation => test equation) htest).optionGetDWithInput (const false)

theorem checkWordWith_iff (test : Raw.Term selected ℕ × Raw.Term selected ℕ → Bool)
    (correct : ∀ equation, test equation = true ↔ Raw.Valid selected equation) (word : List Bool) :
    checkWordWith selected test word = true ↔ word ∈ Raw.Language selected := by
  cases hd : FiniteTermCode.decodeEquation (Raw.Symbol selected) word with
  | none =>
    simp only [checkWordWith,hd,Option.map_none,Option.getD_none,Bool.false_eq_true,false_iff]
    rintro ⟨equation,he,_⟩
    have hp := FiniteTermCode.decodeEquation_encodeEquation (σ := Raw.Symbol selected) equation
    rw [he,hd] at hp
    contradiction
  | some equation =>
    simp only [checkWordWith,hd,Option.map_some,Option.getD_some]
    constructor
    · intro ht
      exact ⟨equation,FiniteTermCode.encodeEquation_of_decodeEquation hd,(correct equation).mp ht⟩
    · rintro ⟨other,he,valid⟩
      have hp := FiniteTermCode.decodeEquation_encodeEquation (σ := Raw.Symbol selected) other
      rw [he,hd] at hp
      cases Option.some.inj hp
      exact (correct equation).mpr valid

theorem language_mem_P_of_checker (test : Raw.Term selected ℕ × Raw.Term selected ℕ → Bool)
    (runtime : ComputableInPolyTime test (equationEncoding selected) encBool)
    (correct : ∀ equation, test equation = true ↔ Raw.Valid selected equation) :
    Raw.Language selected ∈ Cslib.Complexity.P encBits :=
  ⟨checkWordWith selected test,checkWordWith_polyTime selected test runtime,
    fun word => (checkWordWith_iff selected test correct word).symm⟩

/-- Empty, one-choice and union-only signatures have exactly the support
criterion and an actual native original-word polynomial checker. -/
theorem support_language_mem_P (three : Fin 3 ↪ Role)
    (easyCases : selected = ∅ ∨ (∃ r : Role, selected = {.choice r}) ∨ selected = {.union}) :
    Raw.Language selected ∈ Cslib.Complexity.P encBits := by
  apply language_mem_P_of_checker selected (check selected) (check_polyTime selected)
  rintro ⟨s,t⟩
  rcases easyCases with he | ⟨r,he⟩ | he
  · obtain ⟨i,rfl⟩ := Raw.Term.exists_var_of_empty he s
    obtain ⟨j,rfl⟩ := Raw.Term.exists_var_of_empty he t
    rw [check_iff_support,Raw.valid_vars_iff (three 0) (three 1) (three.injective.ne (by decide))]
    simp [Raw.Term.support]
  · classical
    obtain ⟨other,hne⟩ : ∃ other : Role, r ≠ other := by
      by_cases hr : r = three 0
      · exact ⟨three 1,by simpa only [hr] using three.injective.ne (show (0 : Fin 3) ≠ 1 by decide)⟩
      · exact ⟨three 0,hr⟩
    exact (check_iff_support selected s t).trans (Raw.Term.support_eq_iff_valid_choice r other hne he s t)
  · exact (check_iff_support selected s t).trans
      (Raw.Term.support_eq_iff_valid_union (three 0) (three 1) (three.injective.ne (by decide)) he s t)

end KFOL.Complexity.RawSmallSignature
