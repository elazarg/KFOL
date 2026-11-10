module
public import KFOL.Complexity.FullInputMachines
public import KFOL.Complexity.FullTermFoldRuntime
public import KFOL.Complexity.FullHardnessPublic
@[expose] public section
namespace KFOL.Complexity.FullPublicReduction
open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FullTermCode

def check : Raw → Bool
  | .var _ => true
  | .func (.winner _) _ => true
  | .func (.choice _) children => check (children 0) && check (children 1)
  | .func (.rename _) _ => false
private def leaf (_ : Unit) (_ : ℕ) : Bool := true
private def node (_ : Unit) (operation : Operation) (children : List Bool) : Bool :=
  decide (FullTermMachines.operationKind operation ≠ 1) && children.all id
private theorem fold_check (tree : Raw) : FullTermFold.fold leaf node () tree = check tree := by
  induction tree with
  | var => rfl
  | @func n symbol children ih =>
    cases symbol <;> simp [FullTermFold.fold,node,check,ih,FullTermMachines.operationKind,List.ofFn_succ]
private theorem node_polyTime : ComputableInPolyTime
    (fun p : Unit × (Operation × List Bool) => node p.1 p.2.1 p.2.2)
    (encPair encUnit (encPair FullTermMachines.operationEncoding (encList encBool))) encBool := by
  let input := encPair encUnit (encPair FullTermMachines.operationEncoding (encList encBool))
  have hop : ComputableInPolyTime (fun p : Unit × (Operation × List Bool) => p.2.1) input FullTermMachines.operationEncoding := by fun_prop
  have hc : ComputableInPolyTime (fun p : Unit × (Operation × List Bool) => p.2.2) input (encList encBool) := by fun_prop
  have hall := allWithInput (test := fun (_ : Unit × (Operation × List Bool)) b => b) hc (snd input encBool)
  have hne : ComputableInPolyTime
      (fun p : Unit × (Operation × List Bool) =>
        decide (FullTermMachines.operationKind p.2.1 ≠ 1)) input encBool := by
    simpa only [Function.comp_def, decide_not] using
      bool_not.comp ((FullTermMachines.operationKind_polyTime.comp hop).decide_eq' (const (1 : Fin 3)))
  exact bool_and' hne hall

theorem check_polyTime : ComputableInPolyTime check FullTermMachines.termEncoding encBool := by
  have hf := FullTermFold.fold_polyTime (contextEncoding := encUnit) (valueEncoding := encBool)
    leaf node (const true) node_polyTime 1 0 (by intros; simp [encBool_apply]) false
  have h := hf.comp ((const ()).prod (id' (encIn := FullTermMachines.termEncoding)))
  convert h using 1
  funext tree
  exact (fold_check tree).symm

theorem check_view_iff {K : ℕ} (term : KFOL.Term (Fin K) ℕ) : check (view term) = true ↔ term.IsPublic := by
  induction term <;> simp_all [view,check,KFOL.Term.IsPublic]

def wordCheck (word : List Bool) : Bool :=
  (FullInputMachines.decodeInput word).elim false (fun input => check input.2.1 && check input.2.2)

theorem wordCheck_polyTime : ComputableInPolyTime wordCheck encBits encBool := by
  let input := encPair encBits FullInputMachines.inputEncoding
  have hl : ComputableInPolyTime (fun p : List Bool × FullInputMachines.Input => p.2.2.1)
      input FullTermMachines.termEncoding := by fun_prop
  have hr : ComputableInPolyTime (fun p : List Bool × FullInputMachines.Input => p.2.2.2)
      input FullTermMachines.termEncoding := by fun_prop
  exact FullInputMachines.decodeInput_polyTime.optionElimWithInput
    (body := fun (_ : List Bool) (input : FullInputMachines.Input) => check input.2.1 && check input.2.2)
    (const false) (bool_and' (check_polyTime.comp hl) (check_polyTime.comp hr))

def reduce (word : List Bool) : List Bool := if wordCheck word then word else []
theorem reduce_polyTime : ComputableInPolyTime reduce encBits encBits := wordCheck_polyTime.ite id' (const [])

private theorem decode_original (input : EquationInput) :
    FullInputMachines.decodeInput (encodeEquationInput input) = some (input.1,(view input.2.1,view input.2.2)) := by
  let raw : FullInputMachines.Input := (input.1,(view input.2.1,view input.2.2))
  have hcode : FullInputMachines.encodeRawInput raw = encodeEquationInput input := rfl
  rw [← hcode]
  exact FullInputMachines.decodeInput_encodeRawInput raw

private theorem empty_not_full : [] ∉ FullLanguage := by
  rintro ⟨input,_,hcode,_⟩
  have h := decode_original input
  rw [hcode] at h
  contradiction

theorem reduce_correct (word : List Bool) : word ∈ PublicLanguage ↔ reduce word ∈ FullLanguage := by
  constructor
  · rintro ⟨input,hK,hcode,hleft,hright,hvalid⟩
    have hs : wordCheck word = true := by
      rw [← hcode]
      simp only [wordCheck,decode_original,Option.elim_some,Bool.and_eq_true,check_view_iff]
      exact ⟨hleft,hright⟩
    rw [reduce,ite_eq_left hs]
    exact ⟨input,hK,hcode,hvalid⟩
  · intro h
    by_cases hs : wordCheck word = true
    · rw [reduce,ite_eq_left hs] at h
      obtain ⟨input,hK,hcode,hvalid⟩ := h
      have hc : check (view input.2.1) = true ∧ check (view input.2.2) = true := by
        rw [← hcode] at hs
        simpa only [wordCheck,decode_original,Option.elim_some,Bool.and_eq_true] using hs
      exact ⟨input,hK,hcode,(check_view_iff _).mp hc.1,(check_view_iff _).mp hc.2,hvalid⟩
    · rw [reduce,ite_eq_right hs] at h
      exact False.elim (empty_not_full h)
end KFOL.Complexity.FullPublicReduction
