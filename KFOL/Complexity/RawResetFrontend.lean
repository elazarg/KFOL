module

public import KFOL.Complexity.RawSmallSignature
public import KFOL.Complexity.TermMachine
public import KFOL.Complexity.ResetEquality

/-! # Node-for-node native transport of the complete reset checker -/
@[expose] public section
namespace KFOL.Complexity.RawResetFrontend
open Turing.MultiTapeTM ComputableInPolyTime
variable {Role : Type} (selected : Finset (Raw.Operation Role))

private def leaf (_ : Unit) (j : ℕ) : Reset.Term ℕ := .var j
private def node (_ : Unit) (_ : FiniteTermCode.Operation (Raw.Symbol selected))
    (children : List (Reset.Term ℕ)) : Reset.Term ℕ :=
  Reset.Term.step (children.getD 0 (.var 0)) (children.getD 1 (.var 0))

private theorem toReset_node (hselected : selected = {.reset})
    (operation : {op // op ∈ selected}) (args : Fin 2 → Raw.Term selected ℕ) :
    Raw.Term.toReset hselected (.func (.binary operation) args) =
      Reset.Term.step ((args 0).toReset hselected) ((args 1).toReset hselected) := by
  dsimp only [Raw.Term.toReset,Reset.Term.step]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem fold_toReset (hselected : selected = {.reset}) (term : Raw.Term selected ℕ) :
    FiniteFoldMachine.fold leaf (node selected) () term = term.toReset hselected := by
  induction term with
  | var => rfl
  | @func n symbol args ih =>
    cases symbol
    rw [toReset_node selected hselected]
    simp only [FiniteFoldMachine.fold,node,List.ofFn_succ,List.ofFn_zero,List.getD_cons_zero,
      List.getD_cons_succ,ih]
    rfl

private theorem code_length (hselected : selected = {.reset}) (term : Raw.Term selected ℕ) :
    (Algorithms.TermCode.encode (term.toReset hselected)).length ≤
      (FiniteTermCode.encode (Raw.Symbol selected) term).length := by
  induction term with
  | var => rfl
  | @func n symbol args ih =>
    cases symbol
    have h0 := ih 0
    have h1 := ih 1
    rw [toReset_node selected hselected]
    simp only [FiniteTermCode.encode_func,Algorithms.TermCode.encode_step,
      List.length_cons,List.length_append,List.ofFn_succ,List.ofFn_zero,List.flatten_cons,List.flatten_nil,
      List.append_nil]
    simp only [show (Fin.succ (0 : Fin 1) : Fin 2) = 1 from rfl]
    omega

/-- The native translation executes the original binary tree once; its exact
output syntax is the already checked reset syntax, with no extra certificate. -/
theorem toReset_polyTime (hselected : selected = {.reset}) :
    ComputableInPolyTime (Raw.Term.toReset (Var := ℕ) hselected)
      (RawSmallSignature.termEncoding selected) TermMachine.termEncoding := by
  have hl : ComputableInPolyTime (fun p : Unit × ℕ => leaf p.1 p.2)
      (encPair encUnit encNat) TermMachine.termEncoding := TermMachine.var_polyTime.comp (snd _ _)
  have hc : ComputableInPolyTime
      (fun p : Unit × (FiniteTermCode.Operation (Raw.Symbol selected) × List (Reset.Term ℕ)) => p.2.2)
      (encPair encUnit (encPair FiniteTermMachines.operationEncoding (encList TermMachine.termEncoding)))
      (encList TermMachine.termEncoding) := by fun_prop
  have h0 := (listGetD (encA := TermMachine.termEncoding) (.var 0 : Reset.Term ℕ)).comp (hc.prod (const 0))
  have h1 := (listGetD (encA := TermMachine.termEncoding) (.var 0 : Reset.Term ℕ)).comp (hc.prod (const 1))
  have hn : ComputableInPolyTime
      (fun p : Unit × (FiniteTermCode.Operation (Raw.Symbol selected) × List (Reset.Term ℕ)) =>
        node selected p.1 p.2.1 p.2.2)
      (encPair encUnit (encPair FiniteTermMachines.operationEncoding (encList TermMachine.termEncoding)))
      TermMachine.termEncoding := TermMachine.node_polyTime.comp (h0.prod h1)
  have hf := FiniteFoldMachine.fold_polyTime (contextEncoding := encUnit)
    (valueEncoding := TermMachine.termEncoding) leaf (node selected) hl hn 1 1 (by
      intro context term
      cases context
      rw [fold_toReset selected hselected]
      have h := code_length selected hselected term
      simp only [Nat.pow_one,Nat.one_mul]
      exact h.trans (by omega)) (.var 0)
  have hp : ComputableInPolyTime (fun term : Raw.Term selected ℕ => ((),term))
      (RawSmallSignature.termEncoding selected)
      (encPair encUnit (RawSmallSignature.termEncoding selected)) := (const ()).prod id'
  convert hf.comp hp using 1
  funext term
  exact (fold_toReset selected hselected term).symm

/-- Run the already certified independent reset equality algorithm on the
actual translated originals. No canonical-table input promise is needed. -/
def check (hselected : selected = {.reset}) (equation : Raw.Term selected ℕ × Raw.Term selected ℕ) : Bool :=
  Algorithms.ResetEquation.check (equation.1.toReset hselected) (equation.2.toReset hselected)

theorem check_polyTime (hselected : selected = {.reset}) :
    ComputableInPolyTime (check selected hselected) (RawSmallSignature.equationEncoding selected) encBool := by
  have ha := FiniteTermMachines.arguments_polyTime (σ := Raw.Symbol selected)
  have hl := (toReset_polyTime selected hselected).comp ((fst _ _).comp ha)
  have hr := (toReset_polyTime selected hselected).comp ((snd _ _).comp ha)
  exact ResetEquality.check_polyTime.comp (hl.prod hr)

theorem check_iff (three : Fin 3 ↪ Role) (hselected : selected = {.reset})
    (equation : Raw.Term selected ℕ × Raw.Term selected ℕ) :
    check selected hselected equation = true ↔ Raw.Valid selected equation := by
  rw [check,Algorithms.ResetEquation.check_iff_eval three]
  simp only [Raw.Term.eval_toReset]
  rfl

theorem language_mem_P (three : Fin 3 ↪ Role) (hselected : selected = {.reset}) :
    Raw.Language selected ∈ Cslib.Complexity.P encBits :=
  RawSmallSignature.language_mem_P_of_checker selected (check selected hselected)
    (check_polyTime selected hselected) (check_iff selected three hselected)

/-- The whole positive branch of the raw signature dichotomy: the empty
signature and each possible singleton use concrete complete native checkers. -/
theorem small_signature_language_mem_P (three : Fin 3 ↪ Role) (small : selected.card ≤ 1) :
    Raw.Language selected ∈ Cslib.Complexity.P encBits := by
  rcases (Raw.small_signature_cases selected).mp small with empty | choice | union | reset
  · exact RawSmallSignature.support_language_mem_P selected three (Or.inl empty)
  · exact RawSmallSignature.support_language_mem_P selected three (Or.inr (Or.inl choice))
  · exact RawSmallSignature.support_language_mem_P selected three (Or.inr (Or.inr union))
  · exact language_mem_P selected three reset

end KFOL.Complexity.RawResetFrontend
