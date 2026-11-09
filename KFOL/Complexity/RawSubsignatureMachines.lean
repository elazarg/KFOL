module
public import KFOL.Complexity.ResetChoiceMachines
public import KFOL.Complexity.FiniteFoldRuntime
public import KFOL.Reductions.RawSubsignature
@[expose] public section
namespace KFOL.Complexity.RawSubsignatureMachines
open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FiniteTermCode
variable {Role : Type} (selected : Finset (Raw.Operation Role))
abbrev Tree := Raw.Term selected ℕ
noncomputable abbrev termEncoding := FiniteTermMachines.termEncoding (σ := Raw.Symbol selected)
noncomputable abbrev equationEncoding := FiniteTermMachines.equationEncoding (σ := Raw.Symbol selected)

private noncomputable def header (operations : Bool → {op // op ∈ selected}) (sign : Bool) : ℕ :=
  1 + (Words.delimit (encodeOperation (Raw.Symbol selected) ⟨2,.binary (operations sign)⟩)).length
private noncomputable def bound (operations : Bool → {op // op ∈ selected}) : ℕ :=
  1 + max (header selected operations false) (header selected operations true)
private theorem header_le (operations : Bool → {op // op ∈ selected}) (sign : Bool) :
    header selected operations sign ≤ bound selected operations := by
  cases sign <;> simp only [bound] <;> omega

private theorem encode_length (operations : Bool → {op // op ∈ selected}) (tree : RawPair.Term ℕ) :
    (termEncoding selected (Raw.Term.ofRawPair operations tree)).length ≤
      bound selected operations * (RawPairMachines.termEncoding tree).length := by
  have hc : 1 ≤ bound selected operations := by simp [bound]
  induction tree with
  | var j =>
    change (RawPairMachines.termEncoding (.var j)).length ≤ _
    nlinarith
  | @func n symbol children ih =>
    cases symbol with
    | binary sign =>
      have hh := header_le selected operations sign
      have hs : 1 ≤ RawPairMachines.header sign := by simp [RawPairMachines.header]
      have hmul := Nat.mul_le_mul_left (bound selected operations) hs
      have h0 := ih 0
      have h1 := ih 1
      change (encode (Raw.Symbol selected) (Raw.Term.ofRawPair operations (.func (.binary sign) children))).length ≤
        bound selected operations * (encode RawPair.Symbol (.func (.binary sign) children)).length
      simp only [Raw.Term.ofRawPair, encode_func, List.ofFn_succ, List.ofFn_zero, List.flatten_cons,
        List.flatten_nil, List.append_nil, List.length_cons, List.length_append]
      change (encode (Raw.Symbol selected) (Raw.Term.ofRawPair operations (children 0))).length ≤
        bound selected operations * (encode RawPair.Symbol (children 0)).length at h0
      change (encode (Raw.Symbol selected) (Raw.Term.ofRawPair operations (children 1))).length ≤
        bound selected operations * (encode RawPair.Symbol (children 1)).length at h1
      change (Words.delimit (encodeOperation (Raw.Symbol selected) ⟨2,.binary (operations sign)⟩)).length +
        ((encode (Raw.Symbol selected) (Raw.Term.ofRawPair operations (children 0))).length +
         (encode (Raw.Symbol selected) (Raw.Term.ofRawPair operations (children 1))).length) + 1 ≤
        bound selected operations * ((Words.delimit (encodeOperation RawPair.Symbol ⟨2,.binary sign⟩)).length +
         ((encode RawPair.Symbol (children 0)).length + (encode RawPair.Symbol (children 1)).length) + 1)
      unfold header at hh
      unfold RawPairMachines.header at hmul
      nlinarith

private def leaf (_ : Unit) (j : ℕ) : Tree selected := .var j
private noncomputable def node (operations : Bool → {op // op ∈ selected}) (_ : Unit)
    (operation : Operation RawPair.Symbol) (children : List (Tree selected)) : Tree selected :=
  match operation with
  | ⟨_, .binary sign⟩ => FiniteTermMachines.construct ⟨2,Raw.Symbol.binary (operations sign)⟩ children

private theorem fold_map (operations : Bool → {op // op ∈ selected}) (tree : RawPair.Term ℕ) :
    FiniteFoldMachine.fold (leaf selected) (node selected operations) () tree = Raw.Term.ofRawPair operations tree := by
  induction tree with
  | var => rfl
  | @func n symbol children ih =>
    cases symbol with
    | binary sign =>
      simp only [FiniteFoldMachine.fold, node]
      change FiniteTermMachines.construct ⟨2,Raw.Symbol.binary (operations sign)⟩
        (List.ofFn (fun i => FiniteFoldMachine.fold (leaf selected) (node selected operations) () (children i))) = _
      rw [FiniteTermMachines.construct_ofFn]
      simp only [Raw.Term.ofRawPair]
      congr 1
      funext i
      exact ih i

private theorem node_polyTime (operations : Bool → {op // op ∈ selected}) : ComputableInPolyTime
    (fun p : Unit × (Operation RawPair.Symbol × List (Tree selected)) => node selected operations p.1 p.2.1 p.2.2)
    (encPair encUnit (encPair (FiniteTermMachines.operationEncoding (σ := RawPair.Symbol)) (encList (termEncoding selected)))) (termEncoding selected) := by
  let input := encPair encUnit (encPair (FiniteTermMachines.operationEncoding (σ := RawPair.Symbol))
    (encList (termEncoding selected)))
  have hop : ComputableInPolyTime (fun p : Unit × (Operation RawPair.Symbol × List (Tree selected)) => p.2.1)
      input FiniteTermMachines.operationEncoding := by fun_prop
  have hchildren : ComputableInPolyTime (fun p : Unit × (Operation RawPair.Symbol × List (Tree selected)) => p.2.2)
      input (encList (termEncoding selected)) := by fun_prop
  apply hop.finite_cases (branch := fun operation p => node selected operations p.1 operation p.2.2)
  rintro ⟨n, operation⟩
  cases operation with
  | binary sign => exact (FiniteTermMachines.construct_fixed_polyTime ⟨2,Raw.Symbol.binary (operations sign)⟩).comp hchildren

/-- Native syntax embedding preserves every source node and variable. Its
output size is linear in the complete original binary source encoding. -/
theorem ofRawPair_polyTime (operations : Bool → {op // op ∈ selected}) : ComputableInPolyTime
    (Raw.Term.ofRawPair operations) RawPairMachines.termEncoding (termEncoding selected) := by
  have hf := FiniteFoldMachine.fold_polyTime (contextEncoding := encUnit) (valueEncoding := termEncoding selected)
    (leaf selected) (node selected operations) (FiniteTermMachines.var_polyTime.comp (snd encUnit encNat))
    (node_polyTime selected operations) (bound selected operations) 1 (by
      intro context tree
      cases context
      rw [fold_map]
      have h := encode_length selected operations tree
      simp only [pow_one]
      apply h.trans
      apply Nat.mul_le_mul_left
      change (encode RawPair.Symbol tree).length ≤ _
      omega) (.var 0)
  have h := hf.comp ((const ()).prod (id' (encIn := RawPairMachines.termEncoding)))
  convert h using 1
  funext tree
  exact (fold_map selected operations tree).symm


theorem mapEquation_polyTime (operations : Bool → {op // op ∈ selected}) : ComputableInPolyTime
    (fun equation : RawPair.Term ℕ × RawPair.Term ℕ =>
      (Raw.Term.ofRawPair operations equation.1, Raw.Term.ofRawPair operations equation.2))
    RawPairMachines.equationEncoding (equationEncoding selected) := by
  have hl := (ofRawPair_polyTime selected operations).comp
    (fst RawPairMachines.termEncoding RawPairMachines.termEncoding)
  have hr := (ofRawPair_polyTime selected operations).comp
    (snd RawPairMachines.termEncoding RawPairMachines.termEncoding)
  exact FiniteTermMachines.equationRecode_polyTime.comp
    ((hl.prod hr).comp (FiniteTermMachines.arguments_polyTime (σ := RawPair.Symbol)))

theorem choiceUnion_polyTime (a : Role) (ha : Raw.Operation.choice a ∈ selected) (hu : Raw.Operation.union ∈ selected) :
    ComputableInPolyTime (Raw.Reduction.choiceUnion selected a ha hu) RawPairMachines.cnfEncoding (equationEncoding selected) :=
  (mapEquation_polyTime selected (Raw.Term.pairOperations (.choice a) .union ha hu)).comp RawPairMachines.reduction_polyTime

theorem twoChoices_polyTime (a b : Role) (ha : Raw.Operation.choice a ∈ selected) (hb : Raw.Operation.choice b ∈ selected) :
    ComputableInPolyTime (Raw.Reduction.twoChoices selected a b ha hb) RawPairMachines.cnfEncoding (equationEncoding selected) :=
  (mapEquation_polyTime selected (Raw.Term.pairOperations (.choice a) (.choice b) ha hb)).comp RawPairMachines.twoOwnerReduction_polyTime

theorem resetChoice_polyTime (a : Role) (ha : Raw.Operation.choice a ∈ selected) (hr : Raw.Operation.reset ∈ selected) :
    ComputableInPolyTime (Raw.Reduction.resetChoice selected a ha hr) RawPairMachines.cnfEncoding (equationEncoding selected) :=
  (mapEquation_polyTime selected (Raw.Term.pairOperations .reset (.choice a) hr ha)).comp ResetChoiceMachines.reduction_polyTime

private theorem ofRawPair_translate (hr : Raw.Operation.reset ∈ selected) (hu : Raw.Operation.union ∈ selected)
    (tree : ResetUnion.Term ℕ) :
    Raw.Term.ofRawPair (Raw.Term.pairOperations .reset .union hr hu) (Reductions.ResetChoice.translate tree) =
      Raw.Term.ofResetUnion hr hu tree := by
  induction tree with
  | var => rfl
  | @func n symbol children ih =>
    cases symbol <;>
      simp only [Reductions.ResetChoice.translate, Raw.Term.ofRawPair, Raw.Term.ofResetUnion,
        RawPair.Term.node, Raw.Term.pairOperations]
    all_goals
      congr 1
      funext i
      have hi : i = 0 ∨ i = 1 := by omega
      rcases hi with rfl | rfl <;> simpa using ih _

theorem resetUnion_polyTime (hr : Raw.Operation.reset ∈ selected) (hu : Raw.Operation.union ∈ selected) :
    ComputableInPolyTime (Raw.Reduction.resetUnion selected hr hu) RawPairMachines.cnfEncoding (equationEncoding selected) := by
  have h := (mapEquation_polyTime selected (Raw.Term.pairOperations .reset .union hr hu)).comp
    ResetChoiceMachines.translated_reduction_polyTime
  convert h using 1
  funext formula
  exact Prod.ext (ofRawPair_translate selected hr hu _).symm (ofRawPair_translate selected hr hu _).symm
end KFOL.Complexity.RawSubsignatureMachines
