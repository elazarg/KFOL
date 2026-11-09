module
public import KFOL.Complexity.FiniteTermDecoding
public import KFOL.Complexity.ResetUnionReduction
public import KFOL.Reductions.RawPairs
@[expose] public section
namespace KFOL.Complexity.RawPairMachines
open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FiniteTermCode KFOL.Reductions

def operationEquiv : Operation KFOL.RawPair.Symbol ≃ Bool where
  toFun operation := match operation with | ⟨_, .binary sign⟩ => sign
  invFun sign := ⟨2, .binary sign⟩
  left_inv operation := by cases operation with | mk n symbol => cases symbol; rfl
  right_inv _ := rfl
noncomputable instance operationFintype : Fintype (Operation KFOL.RawPair.Symbol) :=
  Fintype.ofEquiv Bool operationEquiv.symm
abbrev Tree := KFOL.RawPair.Term ℕ
noncomputable abbrev termEncoding := FiniteTermMachines.termEncoding (σ := KFOL.RawPair.Symbol)
noncomputable abbrev equationEncoding := FiniteTermMachines.equationEncoding (σ := KFOL.RawPair.Symbol)
abbrev literalEncoding := ResetUnionReduction.literalEncoding
abbrev clauseEncoding := ResetUnionReduction.clauseEncoding
abbrev cnfEncoding := ResetUnionReduction.cnfEncoding

theorem var_polyTime : ComputableInPolyTime (fun j : ℕ => (.var j : Tree)) encNat termEncoding :=
  FiniteTermMachines.var_polyTime

theorem node_polyTime : ComputableInPolyTime
    (fun p : Bool × (Tree × Tree) => KFOL.RawPair.Term.node p.1 p.2.1 p.2.2)
    (encPair encBool (encPair termEncoding termEncoding)) termEncoding := by
  let input := encPair encBool (encPair termEncoding termEncoding)
  have hx : ComputableInPolyTime (fun p : Bool × (Tree × Tree) => p.2.1) input termEncoding := by fun_prop
  have hy : ComputableInPolyTime (fun p : Bool × (Tree × Tree) => p.2.2) input termEncoding := by fun_prop
  have hop := (ComputableInPolyTime.of_finite (fun sign : Bool =>
      (⟨2, KFOL.RawPair.Symbol.binary sign⟩ : Operation KFOL.RawPair.Symbol))
      (encIn := encBool) (encOut := FiniteTermMachines.operationEncoding )).comp (fst encBool (encPair termEncoding termEncoding))
  have h := FiniteTermMachines.construct_polyTime.comp (hop.prod (cons' hx (cons' hy (const []))))
  convert h using 1
  funext p
  unfold KFOL.RawPair.Term.node FiniteTermMachines.construct
  congr 1
  funext i
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl <;> simp

noncomputable def header (sign : Bool) : ℕ :=
  1 + (Words.delimit (encodeOperation KFOL.RawPair.Symbol ⟨2, .binary sign⟩)).length

theorem node_length (sign : Bool) (s t : Tree) :
    (termEncoding (KFOL.RawPair.Term.node sign s t)).length =
      (termEncoding s).length + (termEncoding t).length + header sign := by
  simp [termEncoding, FiniteTermMachines.termEncoding, KFOL.RawPair.Term.node,
    encode_func, List.ofFn_succ, header, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem fold_polyTime (sign : Bool) : ComputableInPolyTime
    (fun p : List Tree × Tree => KFOL.RawPair.Term.fold sign p.1 p.2)
    (encPair (encList termEncoding) termEncoding) termEncoding := by
  let input := encPair (encList termEncoding) termEncoding
  have hl := fst (encList termEncoding) termEncoding
  have hr := (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.listReverse termEncoding)).comp hl
  have hs : ComputableInPolyTime (fun p : ((List Tree × Tree) × Tree) × Tree => p.1.2)
      (encPair (encPair input termEncoding) termEncoding) termEncoding := by fun_prop
  have ht := snd (encPair input termEncoding) termEncoding
  have hstep := node_polyTime.comp ((const sign).prod (ht.prod hs))
  have hg := hl.polyBounded_length.add (PolyBounded.const (header sign))
  have h := foldlWithInput_of_bounded_growth
    (list := fun p : List Tree × Tree => p.1.reverse) (init := fun p => p.2)
    (step := fun _ state term => KFOL.RawPair.Term.node sign term state)
    (snd (encList termEncoding) termEncoding) ⟨hr, hstep, inferInstance, inferInstance⟩
    (growth := fun p => (encList termEncoding p.1).length + header sign) ⟨hg, ?_⟩
  · convert h using 1
    funext p
    rw [List.foldl_reverse]
    rfl
  · intro p state term hterm
    have ht := SizedListEncoding.length_elem_le (encA := termEncoding)
      (encL := encList termEncoding) p.1 term (List.mem_reverse.mp hterm)
    have hn := node_length sign term state
    omega

theorem literalTerm_polyTime : ComputableInPolyTime RawPair.literalTerm literalEncoding termEncoding :=
  var_polyTime.comp ResetUnionReduction.literalName_polyTime

theorem rails_polyTime : ComputableInPolyTime RawPair.rails cnfEncoding (encList termEncoding) := by
  have hi := snd cnfEncoding encNat
  have hp := literalTerm_polyTime.comp (hi.prod (const true))
  have hn := literalTerm_polyTime.comp (hi.prod (const false))
  exact flatMapWithInput (f := fun (_ : CNF) j => [RawPair.literalTerm (j, true), RawPair.literalTerm (j, false)])
    ResetUnionReduction.support_polyTime (cons' hp (cons' hn (const [])))

theorem baseline_polyTime : ComputableInPolyTime RawPair.baseline cnfEncoding termEncoding :=
  (fold_polyTime false).comp (rails_polyTime.prod (const (RawPair.literalTerm (0, true))))

theorem branch_polyTime : ComputableInPolyTime RawPair.branch encNat termEncoding := by
  have hp := literalTerm_polyTime.comp ((id' (encIn := encNat)).prod (const true))
  have hn := literalTerm_polyTime.comp ((id' (encIn := encNat)).prod (const false))
  exact node_polyTime.comp ((const true).prod ((const (.var 0 : Tree)).prod
    (node_polyTime.comp ((const true).prod (hp.prod hn)))))

theorem right_polyTime : ComputableInPolyTime RawPair.right cnfEncoding termEncoding := by
  have hbranches := mapWithInput (f := fun (_ : CNF) j => RawPair.branch j)
    ResetUnionReduction.support_polyTime (branch_polyTime.comp (snd cnfEncoding encNat))
  exact (fold_polyTime false).comp (hbranches.prod baseline_polyTime)

theorem clause_polyTime : ComputableInPolyTime RawPair.clause clauseEncoding termEncoding := by
  have hrest := mapWithInput (f := fun (_ : Clause) literal => RawPair.literalTerm literal)
    (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.listTail literalEncoding)) (literalTerm_polyTime.comp (snd clauseEncoding literalEncoding))
  have hhead := literalTerm_polyTime.comp (headD (encA := literalEncoding) (encL := clauseEncoding) (0, true))
  have hnonempty := (fold_polyTime false).comp (hrest.prod hhead)
  have h := (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.listIsEmpty (encA := literalEncoding))).ite
    (const (.var 0 : Tree)) hnonempty
  convert h using 1
  funext clause
  cases clause <;> rfl

theorem left_polyTime : ComputableInPolyTime RawPair.left cnfEncoding termEncoding := by
  have hclauses := mapWithInput (f := fun (_ : CNF) clause => RawPair.clause clause)
    (id' (encIn := cnfEncoding)) (clause_polyTime.comp (snd cnfEncoding clauseEncoding))
  exact (fold_polyTime true).comp (hclauses.prod (const (.var 0 : Tree)))

theorem coreEquation_polyTime : ComputableInPolyTime RawPair.coreEquation cnfEncoding equationEncoding := by
  have hl := node_polyTime.comp ((const false).prod (left_polyTime.prod right_polyTime))
  exact FiniteTermMachines.equationRecode_polyTime.comp (hl.prod right_polyTime)

theorem hasEmpty_polyTime : ComputableInPolyTime (fun formula : CNF => formula.any List.isEmpty) cnfEncoding encBool := by
  have hc := (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.listIsEmpty (encA := literalEncoding))).comp
    (snd cnfEncoding clauseEncoding)
  exact anyWithInput (test := fun (_ : CNF) clause => clause.isEmpty) (id' (encIn := cnfEncoding)) hc

theorem reduction_polyTime : ComputableInPolyTime RawPair.equation cnfEncoding equationEncoding :=
  hasEmpty_polyTime.ite (const ((.var 0, .var 0) : Tree × Tree)) coreEquation_polyTime

theorem twoOwnerReduction_polyTime : ComputableInPolyTime RawPair.twoOwnerEquation cnfEncoding equationEncoding :=
  (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.listIsEmpty (encA := clauseEncoding))).ite
    (const ((.var 0, .var 1) : Tree × Tree)) reduction_polyTime
end KFOL.Complexity.RawPairMachines
