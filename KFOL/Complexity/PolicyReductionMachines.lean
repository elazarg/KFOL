module
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import KFOL.Complexity.PolicyTermMachines
public import KFOL.Complexity.ResetUnionReduction
public import KFOL.Complexity.FiniteTermDecoding
public import KFOL.Policies.Families
@[expose] public section
namespace KFOL.Complexity.PolicyReductionMachines
open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.Policies KFOL.Reductions
open PolicyTermMachines
variable {Label Role : Type} [Fintype Label]
abbrev Tree := Policies.Term Label ℕ
noncomputable abbrev equationEncoding : (Tree (Label := Label) × Tree (Label := Label)) ↪ List Bool :=
  FiniteTermMachines.equationEncoding
abbrev literalEncoding := ResetUnionReduction.literalEncoding
abbrev clauseEncoding := ResetUnionReduction.clauseEncoding
abbrev cnfEncoding := ResetUnionReduction.cnfEncoding

private theorem expand_polyTime (E : PolicyExpr Label) : ComputableInPolyTime
    (fun p : Tree × (Tree × Tree) => E.expand p.1 p.2.1 p.2.2)
    (encPair termEncoding (encPair termEncoding termEncoding)) termEncoding := by
  let input := encPair (termEncoding (Label := Label)) (encPair (termEncoding (Label := Label)) (termEncoding (Label := Label)))
  have hx := fst (termEncoding (Label := Label)) (encPair (termEncoding (Label := Label)) (termEncoding (Label := Label)))
  have hy : ComputableInPolyTime (fun p : Tree × (Tree × Tree) => p.2.1) input termEncoding := by fun_prop
  have hz : ComputableInPolyTime (fun p : Tree × (Tree × Tree) => p.2.2) input termEncoding := by fun_prop
  induction E with
  | atom d => exact selective_polyTime d
  | bottom => exact step_polyTime.comp ((step_polyTime.comp (hy.prod hx)).prod (step_polyTime.comp (hz.prod hx)))
  | top => exact step_polyTime.comp ((step_polyTime.comp (hz.prod hy)).prod hx)
  | sup E F hE hF => exact hE.comp (hx.prod (hy.prod hF))
  | inf E F hE hF => exact step_polyTime.comp (hE.prod hF)

omit [Fintype Label] in
private theorem relabel_step {Var : Type} (f : Var → ℕ) (s t : Policies.Term Label Var) :
    (Term.step s t).relabel f = Term.step (s.relabel f) (t.relabel f) := by
  simp only [Term.step, FirstOrder.Language.Term.relabel]
  congr 1
  funext i
  split <;> rfl
omit [Fintype Label] in
private theorem relabel_selective {Var : Type} (f : Var → ℕ) (d : Label) (x y z : Policies.Term Label Var) :
    (Term.selective d x y z).relabel f = Term.selective d (x.relabel f) (y.relabel f) (z.relabel f) := by
  simp only [Term.selective, FirstOrder.Language.Term.relabel]
  congr 1
  funext i
  split_ifs <;> rfl
omit [Fintype Label] in
private theorem relabel_expand {Var : Type} (f : Var → ℕ) (E : PolicyExpr Label) (x y z : Policies.Term Label Var) :
    (E.expand x y z).relabel f = E.expand (x.relabel f) (y.relabel f) (z.relabel f) := by
  induction E generalizing x y z with
  | atom d => exact relabel_selective f d x y z
  | bottom => simp only [PolicyExpr.expand, relabel_step]
  | top => simp only [PolicyExpr.expand, relabel_step]
  | sup E F hE hF => simp only [PolicyExpr.expand, hE, hF]
  | inf E F hE hF => simp only [PolicyExpr.expand, relabel_step, hE, hF]

private theorem gate_polyTime (E : PolicyExpr Label) : ComputableInPolyTime
    (fun p : ℕ × Tree => E.gate 0 (2 * p.1 + 2) p.2)
    (encPair encNat termEncoding) termEncoding := by
  have hj := binary_add.comp ((binary_mul' (const 2) (fst encNat (termEncoding (Label := Label)))).prod (const 2))
  exact (expand_polyTime E).comp ((const (.var 0 : Tree)).prod ((var_polyTime.comp hj).prod (snd _ _)))

/-- A fixed-depth native generator. The class transport rejects wide sources;
three nested expanded macros include all actual continuation copies. -/
def clauseAt (plan : Hardness.Plan Role Label) : ℕ → Clause → Tree (Label := Label)
  | 0, _ => .var 1
  | _ + 1, [] => .var 1
  | n + 1, literal :: rest =>
      (if literal.2 then plan.zero else plan.one).gate 0 (2 * literal.1 + 2) (clauseAt plan n rest)

private theorem clauseAt_polyTime (plan : Hardness.Plan Role Label) (n : ℕ) :
    ComputableInPolyTime (clauseAt plan n) clauseEncoding termEncoding := by
  induction n with
  | zero => exact const (.var 1 : Tree)
  | succ n ih =>
    have htail := ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.listTail literalEncoding)
    have hhead := headD (encA := literalEncoding) (encL := clauseEncoding) (0, true)
    have hsign := (snd encNat encBool).comp hhead
    have hname := (fst encNat encBool).comp hhead
    have hargs := hname.prod (ih.comp htail)
    have hbody := hsign.ite ((gate_polyTime plan.zero).comp hargs) ((gate_polyTime plan.one).comp hargs)
    have h := (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.listIsEmpty (encA := literalEncoding))).ite
      (const (.var 1 : Tree)) hbody
    convert h using 1
    funext clause
    cases clause with
    | nil => rfl
    | cons literal rest =>
      rcases literal with ⟨i, sign⟩
      cases sign <;> rfl

omit [Fintype Label] in
private theorem clauseAt_eq (code : Role ↪ ℕ) (plan : Hardness.Plan Role Label) (n : ℕ) (clause : Clause)
    (h : clause.length ≤ n) : clauseAt plan n clause = (plan.clause clause).relabel (Hardness.Variable.toNat code) := by
  induction n generalizing clause with
  | zero => cases clause with | nil => rfl | cons l ls => simp at h
  | succ n ih =>
    cases clause with
    | nil => rfl
    | cons literal rest =>
      have hr : rest.length ≤ n := by simpa using h
      simp only [clauseAt, Hardness.Plan.clause, PolicyExpr.gate, relabel_expand]
      split <;> simp only [FirstOrder.Language.Term.relabel, Hardness.Variable.toNat, ← ih rest hr]

private theorem rightComb_polyTime : ComputableInPolyTime
    (fun p : List (Tree (Label := Label)) × Tree (Label := Label) => p.1.foldr Term.step p.2)
    (encPair (encList termEncoding) termEncoding) termEncoding := by
  let input := encPair (encList (termEncoding (Label := Label))) (termEncoding (Label := Label))
  have hl := fst (encList (termEncoding (Label := Label))) (termEncoding (Label := Label))
  have hr := (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.listReverse (termEncoding (Label := Label)))).comp hl
  have hs : ComputableInPolyTime (fun p : ((List (Tree (Label := Label)) × Tree (Label := Label)) × Tree (Label := Label)) × Tree (Label := Label) => p.1.2)
      (encPair (encPair input termEncoding) termEncoding) termEncoding := by fun_prop
  have ht := snd (encPair input (termEncoding (Label := Label))) (termEncoding (Label := Label))
  have hg := hl.polyBounded_length.add (PolyBounded.const (resetHeader (Label := Label)))
  have h := foldlWithInput_of_bounded_growth (list := fun p : List Tree × Tree => p.1.reverse) (init := fun p => p.2)
    (step := fun _ state tree => Term.step tree state) (snd _ _)
    ⟨hr, step_polyTime.comp (ht.prod hs), inferInstance, inferInstance⟩
    (growth := fun p => (encList termEncoding p.1).length + resetHeader (Label := Label)) ⟨hg, ?_⟩
  · convert h using 1
    funext p
    rw [List.foldl_reverse]
  · intro p state tree htree
    have ht := SizedListEncoding.length_elem_le (encA := termEncoding) (encL := encList termEncoding)
      p.1 tree (List.mem_reverse.mp htree)
    have hn := length_step tree state
    omega


private theorem booleanTerm_polyTime : ComputableInPolyTime
    (fun j : ℕ => (.var (2 * j + 2) : Tree (Label := Label))) encNat termEncoding :=
  var_polyTime.comp (binary_add.comp ((binary_mul' (const 2) (id' (encIn := encNat))).prod (const 2)))

omit [Fintype Label] in
private theorem relabel_rightComb {Var : Type} (f : Var → ℕ) (trees : List (Policies.Term Label Var)) (base : Policies.Term Label Var) :
    (trees.foldr Term.step base).relabel f = (trees.map (fun tree => tree.relabel f)).foldr Term.step (base.relabel f) := by
  induction trees with
  | nil => rfl
  | cons tree trees ih => simp only [List.foldr_cons, List.map_cons, relabel_step, ih]

private theorem baseline_polyTime (code : Role ↪ ℕ) (plan : Hardness.Plan Role Label) : ComputableInPolyTime
    (fun formula => (plan.baseline formula).relabel (Hardness.Variable.toNat code)) cnfEncoding termEncoding := by
  have hvars := mapWithInput (f := fun (_ : CNF) j => (.var (2 * j + 2) : Tree (Label := Label)))
    ResetUnionReduction.support_polyTime (booleanTerm_polyTime.comp (snd cnfEncoding encNat))
  have hlist := listAppend' hvars (const (plan.calibration.map (fun item => (.var (2 * code item.1 + 3) : Tree (Label := Label)))))
  have h := rightComb_polyTime.comp (hlist.prod (const (.var 0 : Tree (Label := Label))))
  convert h using 1
  funext formula
  simp only [Hardness.Plan.baseline, Hardness.Plan.rightComb, relabel_rightComb, Hardness.Plan.inputs,
    List.map_append, List.map_map, Function.comp_def, FirstOrder.Language.Term.relabel, Hardness.Variable.toNat]

noncomputable abbrev testEncoding : (Label × ℕ) ↪ List Bool := encPair (encFinite Label) encNat

private theorem selectiveDynamic_polyTime : ComputableInPolyTime
    (fun p : Label × (Tree × (Tree × Tree)) => Term.selective p.1 p.2.1 p.2.2.1 p.2.2.2)
    (encPair (encFinite Label) (encPair termEncoding (encPair termEncoding termEncoding))) termEncoding := by
  apply (fst (encFinite Label) (encPair (termEncoding (Label := Label))
    (encPair (termEncoding (Label := Label)) (termEncoding (Label := Label))))).finite_cases (branch := fun label p => Term.selective label p.2.1 p.2.2.1 p.2.2.2)
  intro label
  exact (selective_polyTime label).comp (snd _ _)

noncomputable def selectiveHeaderBound : ℕ := Finset.univ.sup (selectiveHeader (Label := Label))

private theorem selective_header_le (label : Label) : selectiveHeader label ≤ selectiveHeaderBound (Label := Label) :=
  Finset.le_sup (by simp)

def gatesNat (tests : List (Label × ℕ)) : Tree (Label := Label) :=
  tests.foldr (fun test continuation => Term.selective test.1 (.var 0) (.var test.2) continuation) (.var 1)

private theorem gatesNat_polyTime : ComputableInPolyTime (gatesNat (Label := Label)) (encList testEncoding) termEncoding := by
  have htestName : ComputableInPolyTime (fun p : List (Label × ℕ) × (Label × ℕ) => p.2.2)
      (encPair (encList testEncoding) testEncoding) encNat := by fun_prop
  have htvars := mapWithInput (f := fun (_ : List (Label × ℕ)) (test : Label × ℕ) => (.var test.2 : Tree (Label := Label)))
    (id' (encIn := encList testEncoding)) (var_polyTime.comp htestName)
  let input := encPair (encPair (encList (testEncoding (Label := Label))) (termEncoding (Label := Label))) (testEncoding (Label := Label))
  have hd : ComputableInPolyTime (fun p : (List (Label × ℕ) × Tree) × (Label × ℕ) => p.2.1) input (encFinite Label) := by fun_prop
  have hj : ComputableInPolyTime (fun p : (List (Label × ℕ) × Tree) × (Label × ℕ) => p.2.2) input encNat := by fun_prop
  have hs : ComputableInPolyTime (fun p : (List (Label × ℕ) × Tree) × (Label × ℕ) => p.1.2) input termEncoding := by fun_prop
  have hstep := selectiveDynamic_polyTime.comp (hd.prod ((const (.var 0 : Tree)).prod ((var_polyTime.comp hj).prod hs)))
  have hreverse := ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.listReverse (testEncoding (Label := Label)))
  have hg := (htvars.polyBounded_length.add (PolyBounded.const ((termEncoding (.var 0 : Tree (Label := Label))).length))).add
    (PolyBounded.const (selectiveHeaderBound (Label := Label)))
  have h := foldlWithInput_of_bounded_growth (list := List.reverse) (init := fun (_ : List (Label × ℕ)) => (.var 1 : Tree))
    (step := fun _ state test => Term.selective test.1 (.var 0) (.var test.2) state)
    (const (.var 1 : Tree)) ⟨hreverse, hstep, inferInstance, inferInstance⟩
    (growth := fun tests => (encList termEncoding (tests.map (fun test => (.var test.2 : Tree)))).length +
      (termEncoding (.var 0 : Tree)).length + selectiveHeaderBound (Label := Label)) ⟨hg, ?_⟩
  · convert h using 1
    funext tests
    rw [List.foldl_reverse]
    rfl
  · intro tests state test htest
    have hm : (.var test.2 : Tree (Label := Label)) ∈ tests.map (fun test => (.var test.2 : Tree)) :=
      List.mem_map.mpr ⟨test, List.mem_reverse.mp htest, rfl⟩
    have hb := SizedListEncoding.length_elem_le (encA := termEncoding) (encL := encList termEncoding) _ _ hm
    have hn := length_selective test.1 (.var 0) (.var test.2) state
    have hh := selective_header_le test.1
    omega

omit [Fintype Label] in
private theorem gatesNat_eq (code : Role ↪ ℕ) (tests : List (Label × Hardness.Variable Role)) :
    gatesNat (tests.map (fun test => (test.1, Hardness.Variable.toNat code test.2))) =
      (Hardness.Plan.gates tests).relabel (Hardness.Variable.toNat code) := by
  induction tests with
  | nil => rfl
  | cons test tests ih =>
    simp only [gatesNat, Hardness.Plan.gates, List.foldr_cons, List.map_cons, relabel_selective,
      FirstOrder.Language.Term.relabel, Hardness.Variable.toNat] at ih ⊢
    exact congrArg (fun continuation => Term.selective test.1 (.var 0) (.var (Hardness.Variable.toNat code test.2)) continuation) ih

private theorem gates_polyTime (code : Role ↪ ℕ) (plan : Hardness.Plan Role Label) : ComputableInPolyTime
    (fun formula => (Hardness.Plan.gates (plan.positiveTests formula)).relabel (Hardness.Variable.toNat code)) cnfEncoding termEncoding := by
  have hj := snd cnfEncoding encNat
  have hname := binary_add.comp ((binary_mul' (const 2) hj).prod (const 2))
  have hp : ComputableInPolyTime (fun p : CNF × ℕ => plan.preliminary.map (fun d => (d, 2 * p.2 + 2)))
      (encPair cnfEncoding encNat) (encList testEncoding) := by
    have h := mapWithInput (encA := encFinite Label) (encB := testEncoding) (f := fun (p : CNF × ℕ) d => (d, 2 * p.2 + 2)) (const plan.preliminary)
      ((snd _ _).prod (hname.comp (fst _ _)))
    exact h
  have htests := flatMapWithInput (f := fun (_ : CNF) j => plan.preliminary.map (fun d => (d, 2*j+2)))
    ResetUnionReduction.support_polyTime hp
  have hlist := listAppend' htests (const (plan.calibration.flatMap (fun item => item.2.1.map (fun d => (d, 2*code item.1+3)))))
  have h := gatesNat_polyTime.comp hlist
  convert h using 1
  funext formula
  rw [← gatesNat_eq]
  simp only [Hardness.Plan.positiveTests, List.map_append, List.map_flatMap, List.map_map, Function.comp_def,
    Hardness.Variable.toNat]

/-- All native expanded clauses have depth at most three here. The source
width guard in the class reduction ensures exact agreement with the paper's
unrestricted independent term construction. -/
def equationAt (code : Role ↪ ℕ) (plan : Hardness.Plan Role Label) (formula : CNF) : Tree (Label := Label) × Tree (Label := Label) :=
  let right := (formula.map (clauseAt plan 3) ++ plan.calibrationBranches.map (fun tree => tree.relabel (Hardness.Variable.toNat code))).foldr
    Term.step ((plan.baseline formula).relabel (Hardness.Variable.toNat code))
  (Term.step ((Hardness.Plan.gates (plan.positiveTests formula)).relabel (Hardness.Variable.toNat code)) right, right)

theorem reduction_polyTime (code : Role ↪ ℕ) (plan : Hardness.Plan Role Label) :
    ComputableInPolyTime (equationAt code plan) cnfEncoding equationEncoding := by
  have hclauses := mapWithInput (f := fun (_ : CNF) clause => clauseAt plan 3 clause)
    (id' (encIn := cnfEncoding)) ((clauseAt_polyTime plan 3).comp (snd cnfEncoding clauseEncoding))
  have hlist := listAppend' hclauses (const (plan.calibrationBranches.map (fun tree => tree.relabel (Hardness.Variable.toNat code))))
  have hr := rightComb_polyTime.comp (hlist.prod (baseline_polyTime code plan))
  have hl := step_polyTime.comp ((gates_polyTime code plan).prod hr)
  exact FiniteTermMachines.equationRecode_polyTime.comp (hl.prod hr)

omit [Fintype Label] in
theorem equationAt_eq (code : Role ↪ ℕ) (plan : Hardness.Plan Role Label) (formula : CNF)
    (hw : ∀ clause ∈ formula, clause.length ≤ 3) : equationAt code plan formula =
      ((plan.equation formula).1.relabel (Hardness.Variable.toNat code),
        (plan.equation formula).2.relabel (Hardness.Variable.toNat code)) := by
  have hc : formula.map (clauseAt plan 3) = formula.map (fun clause => (plan.clause clause).relabel (Hardness.Variable.toNat code)) := by
    apply List.map_congr_left
    exact fun clause hm => clauseAt_eq code plan 3 clause (hw clause hm)
  simp only [equationAt, hc, Hardness.Plan.equation, Hardness.Plan.left, Hardness.Plan.right,
    Hardness.Plan.rightComb, relabel_step, relabel_rightComb, List.map_append, List.map_map, Function.comp_def]
end KFOL.Complexity.PolicyReductionMachines
