module
public import KFOL.Complexity.PolicyGuardWeight
public import KFOL.Complexity.PolicyGuardMachines
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
@[expose] public section
namespace KFOL.Complexity.PolicyTermFrontend
open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.Policies KFOL.FiniteTermCode PolicyGuardMachines
variable {Role Label : Type} [Fintype Role] [Fintype Label] [DecidableEq Role] [DecidableEq Label]
abbrev Tree := Policies.Term Label ℕ
abbrev Annotation := ℕ × List (Guard Label ℕ)
noncomputable abbrev annotationEncoding := encPair encNat (encList (guardEncoding (Label := Label)))
noncomputable abbrev termEncoding := PolicyTermMachines.termEncoding (Label := Label)
noncomputable def labelWeight (d : Label) : ℕ := 2 * (encFinite Label d).length + 1
noncomputable def labelWeightBound : ℕ := Finset.univ.sup (labelWeight (Label := Label))
omit [DecidableEq Label] in
private theorem labelWeight_le (d : Label) : labelWeight d ≤ labelWeightBound (Label := Label) := Finset.le_sup (by simp)

private theorem names_length (names : List ℕ) : (encList encNat names).length = (names.map PolicyGuardWeight.nameWeight).sum := by
  induction names with
  | nil => simp [encList_nil]
  | cons j names ih => simp only [encList_cons, List.length_append, length_frame, encNat_apply, ih,
      List.map_cons, List.sum_cons, PolicyGuardWeight.nameWeight]

omit [DecidableEq Label] in
private theorem passes_length (passes : List (Label × ℕ)) : (encList (passEncoding (Label := Label)) passes).length =
    (passes.map (fun p => PolicyGuardWeight.nameWeight p.2 + 2 * labelWeight p.1)).sum := by
  induction passes with
  | nil => simp [encList_nil]
  | cons p rest ih =>
    simp only [encList_cons, List.length_append, length_frame, length_encPair,
      encNat_apply, ih, List.map_cons, List.sum_cons, PolicyGuardWeight.nameWeight, labelWeight]
    omega

omit [DecidableEq Label] in
private theorem guard_length (g : Guard Label ℕ) : (guardEncoding g).length = PolicyGuardWeight.payload labelWeight g := by
  change (rawGuardEncoding (guardView g)).length = _
  simp only [rawGuardEncoding, guardView, length_encPair, names_length, passes_length,
    encNat_apply, PolicyGuardWeight.payload, PolicyGuardWeight.nameWeight]
  omega

omit [DecidableEq Label] in
private theorem list_length (guards : List (Guard Label ℕ)) : (encList guardEncoding guards).length =
    (guards.map (fun g => 2 * PolicyGuardWeight.payload labelWeight g + 1)).sum := by
  induction guards with
  | nil => simp [encList_nil]
  | cons g gs ih => simp only [encList_cons, List.length_append, length_frame,
      guard_length, ih, List.map_cons, List.sum_cons]

private def leaf (_ : Unit) (j : ℕ) : Annotation (Label := Label) := (j, [⟨j, [], []⟩])
private def resetNode (children : List (Annotation (Label := Label))) : Annotation (Label := Label) :=
  let left := children.getD 0 (0, [])
  let right := children.getD 1 (0, [])
  (right.1, right.2 ++ left.2.map (Guard.addMany right.1))
private def selectiveNode (D : Label → Finset Role) (top : Finset Role) (d : Label)
    (children : List (Annotation (Label := Label))) : Annotation (Label := Label) :=
  let x := children.getD 0 (0, [])
  let y := children.getD 1 (0, [])
  let z := children.getD 2 (0, [])
  let third := (z.2.map (Guard.addPass d y.1)).map (Guard.normalizeAt D top y.1)
  (x.1, x.2 ++ (y.2 ++ third).map (Guard.addMany x.1))
private def node (D : Label → Finset Role) (top : Finset Role) (_ : Unit)
    (operation : Operation (Symbol Label)) (children : List (Annotation (Label := Label))) : Annotation (Label := Label) :=
  match operation with
  | ⟨_, .reset⟩ => resetNode children
  | ⟨_, .selective d⟩ => selectiveNode D top d children

def annotation (D : Label → Finset Role) (top : Finset Role) (tree : Tree (Label := Label)) : Annotation (Label := Label) :=
  (tree.root, tree.normalGuards D top)

omit [Fintype Role] [Fintype Label] [DecidableEq Label] in
private theorem fold_annotation (D : Label → Finset Role) (top : Finset Role) (tree : Tree) :
    FiniteFoldMachine.fold leaf (node D top) () tree = annotation D top tree := by
  induction tree using Term.induction_policy with
  | var j => rfl
  | step s t hs ht => simp [FiniteFoldMachine.fold, Term.step, node, resetNode, List.ofFn_succ,
      hs, ht, annotation, Term.normalGuards, Term.root]
  | selective d x y z hx hy hz => simp [FiniteFoldMachine.fold, Term.selective, node, selectiveNode, List.ofFn_succ,
      hx, hy, hz, annotation, Term.normalGuards, Term.root]

omit [Fintype Role] [DecidableEq Label] in
private theorem annotation_bound (D : Label → Finset Role) (top : Finset Role) (tree : Tree) :
    (annotationEncoding (annotation D top tree)).length ≤
      (12 + 4 * labelWeightBound (Label := Label)) * ((FiniteTermCode.encode (Symbol Label) tree).length + 1)^3 := by
  have h := PolicyGuardWeight.annotation_le labelWeight labelWeightBound labelWeight_le D top tree
  simpa only [annotationEncoding, annotation, length_encPair, encNat_apply, list_length, PolicyGuardWeight.nameWeight] using h

omit [DecidableEq Label] in
private theorem leaf_polyTime : ComputableInPolyTime
    (fun p : Unit × ℕ => (leaf p.1 p.2 : Annotation (Label := Label))) (encPair encUnit encNat) annotationEncoding := by
  have hj := snd encUnit encNat
  have hguard : ComputableInPolyTime (fun p : Unit × ℕ => (p.2, ([] : List ℕ), ([] : List (Label × ℕ))))
      (encPair encUnit encNat) rawGuardEncoding := hj.prod ((const []).prod (const []))
  have hg : ComputableInPolyTime (fun p : Unit × ℕ => (⟨p.2, [], []⟩ : Guard Label ℕ))
      (encPair encUnit encNat) guardEncoding := hguard.of_enc_eq (fun _ => rfl)
  exact hj.prod (cons' hg (const []))

omit [DecidableEq Label] in
private theorem resetNode_polyTime : ComputableInPolyTime (resetNode (Label := Label)) (encList annotationEncoding) annotationEncoding := by
  have hleft := (listGetD (encA := annotationEncoding (Label := Label)) (encL := encList (annotationEncoding (Label := Label))) (0, [])).comp (id'.prod (const 0))
  have hright := (listGetD (encA := annotationEncoding (Label := Label)) (encL := encList (annotationEncoding (Label := Label))) (0, [])).comp (id'.prod (const 1))
  have hr := (fst encNat (encList guardEncoding)).comp hright
  have hguards := (snd encNat (encList guardEncoding)).comp hleft
  have hrightGuards := (snd encNat (encList guardEncoding)).comp hright
  have hroot := hr.comp (fst (encList (annotationEncoding (Label := Label))) (guardEncoding (Label := Label)))
  have hg := snd (encList (annotationEncoding (Label := Label))) (guardEncoding (Label := Label))
  have hm := mapWithInput (f := fun (children : List Annotation) guard =>
    guard.addMany (children.getD 1 (0, [])).1) hguards (addMany_polyTime.comp (hroot.prod hg))
  exact hr.prod (listAppend' hrightGuards hm)

omit [DecidableEq Label] in
private theorem selectiveNode_polyTime (D : Label → Finset Role) (top : Finset Role) (d : Label) : ComputableInPolyTime
    (selectiveNode D top d) (encList annotationEncoding) annotationEncoding := by
  let input := encList (annotationEncoding (Label := Label))
  have hx := (listGetD (encA := annotationEncoding) (encL := input) (0, [])).comp (id'.prod (const 0))
  have hy := (listGetD (encA := annotationEncoding) (encL := input) (0, [])).comp (id'.prod (const 1))
  have hz := (listGetD (encA := annotationEncoding) (encL := input) (0, [])).comp (id'.prod (const 2))
  have hr := (fst encNat (encList guardEncoding)).comp hx
  have htest := (fst encNat (encList guardEncoding)).comp hy
  have hgx := (snd encNat (encList guardEncoding)).comp hx
  have hgy := (snd encNat (encList guardEncoding)).comp hy
  have hgz := (snd encNat (encList guardEncoding)).comp hz
  have hg := snd input (guardEncoding (Label := Label))
  have hi := htest.comp (fst input (guardEncoding (Label := Label)))
  have hr' := hr.comp (fst input (guardEncoding (Label := Label)))
  have hpass := mapWithInput (f := fun (children : List (Annotation (Label := Label))) guard =>
    guard.addPass d (children.getD 1 (0, [])).1) hgz (addPass_polyTime.comp (((const d).prod hi).prod hg))
  have hnorm := mapWithInput (f := fun (children : List (Annotation (Label := Label))) guard =>
    guard.normalizeAt D top (children.getD 1 (0, [])).1) hpass ((normalizeAt_polyTime D top).comp (hi.prod hg))
  have hside := listAppend' hgy hnorm
  have hmany := mapWithInput (f := fun (children : List (Annotation (Label := Label))) guard =>
    guard.addMany (children.getD 0 (0, [])).1) hside (addMany_polyTime.comp (hr'.prod hg))
  exact hr.prod (listAppend' hgx hmany)

omit [DecidableEq Label] in
private theorem node_polyTime (D : Label → Finset Role) (top : Finset Role) : ComputableInPolyTime
    (fun p : Unit × (Operation (Symbol Label) × List (Annotation (Label := Label))) => node D top p.1 p.2.1 p.2.2)
    (encPair encUnit (encPair FiniteTermMachines.operationEncoding (encList annotationEncoding))) annotationEncoding := by
  let input := encPair encUnit (encPair (FiniteTermMachines.operationEncoding (σ := Symbol Label))
    (encList (annotationEncoding (Label := Label))))
  have hop : ComputableInPolyTime (fun p : Unit × (Operation (Symbol Label) × List (Annotation (Label := Label))) => p.2.1)
      input FiniteTermMachines.operationEncoding := by fun_prop
  have hc : ComputableInPolyTime (fun p : Unit × (Operation (Symbol Label) × List (Annotation (Label := Label))) => p.2.2)
      input (encList annotationEncoding) := by fun_prop
  apply hop.finite_cases (branch := fun operation p => node D top p.1 operation p.2.2)
  rintro ⟨n, operation⟩
  cases operation with
  | reset => exact resetNode_polyTime.comp hc
  | selective d => exact (selectiveNode_polyTime D top d).comp hc

omit [DecidableEq Label] in
/-- Full original native annotation, including every collision normalization. -/
theorem annotation_polyTime (D : Label → Finset Role) (top : Finset Role) :
    ComputableInPolyTime (annotation D top) termEncoding annotationEncoding := by
  have hf := FiniteFoldMachine.fold_polyTime (contextEncoding := encUnit) (valueEncoding := annotationEncoding)
    leaf (node D top) leaf_polyTime (node_polyTime D top) (12 + 4*labelWeightBound (Label := Label)) 3 (by
      intro context term
      cases context
      rw [fold_annotation]
      exact (annotation_bound D top term).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))) (0, [])
  have hp : ComputableInPolyTime (fun term : Tree (Label := Label) => ((), term)) termEncoding (encPair encUnit termEncoding) :=
    (const ()).prod id'
  have h := hf.comp hp
  convert h using 1
  funext term
  exact (fold_annotation D top term).symm

omit [DecidableEq Label] in
theorem normalGuards_polyTime (D : Label → Finset Role) (top : Finset Role) :
    ComputableInPolyTime (Term.normalGuards D top : Tree (Label := Label) → _) termEncoding (encList guardEncoding) :=
  (snd _ _).comp (annotation_polyTime D top)

omit [DecidableEq Label] in
theorem observation_polyTime (D : Label → Finset Role) (top : Finset Role) : ComputableInPolyTime
    (fun p : Tree (Label := Label) × Tree (Label := Label) => Term.familyObservationB D top p.1 p.2)
    (encPair termEncoding termEncoding) encBool := by
  have hl := (normalGuards_polyTime D top).comp (fst (termEncoding (Label := Label)) (termEncoding (Label := Label)))
  have hr := (normalGuards_polyTime D top).comp (snd (termEncoding (Label := Label)) (termEncoding (Label := Label)))
  exact bool_and' ((covers_polyTime D).comp (hl.prod hr)) ((covers_polyTime D).comp (hr.prod hl))

theorem equation_polyTime (D : Label → Finset Role) (roles : List Role) (labels : List Label) : ComputableInPolyTime
    (fun p : Tree (Label := Label) × Tree (Label := Label) => Term.familyEquationB D roles labels p.1 p.2)
    (encPair termEncoding termEncoding) encBool := by
  classical
  by_cases hc : patternChainB D roles labels = true
  · have htest : ComputableInPolyTime
        (fun p : (Tree (Label := Label) × Tree (Label := Label)) × Role =>
          Term.familyObservationB (fun d => (D d).erase p.2) (roles.toFinset.erase p.2) p.1.1 p.1.2)
        (encPair (encPair termEncoding termEncoding) (encFinite Role)) encBool := by
      apply (snd (encPair (termEncoding (Label := Label)) (termEncoding (Label := Label))) (encFinite Role)).finite_cases
        (branch := fun k p => Term.familyObservationB (fun d => (D d).erase k) (roles.toFinset.erase k) p.1.1 p.1.2)
      intro k
      exact (observation_polyTime (fun d => (D d).erase k) (roles.toFinset.erase k)).comp (fst _ _)
    have h := allWithInput (test := fun (p : Tree (Label := Label) × Tree (Label := Label)) k =>
      Term.familyObservationB (fun d => (D d).erase k) (roles.toFinset.erase k) p.1 p.2) (const roles) htest
    simpa only [Term.familyEquationB, hc, ite_true] using h
  · simpa only [Term.familyEquationB, hc, Bool.false_eq_true, ite_false] using observation_polyTime D roles.toFinset
end KFOL.Complexity.PolicyTermFrontend
