module

public import KFOL.Complexity.FiniteFoldRuntime
public import KFOL.Complexity.OwnerTermMachines
public import KFOL.Owner.GuardEncoding
public import KFOL.Owner.Completeness
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length

/-! # Original one-owner tree annotations, uniformly in the ambient role count -/

@[expose] public section

namespace KFOL.Complexity.OwnerTermFrontend

universe u

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FiniteTermCode

abbrev Tree := Owner.Term Unit ℕ
abbrev RawGuard := ℕ × (List ℕ × List ℕ)
abbrev rawGuardEncoding := encPair encNat (encPair (encList encNat) (encList encNat))

def guardView (guard : Owner.Guard ℕ) : RawGuard := (guard.source, guard.many, guard.outside)

def guardEncoding : Owner.Guard ℕ ↪ List Bool :=
  ⟨fun guard => rawGuardEncoding (guardView guard), by
    intro x y h
    have he := rawGuardEncoding.injective h
    cases x
    cases y
    simpa only [guardView, Owner.Guard.mk.injEq, Prod.mk.injEq] using he⟩

abbrev Annotation := ℕ × List (Owner.Guard ℕ)
abbrev annotationEncoding := encPair encNat (encList guardEncoding)
noncomputable abbrev termEncoding := OwnerTermMachines.termEncoding (Role := Unit)

@[fun_prop] theorem guardView_polyTime : ComputableInPolyTime guardView guardEncoding rawGuardEncoding :=
  .of_eq (fun _ => rfl)

private theorem addMany_polyTime : ComputableInPolyTime
    (fun p : ℕ × Owner.Guard ℕ => p.2.addMany p.1) (encPair encNat guardEncoding) guardEncoding := by
  have hj := fst encNat guardEncoding
  have hg := guardView_polyTime.comp (snd encNat guardEncoding)
  have hs := (fst encNat (encPair (encList encNat) (encList encNat))).comp hg
  have hm := (fst (encList encNat) (encList encNat)).comp ((snd encNat _).comp hg)
  have ho := (snd (encList encNat) (encList encNat)).comp ((snd encNat _).comp hg)
  have h := hs.prod ((cons' hj hm).prod ho)
  exact h.of_enc_eq (fun _ => rfl)

private theorem addOutside_polyTime : ComputableInPolyTime
    (fun p : ℕ × Owner.Guard ℕ => p.2.addOutside p.1) (encPair encNat guardEncoding) guardEncoding := by
  have hj := fst encNat guardEncoding
  have hg := guardView_polyTime.comp (snd encNat guardEncoding)
  have hs := (fst encNat (encPair (encList encNat) (encList encNat))).comp hg
  have hm := (fst (encList encNat) (encList encNat)).comp ((snd encNat _).comp hg)
  have ho := (snd (encList encNat) (encList encNat)).comp ((snd encNat _).comp hg)
  have h := hs.prod (hm.prod (cons' hj ho))
  exact h.of_enc_eq (fun _ => rfl)

private def leaf (_ : Unit) (j : ℕ) : Annotation := (j, [⟨j, [], []⟩])

private def resetNode (children : List Annotation) : Annotation :=
  let left := children.getD 0 (0, [])
  let right := children.getD 1 (0, [])
  (right.1, right.2 ++ left.2.map (Owner.Guard.addMany right.1))

private def guardedNode (children : List Annotation) : Annotation :=
  let root := children.getD 0 (0, [])
  let left := children.getD 1 (0, [])
  let right := children.getD 2 (0, [])
  let side := left.2 ++ right.2
  let outside := (side.map (Owner.Guard.addOutside left.1)).map (Owner.Guard.addOutside right.1)
  (root.1, root.2 ++ outside.map (Owner.Guard.addMany root.1))

private def node (_ : Unit) (operation : Operation (Owner.Symbol Unit)) (children : List Annotation) : Annotation :=
  match operation with
  | ⟨_, .reset⟩ => resetNode children
  | ⟨_, .guarded _⟩ => guardedNode children

def annotation (term : Tree) : Annotation :=
  (term.root, (term.withOwner false).guards true)

private theorem fold_annotation (term : Tree) :
    FiniteFoldMachine.fold leaf node () term = annotation term := by
  induction term using Owner.Term.induction_owner with
  | var j => rfl
  | step s t hs ht =>
    simp [FiniteFoldMachine.fold, Owner.Term.step, node, resetNode, List.ofFn_succ,
      hs, ht, annotation, Owner.Term.withOwner, Owner.Term.guards, Owner.Term.root]
  | guarded owner x y z hx hy hz =>
    cases owner
    simp [FiniteFoldMachine.fold, Owner.Term.guarded, node, guardedNode, List.ofFn_succ,
      hx, hy, hz, annotation, Owner.Term.withOwner, Owner.Term.guards, Owner.Term.root]

private theorem leaf_polyTime : ComputableInPolyTime
    (fun p : Unit × ℕ => leaf p.1 p.2) (encPair encUnit encNat) annotationEncoding := by
  have hj := snd encUnit encNat
  have hguard : ComputableInPolyTime (fun p : Unit × ℕ => (p.2, ([] : List ℕ), ([] : List ℕ)))
      (encPair encUnit encNat) rawGuardEncoding := hj.prod ((const []).prod (const []))
  have hg : ComputableInPolyTime (fun p : Unit × ℕ => (⟨p.2, [], []⟩ : Owner.Guard ℕ))
      (encPair encUnit encNat) guardEncoding := hguard.of_enc_eq (fun _ => rfl)
  exact hj.prod (cons' hg (const []))

private theorem resetNode_polyTime : ComputableInPolyTime resetNode (encList annotationEncoding) annotationEncoding := by
  have hleft := (listGetD (encA := annotationEncoding) (encL := encList annotationEncoding) (0, [])).comp (id'.prod (const 0))
  have hright := (listGetD (encA := annotationEncoding) (encL := encList annotationEncoding) (0, [])).comp (id'.prod (const 1))
  have hr := (fst encNat (encList guardEncoding)).comp hright
  have hguards := (snd encNat (encList guardEncoding)).comp hleft
  have hrightGuards := (snd encNat (encList guardEncoding)).comp hright
  have hroot := hr.comp (fst (encList annotationEncoding) guardEncoding)
  have hg := snd (encList annotationEncoding) guardEncoding
  have hm := mapWithInput (f := fun (children : List Annotation) guard =>
    guard.addMany (children.getD 1 (0, [])).1) hguards (addMany_polyTime.comp (hroot.prod hg))
  exact hr.prod (listAppend' hrightGuards hm)

private theorem guardedNode_polyTime : ComputableInPolyTime guardedNode (encList annotationEncoding) annotationEncoding := by
  let input := encList annotationEncoding
  have hroot := (listGetD (encA := annotationEncoding) (encL := encList annotationEncoding) (0, [])).comp (id'.prod (const 0))
  have hleft := (listGetD (encA := annotationEncoding) (encL := encList annotationEncoding) (0, [])).comp (id'.prod (const 1))
  have hright := (listGetD (encA := annotationEncoding) (encL := encList annotationEncoding) (0, [])).comp (id'.prod (const 2))
  have hr := (fst encNat (encList guardEncoding)).comp hroot
  have hl := (fst encNat (encList guardEncoding)).comp hleft
  have hz := (fst encNat (encList guardEncoding)).comp hright
  have hrootGuards := (snd encNat (encList guardEncoding)).comp hroot
  have hleftGuards := (snd encNat (encList guardEncoding)).comp hleft
  have hrightGuards := (snd encNat (encList guardEncoding)).comp hright
  have hside := listAppend' hleftGuards hrightGuards
  have hg := snd input guardEncoding
  have hl' := hl.comp (fst input guardEncoding)
  have hz' := hz.comp (fst input guardEncoding)
  have hr' := hr.comp (fst input guardEncoding)
  have hfirst := mapWithInput (f := fun (children : List Annotation) guard =>
    guard.addOutside (children.getD 1 (0, [])).1) hside (addOutside_polyTime.comp (hl'.prod hg))
  have hsecond := mapWithInput (f := fun (children : List Annotation) guard =>
    guard.addOutside (children.getD 2 (0, [])).1) hfirst (addOutside_polyTime.comp (hz'.prod hg))
  have hmany := mapWithInput (f := fun (children : List Annotation) guard =>
    guard.addMany (children.getD 0 (0, [])).1) hsecond (addMany_polyTime.comp (hr'.prod hg))
  exact hr.prod (listAppend' hrootGuards hmany)

private theorem node_polyTime : ComputableInPolyTime
    (fun p : Unit × (Operation (Owner.Symbol Unit) × List Annotation) => node p.1 p.2.1 p.2.2)
    (encPair encUnit (encPair FiniteTermMachines.operationEncoding (encList annotationEncoding))) annotationEncoding := by
  let input := encPair encUnit (encPair (FiniteTermMachines.operationEncoding (σ := Owner.Symbol Unit))
    (encList annotationEncoding))
  have hop : ComputableInPolyTime
      (fun p : Unit × (Operation (Owner.Symbol Unit) × List Annotation) => p.2.1)
      input FiniteTermMachines.operationEncoding := by fun_prop
  have hchildren : ComputableInPolyTime
      (fun p : Unit × (Operation (Owner.Symbol Unit) × List Annotation) => p.2.2)
      input (encList annotationEncoding) := by fun_prop
  apply hop.finite_cases (branch := fun operation p => node p.1 operation p.2.2)
  rintro ⟨n, operation⟩
  cases operation with
  | reset => exact resetNode_polyTime.comp hchildren
  | guarded owner => exact guardedNode_polyTime.comp hchildren

private theorem guardEncoding_length (guard : Owner.Guard ℕ) :
    (guardEncoding guard).length = guard.payloadWeight (fun j => 2 * j.bits.length + 1) := by
  change (rawGuardEncoding (guard.source, guard.many, guard.outside)).length = _
  simp only [rawGuardEncoding, length_encPair, length_encList,
    encNat_apply, Owner.Guard.payloadWeight]
  omega

private theorem annotationEncoding_length (term : Tree) :
    (annotationEncoding (annotation term)).length =
      (term.withOwner false).guardAnnotationWeight (fun j => 2 * j.bits.length + 1) true := by
  simp only [annotationEncoding, annotation, length_encPair, length_encList, guardEncoding_length,
    encNat_apply, Owner.Term.guardAnnotationWeight, Owner.Term.root_withOwner]

/-- The exact original reset/H term computes its full raw annotation in native
polynomial time, retaining every original guard and repeated prerequisite. -/
theorem annotation_polyTime : ComputableInPolyTime annotation termEncoding annotationEncoding := by
  have hfold := FiniteFoldMachine.fold_polyTime (contextEncoding := encUnit) (valueEncoding := annotationEncoding)
    leaf node leaf_polyTime node_polyTime 6 3 (by
      intro context term
      cases context
      rw [fold_annotation, annotationEncoding_length]
      exact (Owner.Term.guardAnnotationWeight_le_encode term).trans
        (Nat.mul_le_mul_left 6 (Nat.pow_le_pow_left (by omega) 3))) (0, [])
  have hp : ComputableInPolyTime (fun term : Tree => ((), term)) termEncoding (encPair encUnit termEncoding) :=
    (const ()).prod id'
  have h := hfold.comp hp
  convert h using 1
  funext term
  exact (fold_annotation term).symm

/-- Full non-owner raw guards, uniformly in the number of ambient roles. -/
theorem guards_polyTime : ComputableInPolyTime
    (fun term : Tree => (term.withOwner false).guards true) termEncoding (encList guardEncoding) :=
  (snd encNat (encList guardEncoding)).comp annotation_polyTime

private def contains (input : ℕ × List ℕ) : Bool := input.2.any (fun j => decide (input.1 = j))

private theorem contains_polyTime : ComputableInPolyTime contains (encPair encNat (encList encNat)) encBool := by
  let input := encPair encNat (encList encNat)
  have hlist := snd encNat (encList encNat)
  have hroot : ComputableInPolyTime (fun p : (ℕ × List ℕ) × ℕ => p.1.1)
      (encPair input encNat) encNat := by fun_prop
  have hitem := snd input encNat
  exact anyWithInput (test := fun (p : ℕ × List ℕ) j => decide (p.1 = j)) hlist (decide_eq' hroot hitem)

private theorem contains_eq (j : ℕ) (values : List ℕ) : contains (j, values) = decide (j ∈ values) := by
  apply Bool.eq_iff_iff.mpr
  simp only [contains, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hj
    exact ⟨j, hj, rfl⟩

@[fun_prop] private theorem source_polyTime : ComputableInPolyTime
    (fun guard : Owner.Guard ℕ => guard.source) guardEncoding encNat :=
  (fst encNat (encPair (encList encNat) (encList encNat))).comp guardView_polyTime

@[fun_prop] private theorem many_polyTime : ComputableInPolyTime
    (fun guard : Owner.Guard ℕ => guard.many) guardEncoding (encList encNat) :=
  (fst (encList encNat) (encList encNat)).comp ((snd encNat _).comp guardView_polyTime)

@[fun_prop] private theorem outside_polyTime : ComputableInPolyTime
    (fun guard : Owner.Guard ℕ => guard.outside) guardEncoding (encList encNat) :=
  (snd (encList encNat) (encList encNat)).comp ((snd encNat _).comp guardView_polyTime)

theorem dominates_polyTime : ComputableInPolyTime
    (fun p : Owner.Guard ℕ × Owner.Guard ℕ => Owner.dominatesB p.1 p.2)
    (encPair guardEncoding guardEncoding) encBool := by
  let input := encPair guardEncoding guardEncoding
  have hw := fst guardEncoding guardEncoding
  have hs := snd guardEncoding guardEncoding
  have hsourceW := source_polyTime.comp hw
  have hsourceS := source_polyTime.comp hs
  have hmW := many_polyTime.comp hw
  have hoW := outside_polyTime.comp hw
  have hmS := many_polyTime.comp hs
  have hoS := outside_polyTime.comp hs
  have hi := snd input encNat
  have hmS' := hmS.comp (fst input encNat)
  have hoS' := hoS.comp (fst input encNat)
  have hsourceS' := hsourceS.comp (fst input encNat)
  have hm := contains_polyTime.comp (hi.prod hmS')
  have ho := contains_polyTime.comp (hi.prod hoS')
  have he := decide_eq' hi hsourceS'
  have hmany := allWithInput (test := fun (p : Owner.Guard ℕ × Owner.Guard ℕ) j => contains (j, p.2.many)) hmW hm
  have houtside := allWithInput (test := fun (p : Owner.Guard ℕ × Owner.Guard ℕ) j =>
    contains (j, p.2.many) || contains (j, p.2.outside) || decide (j = p.2.source)) hoW
    (bool_or.comp ((bool_or.comp (hm.prod ho)).prod he))
  have h := bool_and' (bool_and' (decide_eq' hsourceW hsourceS) hmany) houtside
  convert h using 1
  funext p
  apply Bool.eq_iff_iff.mpr
  simp only [Owner.dominatesB, Function.comp_def, contains_eq, Bool.and_eq_true,
    Bool.or_eq_true, List.all_eq_true, decide_eq_true_eq]
  simp only [or_assoc]

theorem covers_polyTime : ComputableInPolyTime
    (fun p : List (Owner.Guard ℕ) × List (Owner.Guard ℕ) => Owner.coversB p.1 p.2)
    (encPair (encList guardEncoding) (encList guardEncoding)) encBool := by
  let input := encPair (encList guardEncoding) (encList guardEncoding)
  let inner := encPair input guardEncoding
  have hleft := fst (encList guardEncoding) (encList guardEncoding)
  have hright : ComputableInPolyTime
      (fun p : (List (Owner.Guard ℕ) × List (Owner.Guard ℕ)) × Owner.Guard ℕ => p.1.2)
      inner (encList guardEncoding) := by fun_prop
  have hstrong := snd inner guardEncoding
  have hweak : ComputableInPolyTime
      (fun p : ((List (Owner.Guard ℕ) × List (Owner.Guard ℕ)) × Owner.Guard ℕ) × Owner.Guard ℕ => p.1.2)
      (encPair inner guardEncoding) guardEncoding := by fun_prop
  have hdom := dominates_polyTime.comp (hstrong.prod hweak)
  have hany := anyWithInput (test := fun (p : (List (Owner.Guard ℕ) × List (Owner.Guard ℕ)) × Owner.Guard ℕ) strong =>
    Owner.dominatesB strong p.2) hright hdom
  exact allWithInput (test := fun (p : List (Owner.Guard ℕ) × List (Owner.Guard ℕ)) weak =>
    p.2.any (fun strong => Owner.dominatesB strong weak)) hleft hany

/-- The original one-owner syntax checker is polynomial-time uniformly in the
ambient number of roles; its entire input alphabet is reset and one ternary H. -/
theorem equation_polyTime : ComputableInPolyTime
    (fun p : Tree × Tree => Owner.Term.equationB true (p.1.withOwner false) (p.2.withOwner false))
    (encPair termEncoding termEncoding) encBool := by
  have hl := guards_polyTime.comp (fst termEncoding termEncoding)
  have hr := guards_polyTime.comp (snd termEncoding termEncoding)
  exact bool_and' (covers_polyTime.comp (hl.prod hr)) (covers_polyTime.comp (hr.prod hl))

private theorem ownersIn_withOwner {Role : Type u} (owner : Role) (term : Tree) :
    (term.withOwner owner).OwnersIn (fun r => r = owner) := by
  induction term with
  | var j => trivial
  | @func n symbol children ih =>
    cases symbol with
    | reset => exact ⟨ih 0, ih 1⟩
    | guarded _ => exact ⟨rfl, ih 0, ih 1, ih 2⟩

/-- The same encoded Unit-signature checker decides actual equality for every
ambient role type with three distinct roles and every concrete chosen owner. -/
theorem equation_iff {Role : Type u} [DecidableEq Role] (three : Fin 3 ↪ Role)
    (owner observer : Role) (hne : observer ≠ owner) (left right : Tree) :
    Owner.Term.equationB true (left.withOwner false) (right.withOwner false) = true ↔
      ∀ valuation : ℕ → WinnerSet Role,
        (left.withOwner owner).eval valuation = (right.withOwner owner).eval valuation := by
  have he : Owner.Term.equationB true (left.withOwner false) (right.withOwner false) =
      Owner.Term.equationB observer (left.withOwner owner) (right.withOwner owner) := by
    unfold Owner.Term.equationB
    rw [Owner.Term.guards_withOwner_outsider left owner observer hne,
      Owner.Term.guards_withOwner_outsider right owner observer hne]
  rw [he]
  exact Owner.Term.equationB_correct three owner observer hne
    (left.withOwner owner) (right.withOwner owner) (ownersIn_withOwner owner left) (ownersIn_withOwner owner right)

end KFOL.Complexity.OwnerTermFrontend
