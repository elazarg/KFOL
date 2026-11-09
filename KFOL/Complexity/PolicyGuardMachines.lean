module
public import KFOL.Complexity.PolicyTermMachines
public import KFOL.Complexity.FiniteFoldRuntime
public import KFOL.Policies.Recognition
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite
@[expose] public section
namespace KFOL.Complexity.PolicyGuardMachines
open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.Policies KFOL.FiniteTermCode
variable {Role Label : Type} [Fintype Role] [Fintype Label] [DecidableEq Role] [DecidableEq Label]
noncomputable abbrev passEncoding : (Label × ℕ) ↪ List Bool := encPair (encFinite Label) encNat
noncomputable abbrev rawGuardEncoding : (ℕ × (List ℕ × List (Label × ℕ))) ↪ List Bool :=
  encPair encNat (encPair (encList encNat) (encList passEncoding))
def guardView (g : Guard Label ℕ) := (g.source, g.many, g.passes)
noncomputable def guardEncoding : Guard Label ℕ ↪ List Bool :=
  ⟨fun g => rawGuardEncoding (guardView g), by
    intro x y h
    have he := rawGuardEncoding.injective h
    cases x; cases y
    simpa only [guardView, Guard.mk.injEq, Prod.mk.injEq] using he⟩
omit [DecidableEq Label] in
theorem guardView_polyTime : ComputableInPolyTime (guardView (Label := Label)) guardEncoding rawGuardEncoding :=
  .of_eq (fun _ => rfl)

omit [DecidableEq Label] in
theorem addMany_polyTime : ComputableInPolyTime
    (fun p : ℕ × Guard Label ℕ => p.2.addMany p.1) (encPair encNat guardEncoding) guardEncoding := by
  have hj := fst encNat (guardEncoding (Label := Label))
  have hg := guardView_polyTime.comp (snd encNat (guardEncoding (Label := Label)))
  have hs := (fst encNat (encPair (encList encNat) (encList (passEncoding (Label := Label))))).comp hg
  have hm := (fst (encList encNat) (encList (passEncoding (Label := Label)))).comp ((snd encNat _).comp hg)
  have hp := (snd (encList encNat) (encList (passEncoding (Label := Label)))).comp ((snd encNat _).comp hg)
  exact (hs.prod ((cons' hj hm).prod hp)).of_enc_eq (fun _ => rfl)

omit [DecidableEq Label] in
theorem addPass_polyTime : ComputableInPolyTime
    (fun p : (Label × ℕ) × Guard Label ℕ => p.2.addPass p.1.1 p.1.2)
    (encPair passEncoding guardEncoding) guardEncoding := by
  have hj := fst (passEncoding (Label := Label)) (guardEncoding (Label := Label))
  have hg := guardView_polyTime.comp (snd (passEncoding (Label := Label)) (guardEncoding (Label := Label)))
  have hs := (fst encNat (encPair (encList encNat) (encList (passEncoding (Label := Label))))).comp hg
  have hm := (fst (encList encNat) (encList (passEncoding (Label := Label)))).comp ((snd encNat _).comp hg)
  have hp := (snd (encList encNat) (encList (passEncoding (Label := Label)))).comp ((snd encNat _).comp hg)
  exact (hs.prod (hm.prod (cons' hj hp))).of_enc_eq (fun _ => rfl)

omit [DecidableEq Label] in
theorem labelsAt_polyTime : ComputableInPolyTime
    (fun p : ℕ × Guard Label ℕ => p.2.labelsAt p.1) (encPair encNat guardEncoding) (encList (encFinite Label)) := by
  let input := encPair encNat (guardEncoding (Label := Label))
  have hpasses : ComputableInPolyTime (fun p : ℕ × Guard Label ℕ => p.2.passes) input (encList passEncoding) :=
    (snd _ _).comp ((snd _ _).comp (guardView_polyTime.comp (snd _ _)))
  have hp : ComputableInPolyTime (fun p : (ℕ × Guard Label ℕ) × (Label × ℕ) => p.2.2)
      (encPair input passEncoding) encNat := by fun_prop
  have hi : ComputableInPolyTime (fun p : (ℕ × Guard Label ℕ) × (Label × ℕ) => p.1.1)
      (encPair input passEncoding) encNat := by fun_prop
  have hfiltered := filterWithInput (test := fun (p : ℕ × Guard Label ℕ) (test : Label × ℕ) => decide (test.2 = p.1))
    hpasses (decide_eq' hp hi)
  exact mapWithInput (f := fun (_ : ℕ × Guard Label ℕ) (test : Label × ℕ) => test.1)
    hfiltered ((fst (encFinite Label) encNat).comp (snd input passEncoding))

noncomputable def ofMembership (f : Role → Bool) : Finset Role := Finset.univ.filter (fun r => f r = true)

omit [DecidableEq Label] in
theorem blockingUnion_polyTime (D : Label → Finset Role) : ComputableInPolyTime (blockingUnion D)
    (encList (encFinite Label)) (encFinite (Finset Role)) := by
  have hmem : ComputableInPolyTime (fun labels : List Label => fun r : Role => labels.any (fun d => decide (r ∈ D d)))
      (encList (encFinite Label)) (encPi encBool) := by
    apply ComputableInPolyTime.pi
    intro r
    exact anyWithInput (test := fun (_ : List Label) d => decide (r ∈ D d)) id'
      ((ComputableInPolyTime.of_finite (fun d : Label => decide (r ∈ D d))
        (encIn := encFinite Label) (encOut := encBool)).comp (snd _ _))
  have h := (ComputableInPolyTime.of_finite (ofMembership (Role := Role))
    (encIn := encPi encBool) (encOut := encFinite (Finset Role))).comp hmem
  convert h using 1
  funext labels
  apply Finset.ext
  intro r
  simp only [Function.comp_def, ofMembership, Finset.mem_filter, Finset.mem_univ, true_and, List.any_eq_true,
    decide_eq_true_eq, mem_blockingUnion]

omit [DecidableEq Label] in
theorem blockingAt_polyTime (D : Label → Finset Role) : ComputableInPolyTime
    (fun p : ℕ × Guard Label ℕ => p.2.blockingAt D p.1) (encPair encNat guardEncoding) (encFinite (Finset Role)) :=
  (blockingUnion_polyTime D).comp labelsAt_polyTime

omit [DecidableEq Label] in
theorem normalizeAt_polyTime (D : Label → Finset Role) (top : Finset Role) : ComputableInPolyTime
    (fun p : ℕ × Guard Label ℕ => p.2.normalizeAt D top p.1) (encPair encNat guardEncoding) guardEncoding := by
  have htest := decide_eq' (blockingAt_polyTime D) (const top)
  have h := htest.ite addMany_polyTime (snd encNat (guardEncoding (Label := Label)))
  convert h using 1
  funext p
  simp only [Guard.normalizeAt, decide_eq_true_eq]



private def contains (p : ℕ × List ℕ) : Bool := p.2.any (fun j => decide (p.1 = j))
private theorem contains_polyTime : ComputableInPolyTime contains (encPair encNat (encList encNat)) encBool := by
  let input := encPair encNat (encList encNat)
  have hl := snd encNat (encList encNat)
  have hj : ComputableInPolyTime (fun p : (ℕ × List ℕ) × ℕ => p.1.1) (encPair input encNat) encNat := by fun_prop
  exact anyWithInput (test := fun (p : ℕ × List ℕ) j => decide (p.1 = j)) hl (decide_eq' hj (snd input encNat))
private theorem contains_eq (p : ℕ × List ℕ) : contains p = decide (p.1 ∈ p.2) := by
  apply Bool.eq_iff_iff.mpr
  simp only [contains, List.any_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨_, hm, he⟩ => he ▸ hm, fun hm => ⟨p.1, hm, rfl⟩⟩

omit [DecidableEq Label] in
private theorem source_polyTime : ComputableInPolyTime (fun g : Guard Label ℕ => g.source) guardEncoding encNat :=
  (fst _ _).comp guardView_polyTime
omit [DecidableEq Label] in
private theorem many_polyTime : ComputableInPolyTime (fun g : Guard Label ℕ => g.many) guardEncoding (encList encNat) :=
  (fst _ _).comp ((snd _ _).comp guardView_polyTime)
omit [DecidableEq Label] in
private theorem passes_polyTime : ComputableInPolyTime (fun g : Guard Label ℕ => g.passes) guardEncoding (encList passEncoding) :=
  (snd _ _).comp ((snd _ _).comp guardView_polyTime)

omit [DecidableEq Label] in
theorem dominates_polyTime (D : Label → Finset Role) : ComputableInPolyTime
    (fun p : Guard Label ℕ × Guard Label ℕ => dominatesB D p.1 p.2)
    (encPair guardEncoding guardEncoding) encBool := by
  let input := encPair (guardEncoding (Label := Label)) (guardEncoding (Label := Label))
  have hw := fst (guardEncoding (Label := Label)) (guardEncoding (Label := Label))
  have hs := snd (guardEncoding (Label := Label)) (guardEncoding (Label := Label))
  have hsw := source_polyTime.comp hw
  have hss := source_polyTime.comp hs
  have hmw := many_polyTime.comp hw
  have hms := many_polyTime.comp hs
  have hpw := passes_polyTime.comp hw
  have hi := snd input encNat
  have hms' := hms.comp (fst input encNat)
  have hm := contains_polyTime.comp (hi.prod hms')
  have hmany := allWithInput (test := fun (p : Guard Label ℕ × Guard Label ℕ) j => contains (j, p.2.many)) hmw hm
  let inner := encPair input (passEncoding (Label := Label))
  have hj : ComputableInPolyTime (fun p : (Guard Label ℕ × Guard Label ℕ) × (Label × ℕ) => p.2.2) inner encNat := by fun_prop
  have hd : ComputableInPolyTime (fun p : (Guard Label ℕ × Guard Label ℕ) × (Label × ℕ) => p.2.1) inner (encFinite Label) := by fun_prop
  have hstrong : ComputableInPolyTime (fun p : (Guard Label ℕ × Guard Label ℕ) × (Label × ℕ) => p.1.2) inner guardEncoding := by fun_prop
  have hblock := (blockingAt_polyTime D).comp (hj.prod hstrong)
  have hsubset := (ComputableInPolyTime.of_finite (fun p : Label × Finset Role => decide (D p.1 ⊆ p.2))
    (encIn := encPair (encFinite Label) (encFinite (Finset Role))) (encOut := encBool)).comp (hd.prod hblock)
  have hmember := contains_polyTime.comp (hj.prod (many_polyTime.comp hstrong))
  have heq := decide_eq' hj (source_polyTime.comp hstrong)
  have hpass := allWithInput (test := fun (p : Guard Label ℕ × Guard Label ℕ) (test : Label × ℕ) =>
    contains (test.2, p.2.many) || decide (test.2 = p.2.source) || decide (D test.1 ⊆ p.2.blockingAt D test.2)) hpw
    (bool_or.comp ((bool_or.comp (hmember.prod heq)).prod hsubset))
  have h := bool_and' (bool_and' (decide_eq' hsw hss) hmany) hpass
  convert h using 1
  funext p
  apply Bool.eq_iff_iff.mpr
  simp only [dominatesB, Function.comp_def, contains_eq, Bool.and_eq_true, Bool.or_eq_true,
    List.all_eq_true, decide_eq_true_eq, or_assoc]

omit [DecidableEq Label] in
theorem covers_polyTime (D : Label → Finset Role) : ComputableInPolyTime
    (fun p : List (Guard Label ℕ) × List (Guard Label ℕ) => coversB D p.1 p.2)
    (encPair (encList guardEncoding) (encList guardEncoding)) encBool := by
  let input := encPair (encList (guardEncoding (Label := Label))) (encList (guardEncoding (Label := Label)))
  let inner := encPair input (guardEncoding (Label := Label))
  have hl := fst (encList (guardEncoding (Label := Label))) (encList (guardEncoding (Label := Label)))
  have hr : ComputableInPolyTime (fun p : (List (Guard Label ℕ) × List (Guard Label ℕ)) × Guard Label ℕ => p.1.2)
      inner (encList guardEncoding) := by fun_prop
  have hstrong := snd inner (guardEncoding (Label := Label))
  have hweak : ComputableInPolyTime (fun p : ((List (Guard Label ℕ) × List (Guard Label ℕ)) × Guard Label ℕ) × Guard Label ℕ => p.1.2)
      (encPair inner guardEncoding) guardEncoding := by fun_prop
  have hdom := (dominates_polyTime D).comp (hstrong.prod hweak)
  have hany := anyWithInput (test := fun (p : (List (Guard Label ℕ) × List (Guard Label ℕ)) × Guard Label ℕ) strong => dominatesB D strong p.2) hr hdom
  exact allWithInput (test := fun (p : List (Guard Label ℕ) × List (Guard Label ℕ)) weak => p.2.any (fun strong => dominatesB D strong weak)) hl hany
end KFOL.Complexity.PolicyGuardMachines
