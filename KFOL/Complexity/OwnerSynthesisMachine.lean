module

public import KFOL.Complexity.OwnerCheckMachine
public import KFOL.Complexity.OwnerPathMachines
public import KFOL.Complexity.OptionTraversal

/-! # Native owner-table synthesis from the actual recorded saturation run -/

@[expose] public section

namespace KFOL.Complexity.OwnerRuntime

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.Algorithms

variable {Role : Type} [Fintype Role]

noncomputable abbrev termEncoding := OwnerTermMachines.termEncoding (Role := Role)

noncomputable def finishTerm (owner : Role) (context : Context) (state : RawGuard) :
    Option (Owner.Term Role ℕ) :=
  if permitted context.1 context.2.1 state then
    some (Owner.Term.step (.var context.2.1) (.var context.1.1))
  else (finishWitness context state).map (fun z =>
    Owner.Term.guarded owner (.var context.1.1) (.var context.2.1) (.var z))

theorem finishTerm_polyTime (owner : Role) : ComputableInPolyTime
    (fun p : FinishInput => finishTerm owner p.1 p.2)
    finishEncoding (encOption termEncoding) := by
  have ht : ComputableInPolyTime (fun p : FinishInput => p.1.1) finishEncoding tableEncoding := by fun_prop
  have hj : ComputableInPolyTime (fun p : FinishInput => p.1.2.1) finishEncoding encNat := by fun_prop
  have hr : ComputableInPolyTime (fun p : FinishInput => p.1.1.1) finishEncoding encNat := by fun_prop
  have hs := snd contextEncoding guardEncoding
  have htest := permitted_polyTime.comp (ht.prod (hj.prod hs))
  have hjv := (OwnerTermMachines.var_polyTime (Role := Role)).comp hj
  have hrv := (OwnerTermMachines.var_polyTime (Role := Role)).comp hr
  have hfirst := (optionSome (termEncoding (Role := Role))).comp (OwnerTermMachines.step_polyTime.comp (hjv.prod hrv))
  have hroot : ComputableInPolyTime (fun p : FinishInput × ℕ => p.1.1.1.1)
      (encPair finishEncoding encNat) encNat := by fun_prop
  have houtput : ComputableInPolyTime (fun p : FinishInput × ℕ => p.1.1.2.1)
      (encPair finishEncoding encNat) encNat := by fun_prop
  have hz := snd finishEncoding encNat
  have hguarded := (OwnerTermMachines.guarded_polyTime owner).comp
    (((OwnerTermMachines.var_polyTime (Role := Role)).comp hroot).prod
      (((OwnerTermMachines.var_polyTime (Role := Role)).comp houtput).prod ((OwnerTermMachines.var_polyTime (Role := Role)).comp hz)))
  have hsecond := finishWitness_polyTime.optionMapWithInput
    (f := fun (p : FinishInput) z => Owner.Term.guarded owner (.var p.1.1.1) (.var p.1.2.1) (.var z)) hguarded
  exact htest.ite hfirst hsecond

noncomputable def guardPath (owner : Role) (context : Context) : Option (Owner.Term Role ℕ) :=
  if context.2.1 = context.1.1 then some (.var context.1.1) else
    let result := run context
    (finishTerm owner context result.1).map (Owner.Term.pathTerm owner context.1.1 result.2)

theorem guardPath_polyTime (owner : Role) : ComputableInPolyTime
    (guardPath owner) contextEncoding (encOption termEncoding) := by
  have hj : ComputableInPolyTime (fun p : Context => p.2.1) contextEncoding encNat := by fun_prop
  have hr : ComputableInPolyTime (fun p : Context => p.1.1) contextEncoding encNat := by fun_prop
  have hroot := (optionSome (termEncoding (Role := Role))).comp ((OwnerTermMachines.var_polyTime (Role := Role)).comp hr)
  have hs := (fst guardEncoding (encList OwnerTermMachines.frameEncoding)).comp run_polyTime
  have hframes := (snd guardEncoding (encList OwnerTermMachines.frameEncoding)).comp run_polyTime
  have hfinish := (finishTerm_polyTime owner).comp (id'.prod hs)
  have hr' := hr.comp (fst contextEncoding (termEncoding (Role := Role)))
  have hf' := hframes.comp (fst contextEncoding (termEncoding (Role := Role)))
  have hfill := snd contextEncoding (termEncoding (Role := Role))
  have hbody := (OwnerTermMachines.pathTerm_polyTime owner).comp (hr'.prod (hf'.prod hfill))
  have hpath := hfinish.optionMapWithInput
    (f := fun (p : Context) fill => Owner.Term.pathTerm owner p.1.1 (run p).2 fill) hbody
  have h := (decide_eq' hj hr).ite hroot hpath
  convert h using 1
  funext context
  simp only [guardPath, decide_eq_true_eq, Function.comp_def]

omit [Fintype Role] in
private theorem joinPaths_fold (root : ℕ) (terms : List (Owner.Term Role ℕ)) :
    Owner.Term.joinPaths root terms = terms.foldr Owner.Term.step (.var root) := by
  induction terms with
  | nil => rfl
  | cons term terms ih => simp only [Owner.Term.joinPaths, List.foldr_cons, ih]

theorem joinPaths_polyTime : ComputableInPolyTime
    (fun p : ℕ × List (Owner.Term Role ℕ) => Owner.Term.joinPaths p.1 p.2)
    (encPair encNat (encList termEncoding)) termEncoding := by
  let input := encPair encNat (encList (termEncoding (Role := Role)))
  have hr := fst encNat (encList (termEncoding (Role := Role)))
  have hlist := snd encNat (encList (termEncoding (Role := Role)))
  have hreverse := (ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.listReverse (termEncoding (Role := Role)))).comp hlist
  have hs : ComputableInPolyTime
      (fun p : ((ℕ × List (Owner.Term Role ℕ)) × Owner.Term Role ℕ) × Owner.Term Role ℕ => p.1.2)
      (encPair (encPair input termEncoding) termEncoding) termEncoding := by fun_prop
  have ht := snd (encPair input (termEncoding (Role := Role))) (termEncoding (Role := Role))
  have hstep := OwnerTermMachines.step_polyTime.comp (ht.prod hs)
  have h := foldlWithInput_of_bounded_growth
    (list := fun p : ℕ × List (Owner.Term Role ℕ) => p.2.reverse)
    (init := fun p => (.var p.1 : Owner.Term Role ℕ))
    (step := fun _ state term => Owner.Term.step term state)
    ((OwnerTermMachines.var_polyTime (Role := Role)).comp hr) ⟨hreverse, hstep, inferInstance, inferInstance⟩
    (growth := fun p => (encList (termEncoding (Role := Role)) p.2).length +
      OwnerTermMachines.resetHeader (Role := Role))
    ⟨hlist.polyBounded_length.add (PolyBounded.const _), ?_⟩
  · convert h using 1
    funext p
    rw [List.foldl_reverse, joinPaths_fold]
  · intro p state term hterm
    have ht := SizedListEncoding.length_elem_le (encA := termEncoding)
      (encL := encList termEncoding) p.2 term (List.mem_reverse.mp hterm)
    have hl := OwnerTermMachines.length_step term state
    simp only [termEncoding] at *
    omega

noncomputable def synthesize (owner : Role) (input : ℕ × RawTable) : Option (Owner.Term Role ℕ) :=
  if check input then
    (input.2.2.mapM (fun p => guardPath owner (input.2, p))).map (Owner.Term.joinPaths input.2.1)
  else none

theorem synthesize_polyTime (owner : Role) : ComputableInPolyTime
    (synthesize owner) rawEncoding (encOption termEncoding) := by
  have hrecords : ComputableInPolyTime (fun p : ℕ × RawTable => p.2.2)
      rawEncoding (encList entryEncoding) := by fun_prop
  have htable : ComputableInPolyTime (fun p : (ℕ × RawTable) × RawEntry => p.1.2)
      (encPair rawEncoding entryEncoding) tableEncoding := by fun_prop
  have hrecord := snd rawEncoding entryEncoding
  have hentry := (guardPath_polyTime owner).comp (htable.prod hrecord)
  have hpaths := mapMWithInput_polyTime
    (f := fun (p : ℕ × RawTable) (entry : RawEntry) => guardPath owner (p.2, entry))
    hrecords hentry (.var 0 : Owner.Term Role ℕ)
  have hr : ComputableInPolyTime (fun p : (ℕ × RawTable) × List (Owner.Term Role ℕ) => p.1.2.1)
      (encPair rawEncoding (encList termEncoding)) encNat := by fun_prop
  have hl := snd rawEncoding (encList (termEncoding (Role := Role)))
  have hj := joinPaths_polyTime.comp (hr.prod hl)
  have hjoined := hpaths.optionMapWithInput
    (f := fun (p : ℕ × RawTable) terms => Owner.Term.joinPaths p.2.1 terms) hj
  exact check_polyTime.ite hjoined (const none)

end KFOL.Complexity.OwnerRuntime
