module

public import KFOL.Complexity.RecognitionMachine
public import KFOL.Complexity.TermMachine
public import KFOL.Reset.Realizability.Records
public import Mathlib.Data.List.GetD

/-! Native reset-table synthesis. Internal positions are bounded by physically
stored guard width; original sparse dictionary labels remain binary data. -/

@[expose] public section

namespace KFOL.Complexity.ResetSynthesis

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.Algorithms KFOL.Complexity.RawRecords

abbrev Context := List Record × (ℕ × List Bool)
abbrev contextEncoding := encPair (encList recordEncoding) (encPair encNat encBits)
abbrev orderEncoding := encList encUnary

/-- Root plus the actual previously added positions. Every loop traverses the
physical target-mask width, never a numeric variable-label maximum. -/
def reached (context : Context) (order : List ℕ) : List Bool :=
  (List.range context.2.2.length).map (fun i => decide (i = context.2.1) || order.any (fun j => decide (j = i)))

def ready (context : Context) (reached : List Bool) (position : ℕ) : Bool :=
  context.2.2.getD position false && !reached.getD position false &&
    context.1.any (fun record => decide (record.1 = position) && ReachMachine.subset record.2 reached)

def choose (context : Context) (order : List ℕ) : Option ℕ :=
  let current := reached context order
  (List.range context.2.2.length).find? (ready context current)

def advance (context : Context) (order : List ℕ) : List ℕ :=
  (choose context order).elim order (fun position => order ++ [position])

def run (context : Context) : List ℕ := (advance context)^[context.2.2.length] []

def contextView (d : GuardDescriptor) (root : Fin d.labels.length) (target : Finset (Fin d.labels.length)) : Context :=
  (d.records.map recordView, (root.val, Bitset.encode target))

theorem reached_view (d : GuardDescriptor) (root : Fin d.labels.length)
    (target : Finset (Fin d.labels.length)) (order : List (Fin d.labels.length)) :
    reached (contextView d root target) (order.map Fin.val) = Bitset.encode (insert root order.toFinset) := by
  apply List.ext_getElem (by simp [reached, contextView, Bitset.encode])
  intro i hi hi'
  have hin : i < d.labels.length := by simpa only [Bitset.encode, List.length_ofFn] using hi'
  let pos : Fin d.labels.length := ⟨i, hin⟩
  have hroot : i = root.val ↔ pos = root := by
    change pos.val = root.val ↔ pos = root
    exact Fin.ext_iff.symm
  have horder : (order.map Fin.val).any (fun j => decide (j = i)) = decide (pos ∈ order) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_map, Function.comp_apply, List.any_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨j, hj, he⟩
      have hp : j = pos := Fin.ext he
      exact hp ▸ hj
    · intro hp
      exact ⟨pos, hp, rfl⟩
  simp only [reached, contextView, List.getElem_map, List.getElem_range,
    Bitset.encode, List.getElem_ofFn]
  rw [horder]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, decide_eq_true_eq, Finset.mem_insert, List.mem_toFinset]
  exact or_congr hroot Iff.rfl

private theorem read_encode {n : ℕ} (A : Finset (Fin n)) (i : Fin n) :
    (Bitset.encode A).getD i.val false = decide (i ∈ A) := by
  simpa only [GuardWords.readBit, List.getD_eq_getElem?_getD] using Bitset.read_encode A i

theorem enabled_view (d : GuardDescriptor) (root position : Fin d.labels.length)
    (current : Finset (Fin d.labels.length)) :
    (d.records.map recordView).any (fun record => decide (record.1 = position.val) &&
      ReachMachine.subset record.2 (Bitset.encode current)) =
        true ↔ (d.table root).Enabled (current : Set (Fin d.labels.length)) position := by
  simp only [List.any_map, Function.comp_apply, recordView, Bool.and_eq_true, decide_eq_true_eq,
    ReachMachine.subset_encode, List.any_eq_true]
  rw [Reset.GuardTable.Enabled]
  constructor
  · rintro ⟨⟨j, A⟩, hr, hj, hA⟩
    have he : j = position := Fin.ext (of_decide_eq_true hj)
    subst j
    exact ⟨A, (GuardDescriptor.mem_guards d position A).mpr hr, hA⟩
  · rintro ⟨A, hA, hsub⟩
    exact ⟨(position, A), (GuardDescriptor.mem_guards d position A).mp hA, decide_eq_true rfl, hsub⟩

theorem ready_view (d : GuardDescriptor) (root : Fin d.labels.length)
    (target : Finset (Fin d.labels.length)) (order : List (Fin d.labels.length)) (position : Fin d.labels.length) :
    ready (contextView d root target) (reached (contextView d root target) (order.map Fin.val)) position.val =
      decide (position ∈ (d.table root).greedyCandidates target order) := by
  rw [reached_view]
  unfold ready contextView
  rw [read_encode, read_encode]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
  rw [enabled_view d root]
  rw [Reset.GuardTable.mem_greedyCandidates]
  simp only [decide_eq_false_iff_not, GuardDescriptor.table]
  tauto

/-- The native bounded scan picks the SAME least fresh enabled position as
the independent finite-set greedy algorithm. -/
theorem choose_view (d : GuardDescriptor) (root : Fin d.labels.length)
    (target : Finset (Fin d.labels.length)) (order : List (Fin d.labels.length)) :
    choose (contextView d root target) (order.map Fin.val) =
      if h : ((d.table root).greedyCandidates target order).Nonempty then
        some (((d.table root).greedyCandidates target order).min' h).val else none := by
  classical
  let candidates := (d.table root).greedyCandidates target order
  by_cases h : candidates.Nonempty
  · rw [dite_eq_left h]
    apply List.find?_range_eq_some.mpr
    refine ⟨?_, ?_, ?_⟩
    · exact (ready_view d root target order (candidates.min' h)).trans
        (decide_eq_true (Finset.min'_mem candidates h))
    · exact List.mem_range.mpr (by simpa only [contextView, Bitset.length_encode] using (candidates.min' h).isLt)
    · intro j hj
      have hjn : j < d.labels.length := lt_trans hj (candidates.min' h).isLt
      have hnot : ready (contextView d root target) (reached (contextView d root target) (order.map Fin.val)) j ≠ true := by
        intro hp
        have hmem : (⟨j, hjn⟩ : Fin d.labels.length) ∈ candidates := of_decide_eq_true
          ((ready_view d root target order ⟨j, hjn⟩).symm.trans hp)
        have hle := Finset.min'_le candidates _ hmem
        exact Nat.not_le_of_gt hj hle
      cases ht : ready (contextView d root target) (reached (contextView d root target) (order.map Fin.val)) j with
      | false => rfl
      | true => exact (hnot ht).elim
  · rw [dite_eq_right h]
    apply List.find?_eq_none.mpr
    intro j hj hp
    have hjn : j < d.labels.length := by simpa only [contextView, Bitset.length_encode, List.mem_range] using hj
    exact h ⟨⟨j, hjn⟩, of_decide_eq_true ((ready_view d root target order ⟨j, hjn⟩).symm.trans hp)⟩

theorem run_view (d : GuardDescriptor) (root : Fin d.labels.length)
    (target : Finset (Fin d.labels.length)) :
    run (contextView d root target) =
      ((d.table root).greedyOrder target d.labels.length).map Fin.val := by
  have h (k : ℕ) : (advance (contextView d root target))^[k] [] =
      ((d.table root).greedyOrder target k).map Fin.val := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      unfold advance
      rw [choose_view]
      rw [Reset.GuardTable.greedyOrder]
      split <;> simp [List.map_append]
  simpa only [run, contextView, Bitset.length_encode] using h d.labels.length


abbrev OrderInput := Context × List ℕ
abbrev orderInputEncoding := encPair contextEncoding orderEncoding

theorem reached_polyTime : ComputableInPolyTime
    (fun p : OrderInput => reached p.1 p.2) orderInputEncoding encBits := by
  have htarget : ComputableInPolyTime (fun p : OrderInput => p.1.2.2) orderInputEncoding encBits := by fun_prop
  have hwidth := length_bits.comp htarget
  have hrange := ComputableInPolyTime.range.comp hwidth
  let scanEncoding := encPair orderInputEncoding encUnary
  have hi := snd orderInputEncoding encUnary
  have hr : ComputableInPolyTime (fun p : OrderInput × ℕ => p.1.1.2.1) scanEncoding encNat := by fun_prop
  have heq := decide_eq' (unary_to_binary.comp hi) hr
  have hs : ComputableInPolyTime (fun p : OrderInput × ℕ => p.1.2) scanEncoding orderEncoding := by fun_prop
  have hj := snd scanEncoding encUnary
  have hi' : ComputableInPolyTime (fun p : (OrderInput × ℕ) × ℕ => p.1.2)
      (encPair scanEncoding encUnary) encUnary := by fun_prop
  have hmem := anyWithInput (test := fun (p : OrderInput × ℕ) j => decide (j = p.2)) hs (decide_eq' hj hi')
  have hmap := mapWithInput (f := fun (p : OrderInput) i =>
    decide (i = p.1.2.1) || p.2.any (fun j => decide (j = i))) hrange (bool_or.comp (heq.prod hmem))
  exact (bits_encList_polyTime encBool).2.comp hmap

abbrev ReadyInput := (Context × List Bool) × ℕ
abbrev readyInputEncoding := encPair (encPair contextEncoding encBits) encUnary

theorem ready_polyTime : ComputableInPolyTime
    (fun p : ReadyInput => ready p.1.1 p.1.2 p.2) readyInputEncoding encBool := by
  have hi := snd (encPair contextEncoding encBits) encUnary
  have ht : ComputableInPolyTime (fun p : ReadyInput => p.1.1.2.2) readyInputEncoding encBits := by fun_prop
  have hc : ComputableInPolyTime (fun p : ReadyInput => p.1.2) readyInputEncoding encBits := by fun_prop
  have hin := bitsGetDWithInput ht hi false
  have hfresh := bool_not.comp (bitsGetDWithInput hc hi false)
  have hrecords : ComputableInPolyTime (fun p : ReadyInput => p.1.1.1)
      readyInputEncoding (encList recordEncoding) := by fun_prop
  let scanEncoding := encPair readyInputEncoding recordEncoding
  have ho : ComputableInPolyTime (fun p : ReadyInput × Record => p.2.1) scanEncoding encNat := by fun_prop
  have hi' : ComputableInPolyTime (fun p : ReadyInput × Record => p.1.2) scanEncoding encUnary := by fun_prop
  have hg : ComputableInPolyTime (fun p : ReadyInput × Record => p.2.2) scanEncoding encBits := by fun_prop
  have hs : ComputableInPolyTime (fun p : ReadyInput × Record => p.1.1.2) scanEncoding encBits := by fun_prop
  have hp := bool_and' (decide_eq' ho (unary_to_binary.comp hi')) (ReachMachine.subset_polyTime.comp (hg.prod hs))
  have hany := anyWithInput (test := fun (p : ReadyInput) record =>
    decide (record.1 = p.2) && ReachMachine.subset record.2 p.1.2) hrecords hp
  exact bool_and' (bool_and' hin hfresh) hany

theorem choose_polyTime : ComputableInPolyTime
    (fun p : OrderInput => choose p.1 p.2) orderInputEncoding (encOption encUnary) := by
  have ht : ComputableInPolyTime (fun p : OrderInput => p.1.2.2) orderInputEncoding encBits := by fun_prop
  have hrange := ComputableInPolyTime.range.comp (length_bits.comp ht)
  have hc : ComputableInPolyTime (fun p : OrderInput × ℕ => p.1.1)
      (encPair orderInputEncoding encUnary) contextEncoding := by fun_prop
  have hs := reached_polyTime.comp (fst orderInputEncoding encUnary)
  have hi := snd orderInputEncoding encUnary
  have hp := ready_polyTime.comp ((hc.prod hs).prod hi)
  exact findWithInput (test := fun (p : OrderInput) i => ready p.1 (reached p.1 p.2) i) hrange hp

theorem advance_polyTime : ComputableInPolyTime
    (fun p : OrderInput => advance p.1 p.2) orderInputEncoding orderEncoding := by
  have horder := snd contextEncoding orderEncoding
  have hs : ComputableInPolyTime (fun p : OrderInput × ℕ => p.1.2)
      (encPair orderInputEncoding encUnary) orderEncoding := by fun_prop
  have hi := snd orderInputEncoding encUnary
  exact choose_polyTime.optionElimWithInput
    (body := fun (p : OrderInput) i => p.2 ++ [i]) horder (listAppend' hs (cons' hi (const [])))

private theorem advance_growth (context : Context) (order : List ℕ) :
    (orderEncoding (advance context order)).length ≤ (orderEncoding order).length + 2 * context.2.2.length + 1 := by
  unfold advance
  cases hc : choose context order with
  | none => simp only [Option.elim_none]; omega
  | some i =>
    have hi : i < context.2.2.length := List.mem_range.mp (List.mem_of_find?_eq_some hc)
    simp only [Option.elim_some, orderEncoding, encList_append, List.length_append,
      encList_cons, encList_nil, List.append_nil, length_frame, encUnary_apply, List.length_replicate]
    omega

theorem run_polyTime : ComputableInPolyTime run contextEncoding orderEncoding := by
  have ht : ComputableInPolyTime (fun context : Context => context.2.2) contextEncoding encBits := by fun_prop
  have hcount := length_bits.comp ht
  have hbound : PolyBounded (fun context : Context => (contextEncoding context).length)
      (fun context => 2 * context.2.2.length + 1) :=
    ((PolyBounded.const 2).mul hcount.polyBounded).add (PolyBounded.const 1)
  exact ComputableInPolyTime.iterateWith_of_bounded_growth id' hcount (const []) advance_polyTime hbound advance_growth


abbrev pathEncoding := encPair encNat (encList encNat)

private theorem length_var (j : ℕ) : (TermMachine.termEncoding (.var j)).length = 2 * (encNat j).length + 3 := by
  simp [TermMachine.termEncoding, TermCode.encode, Words.delimit_length, encNat_apply, Words.BinaryNatCode.encode]

private theorem length_step (s t : Reset.Term ℕ) :
    (TermMachine.termEncoding (Reset.Term.step s t)).length =
      1 + (TermMachine.termEncoding s).length + (TermMachine.termEncoding t).length := by
  change (TermCode.encode (Reset.Term.step s t)).length = 1 + (TermCode.encode s).length + (TermCode.encode t).length
  rw [TermCode.encode_step, List.length_cons, List.length_append]
  omega

/-- The actual primitive left-associated path constructor, with original
binary variable names and no duplicated recursive continuation. -/
theorem pathTerm_polyTime : ComputableInPolyTime
    (fun p : ℕ × List ℕ => Reset.Term.pathTerm p.1 p.2) pathEncoding TermMachine.termEncoding := by
  have hr := fst encNat (encList encNat)
  have hl := snd encNat (encList encNat)
  have htail := (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.tail (encA := encNat) (encL := encList encNat))).comp hl
  have hhead := (headD (encA := encNat) (encL := encList encNat) 0).comp hl
  have hinit := TermMachine.var_polyTime.comp hhead
  have hstate : ComputableInPolyTime
      (fun p : ((ℕ × List ℕ) × Reset.Term ℕ) × ℕ => p.1.2)
      (encPair (encPair pathEncoding TermMachine.termEncoding) encNat) TermMachine.termEncoding := by fun_prop
  have hj := snd (encPair pathEncoding TermMachine.termEncoding) encNat
  have hstep := TermMachine.node_polyTime.comp (hstate.prod (TermMachine.var_polyTime.comp hj))
  have hfold := foldlWithInput_of_bounded_growth
    (list := fun p : ℕ × List ℕ => p.2.tail)
    (init := fun p => (.var (p.2.headD 0) : Reset.Term ℕ))
    (step := fun _ state j => Reset.Term.step state (.var j))
    hinit ⟨htail, hstep, inferInstance, inferInstance⟩
    (growth := fun p => 2 * (encList encNat p.2).length + 4)
    ⟨((PolyBounded.const 2).mul hl.polyBounded_length).add (PolyBounded.const 4), ?_⟩
  · have hroot := TermMachine.var_polyTime.comp hr
    have hnonempty := TermMachine.node_polyTime.comp (hfold.prod hroot)
    have hempty := (ComputableInPolyTime.of_tidy
      (ComputableTidilyInPolyTime.listIsEmpty (encA := encNat) (encL := encList encNat))).comp hl
    have h := hempty.ite hroot hnonempty
    convert h using 1
    funext p
    rcases p with ⟨root, positions⟩
    dsimp only [Function.comp_def]
    cases positions <;> rfl
  · intro p state j hjmem
    have hmem : j ∈ p.2 := List.mem_of_mem_tail hjmem
    have hb := SizedListEncoding.length_elem_le (encA := encNat) (encL := encList encNat) p.2 j hmem
    rw [length_step, length_var]
    omega

theorem joinPaths_polyTime : ComputableInPolyTime
    (fun p : ℕ × List (Reset.Term ℕ) => Reset.Term.joinPaths p.1 p.2)
    (encPair encNat (encList TermMachine.termEncoding)) TermMachine.termEncoding := by
  let input := encPair encNat (encList TermMachine.termEncoding)
  have hr := fst encNat (encList TermMachine.termEncoding)
  have hterms := snd encNat (encList TermMachine.termEncoding)
  have hreverse := (ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.listReverse TermMachine.termEncoding)).comp hterms
  have hs : ComputableInPolyTime
      (fun p : ((ℕ × List (Reset.Term ℕ)) × Reset.Term ℕ) × Reset.Term ℕ => p.1.2)
      (encPair (encPair input TermMachine.termEncoding) TermMachine.termEncoding) TermMachine.termEncoding := by fun_prop
  have ht := snd (encPair input TermMachine.termEncoding) TermMachine.termEncoding
  have hstep := TermMachine.node_polyTime.comp (ht.prod hs)
  have h := foldlWithInput_of_bounded_growth
    (list := fun p : ℕ × List (Reset.Term ℕ) => p.2.reverse)
    (init := fun p => (.var p.1 : Reset.Term ℕ))
    (step := fun _ state term => Reset.Term.step term state)
    (TermMachine.var_polyTime.comp hr) ⟨hreverse, hstep, inferInstance, inferInstance⟩
    (growth := fun p => (encList TermMachine.termEncoding p.2).length + 1)
    ⟨hterms.polyBounded_length.add (PolyBounded.const 1), ?_⟩
  · convert h using 1
    funext p
    rw [List.foldl_reverse]
    rfl
  · intro p state term hterm
    have hb := SizedListEncoding.length_elem_le (encA := TermMachine.termEncoding)
      (encL := encList TermMachine.termEncoding) p.2 term (List.mem_reverse.mp hterm)
    rw [length_step]
    omega


/-- Physically insert the output position into its prerequisite mask. -/
def target (record : Record) : List Bool :=
  (List.range record.2.length).map (fun i => record.2.getD i false || decide (i = record.1))

theorem target_polyTime : ComputableInPolyTime target recordEncoding encBits := by
  have hm := snd encNat encBits
  have hrange := ComputableInPolyTime.range.comp (length_bits.comp hm)
  have hw : ComputableInPolyTime (fun p : Record × ℕ => p.1.2) (encPair recordEncoding encUnary) encBits := by fun_prop
  have hi := snd recordEncoding encUnary
  have hj : ComputableInPolyTime (fun p : Record × ℕ => p.1.1) (encPair recordEncoding encUnary) encNat := by fun_prop
  have hbit := bool_or.comp ((bitsGetDWithInput hw hi false).prod (decide_eq' (unary_to_binary.comp hi) hj))
  have hmap := mapWithInput (f := fun (record : Record) i => record.2.getD i false || decide (i = record.1)) hrange hbit
  exact (bits_encList_polyTime encBool).2.comp hmap

theorem target_view {n : ℕ} (record : GuardRecord.Record n) : target (recordView record) = Bitset.encode (insert record.1 record.2) := by
  apply List.ext_getElem (by simp [target, recordView, Bitset.encode])
  intro i hi hi'
  have hin : i < n := by simpa only [Bitset.encode, List.length_ofFn] using hi'
  let pos : Fin n := ⟨i, hin⟩
  simp only [target, recordView, List.getElem_map, List.getElem_range, Bitset.encode, List.getElem_ofFn]
  change ((Bitset.encode record.2).getD i false || decide (i = record.1.val)) = decide (pos ∈ insert record.1 record.2)
  rw [read_encode record.2 pos]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, decide_eq_true_eq, Finset.mem_insert]
  have he : i = record.1.val ↔ pos = record.1 := by
    change pos.val = record.1.val ↔ pos = record.1
    exact Fin.ext_iff.symm
  rw [he]
  tauto

private theorem labelLookup_polyTime : ComputableInPolyTime
    (fun p : List ℕ × ℕ => p.1.getD p.2 0) (encPair (encList encNat) encNat) encNat :=
  .of_tidy (ComputableTidilyInPolyTime.listGetD_binary 0
    (ComputableTidilyInPolyTime.fst (encList encNat) encNat)
    (ComputableTidilyInPolyTime.snd (encList encNat) encNat))

def labels (dictionary order : List ℕ) : List ℕ := order.map (fun position => dictionary.getD position 0)

theorem labels_polyTime : ComputableInPolyTime
    (fun p : List ℕ × List ℕ => labels p.1 p.2)
    (encPair (encList encNat) orderEncoding) (encList encNat) := by
  let input := encPair (encList encNat) orderEncoding
  have hl := snd (encList encNat) orderEncoding
  have hd : ComputableInPolyTime (fun p : (List ℕ × List ℕ) × ℕ => p.1.1)
      (encPair input encUnary) (encList encNat) := by fun_prop
  have hi := snd input encUnary
  have hread := (listGetD (encA := encNat) (encL := encList encNat) 0).comp (hd.prod hi)
  exact mapWithInput (f := fun (p : List ℕ × List ℕ) i => p.1.getD i 0) hl hread

abbrev PathRequest := Data × (ℕ × Record)
abbrev pathRequestEncoding := encPair dataEncoding (encPair encNat recordEncoding)

def pathContext (input : PathRequest) : Context := (input.1.2, (input.2.1, target input.2.2))

def path (input : PathRequest) : Reset.Term ℕ :=
  Reset.Term.pathTerm (input.1.1.getD input.2.1 0) (labels input.1.1 (run (pathContext input)).reverse)

theorem path_polyTime : ComputableInPolyTime path pathRequestEncoding TermMachine.termEncoding := by
  have hd : ComputableInPolyTime (fun p : PathRequest => p.1.1) pathRequestEncoding (encList encNat) := by fun_prop
  have hr : ComputableInPolyTime (fun p : PathRequest => p.2.1) pathRequestEncoding encNat := by fun_prop
  have hroot := labelLookup_polyTime.comp (hd.prod hr)
  have hrecords : ComputableInPolyTime (fun p : PathRequest => p.1.2)
      pathRequestEncoding (encList recordEncoding) := by fun_prop
  have hrecord : ComputableInPolyTime (fun p : PathRequest => p.2.2) pathRequestEncoding recordEncoding := by fun_prop
  have hcontext := hrecords.prod (hr.prod (target_polyTime.comp hrecord))
  have horder := run_polyTime.comp hcontext
  have hreverse := (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.listReverse encUnary)).comp horder
  have hlabels := labels_polyTime.comp (hd.prod hreverse)
  exact pathTerm_polyTime.comp (hroot.prod hlabels)


private theorem relabel_fold {Var Var' : Type*} (f : Var → Var') (positions : List Var) (t : Reset.Term Var) :
    (positions.foldl (fun term i => Reset.Term.step term (.var i)) t).relabel f =
      (positions.map f).foldl (fun term i => Reset.Term.step term (.var i)) (t.relabel f) := by
  induction positions generalizing t with
  | nil => rfl
  | cons i positions ih =>
    rw [List.foldl_cons, ih, Reset.Term.relabel_step]
    rfl

theorem relabel_pathTerm {Var Var' : Type*} (f : Var → Var') (root : Var) (positions : List Var) :
    (Reset.Term.pathTerm root positions).relabel f = Reset.Term.pathTerm (f root) (positions.map f) := by
  cases positions with
  | nil => rfl
  | cons i positions =>
    rw [Reset.Term.pathTerm, Reset.Term.relabel_step, relabel_fold]
    rfl

theorem path_view (d : GuardDescriptor) (root : Fin d.labels.length)
    (record : GuardRecord.Record d.labels.length) :
    path (view d, (root.val, recordView record)) =
      (Reset.Term.pathTerm root ((d.table root).greedyOrder (insert record.1 record.2) d.labels.length).reverse).relabel d.labels.get := by
  have hcontext : pathContext (view d, (root.val, recordView record)) = contextView d root (insert record.1 record.2) := by
    unfold pathContext contextView view
    rw [target_view]
  have hlabel (i : Fin d.labels.length) : d.labels.getD i.val 0 = d.labels.get i := by
    rw [List.getD_eq_getElem _ _ i.isLt]
    rfl
  unfold path
  rw [hcontext, run_view, relabel_pathTerm]
  change Reset.Term.pathTerm (d.labels.getD root.val 0)
    (labels d.labels ((((d.table root).greedyOrder (insert record.1 record.2) d.labels.length).map Fin.val).reverse)) = _
  rw [hlabel]
  congr 1
  simp only [labels, List.map_reverse, List.map_map, Function.comp_def, hlabel]

/-- Empty-mask discovery, independent of any guessed root convention. -/
def emptyMask (word : List Bool) : Bool := ReachMachine.subset word (List.replicate word.length false)

theorem emptyMask_polyTime : ComputableInPolyTime emptyMask encBits encBool :=
  ReachMachine.subset_polyTime.comp (id'.prod ((bitsReplicate false).comp length_bits))

theorem emptyMask_encode {n : ℕ} (A : Finset (Fin n)) : emptyMask (Bitset.encode A) = decide (A = ∅) := by
  simp only [emptyMask, Bitset.length_encode, ReachMachine.empty_encode, ReachMachine.subset_encode, Finset.subset_empty]

def findRoot (records : List Record) : Option ℕ :=
  (records.find? (fun record => emptyMask record.2)).map Prod.fst

theorem findRoot_polyTime : ComputableInPolyTime findRoot (encList recordEncoding) (encOption encNat) := by
  have hw : ComputableInPolyTime (fun p : List Record × Record => p.2.2)
      (encPair (encList recordEncoding) recordEncoding) encBits := by fun_prop
  have ht : ComputableInPolyTime (fun p : List Record × Record => emptyMask p.2.2)
      (encPair (encList recordEncoding) recordEncoding) encBool := emptyMask_polyTime.comp hw
  have hf := findWithInput (test := fun (_ : List Record) record => emptyMask record.2) id' ht
  have ho := fst encNat encBits
  exact hf.optionMapWithInput (f := fun (_ : List Record) record => record.1)
    (ho.comp (snd (encList recordEncoding) recordEncoding))

theorem findRoot_view (d : GuardDescriptor) : findRoot (d.records.map recordView) = d.root?.map Fin.val := by
  unfold findRoot GuardDescriptor.root?
  have hp : (fun record : GuardRecord.Record d.labels.length => emptyMask (recordView record).2) =
      (fun record => decide (record.2 = ∅)) := by
    funext record
    exact emptyMask_encode record.2
  rw [List.find?_map]
  change ((d.records.find? (fun record => emptyMask (recordView record).2)).map recordView).map Prod.fst = _
  rw [hp]
  simp only [Option.map_map]
  rfl

def rawSynthesize (data : Data) : Option (Reset.Term ℕ) :=
  (findRoot data.2).map (fun root => Reset.Term.joinPaths (data.1.getD root 0)
    (data.2.map (fun record => path (data, (root, record)))))

theorem rawSynthesize_polyTime : ComputableInPolyTime rawSynthesize dataEncoding (encOption TermMachine.termEncoding) := by
  have hrecords := snd (encList encNat) (encList recordEncoding)
  have hr := findRoot_polyTime.comp hrecords
  let input := encPair dataEncoding encNat
  have hd : ComputableInPolyTime (fun p : (Data × ℕ) × Record => p.1.1)
      (encPair input recordEncoding) dataEncoding := by fun_prop
  have hroot : ComputableInPolyTime (fun p : (Data × ℕ) × Record => p.1.2)
      (encPair input recordEncoding) encNat := by fun_prop
  have hrecord := snd input recordEncoding
  have hpath := path_polyTime.comp (hd.prod (hroot.prod hrecord))
  have hlist : ComputableInPolyTime (fun p : Data × ℕ => p.1.2) input (encList recordEncoding) := by fun_prop
  have hpaths := mapWithInput (f := fun (p : Data × ℕ) record => path (p.1, (p.2, record))) hlist hpath
  have hlabels : ComputableInPolyTime (fun p : Data × ℕ => p.1.1) input (encList encNat) := by fun_prop
  have hindex := snd dataEncoding encNat
  have hname := labelLookup_polyTime.comp (hlabels.prod hindex)
  have hjoin := joinPaths_polyTime.comp (hname.prod hpaths)
  exact hr.optionMapWithInput (f := fun (data : Data) root => Reset.Term.joinPaths (data.1.getD root 0)
    (data.2.map (fun record => path (data, (root, record))))) hjoin

/-- Complete typed-descriptor algorithm. Recognition is checked before any
output; all generated syntax is an original primitive reset tree. -/
def synthesize (d : GuardDescriptor) : Option (Reset.Term ℕ) :=
  if d.check then rawSynthesize (view d) else none

theorem synthesize_polyTime : ComputableInPolyTime synthesize
    DescriptorValidation.descriptorEncoding (encOption TermMachine.termEncoding) :=
  RecognitionMachine.check_polyTime.ite (rawSynthesize_polyTime.comp RawRecords.view_polyTime) (const none)

def synthesizeWord (word : List Bool) : Option (Reset.Term ℕ) := (GuardDescriptor.decode word).bind synthesize

theorem synthesizeWord_polyTime : ComputableInPolyTime synthesizeWord encBits (encOption TermMachine.termEncoding) := by
  have hb := synthesize_polyTime.comp (snd encBits DescriptorValidation.descriptorEncoding)
  have h := DescriptorValidation.decode_polyTime.optionElimWithInput (body := fun (_ : List Bool) d => synthesize d) (const none) hb
  convert h using 1
  funext word
  unfold synthesizeWord
  cases GuardDescriptor.decode word <;> rfl



theorem relabel_joinPaths {Var Var' : Type*} (f : Var → Var') (root : Var) (terms : List (Reset.Term Var)) :
    (Reset.Term.joinPaths root terms).relabel f =
      Reset.Term.joinPaths (f root) (terms.map (fun t => t.relabel f)) := by
  induction terms with
  | nil => rfl
  | cons t terms ih =>
    simp only [Reset.Term.joinPaths, List.foldr_cons, List.map_cons, Reset.Term.relabel_step]
    exact congrArg (Reset.Term.step (t.relabel f)) ih

theorem rawSynthesize_view (d : GuardDescriptor) :
    rawSynthesize (view d) = d.root?.map (fun root => (d.recordTerm root).relabel d.labels.get) := by
  unfold rawSynthesize view
  rw [findRoot_view]
  simp only [Option.map_map]
  apply congrArg (fun f => d.root?.map f)
  funext root
  have hlabel : d.labels.getD root.val 0 = d.labels.get root := by
    rw [List.getD_eq_getElem _ _ root.isLt]
    rfl
  dsimp only [Function.comp_def]
  rw [GuardDescriptor.recordTerm, relabel_joinPaths, hlabel]
  apply congrArg (Reset.Term.joinPaths (d.labels.get root))
  simp only [List.map_map, GuardDescriptor.recordPaths]
  apply List.map_congr_left
  intro record _
  exact path_view d root record

/-- The executable output is the literal raw-record construction, relabelled
back to the original sparse variable names. -/
theorem synthesize_eq (d : GuardDescriptor) :
    synthesize d = if d.check then
      d.root?.map (fun root => (d.recordTerm root).relabel d.labels.get) else none := by
  unfold synthesize
  rw [rawSynthesize_view]

/-- Successful synthesis returns an actual primitive reset tree whose
independently defined minimal-selector table is exactly the input table. -/
theorem synthesize_spec (d : GuardDescriptor) (hc : d.check = true) :
    ∃ (root : Fin d.labels.length) (t : Reset.Term (Fin d.labels.length)),
      synthesize d = some (t.relabel d.labels.get) ∧ t.root = root ∧
      t.table = d.guards ∧ t.size ≤ 1 + 2 * d.labels.length * d.records.length := by
  obtain ⟨root, hw⟩ := d.check_eq_true.mp hc
  refine ⟨root, d.recordTerm root, ?_, d.recordTerm_spec root hw⟩
  simp only [synthesize_eq, hc, ite_true, d.root?_eq_some_of_wellFormed root hw, Option.map_some]

theorem synthesize_isSome (d : GuardDescriptor) : (synthesize d).isSome = d.check := by
  cases hc : d.check with
  | false => simp [synthesize, hc]
  | true =>
    obtain ⟨root, t, ht, _⟩ := synthesize_spec d hc
    rw [ht]
    rfl

theorem synthesizeWord_isSome (word : List Bool) :
    (synthesizeWord word).isSome = GuardDescriptor.recognize word := by
  unfold synthesizeWord GuardDescriptor.recognize
  cases hd : GuardDescriptor.decode word with
  | none => rfl
  | some d => exact synthesize_isSome d



universe u

/-- Renaming changes variable lookup only; repeated occurrences remain
independent occurrences in the generated primitive tree. -/
theorem eval_relabel {Var Var' : Type*} {Role : Type u} (t : Reset.Term Var)
    (f : Var → Var') (v : Var' → WinnerSet Role) :
    Reset.Term.eval (t.relabel f) v = t.eval (v ∘ f) := by
  induction t using Reset.Term.induction_reset with
  | var => rfl
  | step s t hs ht =>
    simp only [Reset.Term.relabel_step, Reset.Term.eval_step, hs, ht]

theorem size_relabel {Var Var' : Type*} (t : Reset.Term Var) (f : Var → Var') :
    Reset.Term.size (t.relabel f) = t.size := by
  induction t using Reset.Term.induction_reset with
  | var => rfl
  | step s t hs ht =>
    simp only [Reset.Term.relabel_step, Reset.Term.size_step, hs, ht]

/-- The actual executable result satisfies the raw input's guard semantics
for every role carrier and every original-label valuation. -/
theorem synthesize_semantics {Role : Type u} (d : GuardDescriptor) (hc : d.check = true) :
    ∃ output : Reset.Term ℕ, synthesize d = some output ∧
      output.size ≤ 1 + 2 * d.labels.length * d.records.length ∧
      ∀ (v : ℕ → WinnerSet Role) (winner : Role),
        winner ∈ (output.eval v).val ↔
          ∃ p ∈ d.records, (∀ k ∈ p.2, (v (d.labels.get k)).Ambiguous) ∧
            winner ∈ (v (d.labels.get p.1)).val := by
  obtain ⟨root, t, ht, _, htable, hsize⟩ := synthesize_spec d hc
  refine ⟨t.relabel d.labels.get, ht, ?_, ?_⟩
  · rw [size_relabel]
    exact hsize
  · intro v winner
    rw [eval_relabel, Reset.Term.mem_eval]
    simp only [Reset.Term.selected_iff_table, htable, Function.comp_def]
    constructor
    · rintro ⟨j, ⟨A,hA,hsub⟩, hw⟩
      refine ⟨(j,A), (d.mem_guards j A).mp hA, ?_, hw⟩
      intro k hk
      exact hsub hk
    · rintro ⟨⟨j,A⟩, hp, hA, hw⟩
      exact ⟨j, ⟨A, (d.mem_guards j A).mpr hp, fun _ hk => hA _ hk⟩, hw⟩

/-- Byte-valued interface: output bytes are exactly the original primitive
reset prefix-tree codec, with none on malformed or unrealizable inputs. -/
def synthesizeCode (word : List Bool) : Option (List Bool) :=
  (synthesizeWord word).map TermCode.encode

theorem synthesizeCode_polyTime : ComputableInPolyTime synthesizeCode encBits (encOption encBits) := by
  have he : ComputableInPolyTime TermCode.encode TermMachine.termEncoding encBits := .of_eq (fun _ => rfl)
  exact synthesizeWord_polyTime.optionMapWithInput
    (f := fun (_ : List Bool) t => TermCode.encode t)
    (he.comp (snd encBits TermMachine.termEncoding))

theorem synthesizeCode_isSome (word : List Bool) :
    (synthesizeCode word).isSome = GuardDescriptor.recognize word := by
  simp only [synthesizeCode, Option.isSome_map, synthesizeWord_isSome]

theorem synthesizeWord_decode {word : List Bool} {d : GuardDescriptor}
    (hd : GuardDescriptor.decode word = some d) : synthesizeWord word = synthesize d := by
  simp only [synthesizeWord, hd, Option.bind_some]

theorem synthesizeCode_malformed {word : List Bool}
    (hd : GuardDescriptor.decode word = none) : synthesizeCode word = none := by
  simp only [synthesizeCode, synthesizeWord, hd, Option.bind_none, Option.map_none]



theorem synthesizeCode_encode (d : GuardDescriptor) :
    synthesizeCode d.encode = (synthesize d).map TermCode.encode := by
  simp only [synthesizeCode, synthesizeWord, GuardDescriptor.decode_encode, Option.bind_some]

/-- Complete encoded synthesis, including the original primitive output
syntax and its evaluation, rather than a detached guard certificate. -/
theorem synthesizeCode_encode_spec {Role : Type u} (d : GuardDescriptor) (hc : d.check = true) :
    ∃ output : Reset.Term ℕ, synthesizeCode d.encode = some (TermCode.encode output) ∧
      output.size ≤ 1 + 2 * d.labels.length * d.records.length ∧
      ∀ (v : ℕ → WinnerSet Role) (winner : Role),
        winner ∈ (output.eval v).val ↔
          ∃ p ∈ d.records, (∀ k ∈ p.2, (v (d.labels.get k)).Ambiguous) ∧
            winner ∈ (v (d.labels.get p.1)).val := by
  obtain ⟨output, ho, hsize, hsem⟩ := synthesize_semantics (Role := Role) d hc
  refine ⟨output, ?_, hsize, hsem⟩
  simp only [synthesizeCode_encode, ho, Option.map_some]

end KFOL.Complexity.ResetSynthesis
