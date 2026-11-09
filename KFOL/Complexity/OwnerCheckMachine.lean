module
public import KFOL.Complexity.OwnerRunMachine

/-! # Complete native owner-table checking and its independent specification -/

@[expose] public section
namespace KFOL.Complexity.OwnerRuntime
open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.Algorithms

abbrev FinishInput := Context × RawGuard
abbrev finishEncoding := encPair contextEncoding guardEncoding

def finishTest (context : Context) (state : RawGuard) (z : ℕ) : Bool :=
  let j := context.2.1
  let target := union (context.2.2.1, union (context.2.2.2, single (context.2.2.1.length, j)))
  let outside := union (state.2, union (single (state.1.length, j), single (state.1.length, z)))
  member (target, z) && permitted context.1 j (state.1, outside) &&
    permitted context.1 z (state.1, outside)

theorem finishTest_polyTime : ComputableInPolyTime
    (fun p : FinishInput × ℕ => finishTest p.1.1 p.1.2 p.2)
    (encPair finishEncoding encNat) encBool := by
  let input := encPair finishEncoding encNat
  have hj : ComputableInPolyTime (fun p : FinishInput × ℕ => p.1.1.2.1) input encNat := by fun_prop
  have hz := snd finishEncoding encNat
  have hm : ComputableInPolyTime (fun p : FinishInput × ℕ => p.1.2.1) input encBits := by fun_prop
  have ho : ComputableInPolyTime (fun p : FinishInput × ℕ => p.1.2.2) input encBits := by fun_prop
  have hgm : ComputableInPolyTime (fun p : FinishInput × ℕ => p.1.1.2.2.1) input encBits := by fun_prop
  have hgo : ComputableInPolyTime (fun p : FinishInput × ℕ => p.1.1.2.2.2) input encBits := by fun_prop
  have ht : ComputableInPolyTime (fun p : FinishInput × ℕ => p.1.1.1) input tableEncoding := by fun_prop
  have hsj := single_polyTime.comp ((length_bits.comp hm).prod hj)
  have hsz := single_polyTime.comp ((length_bits.comp hm).prod hz)
  have hgj := single_polyTime.comp ((length_bits.comp hgm).prod hj)
  have htarget := union_polyTime.comp (hgm.prod (union_polyTime.comp (hgo.prod hgj)))
  have houtside := union_polyTime.comp (ho.prod (union_polyTime.comp (hsj.prod hsz)))
  have hpj := permitted_polyTime.comp (ht.prod (hj.prod (hm.prod houtside)))
  have hpz := permitted_polyTime.comp (ht.prod (hz.prod (hm.prod houtside)))
  exact bool_and' (bool_and' (member_polyTime.comp (htarget.prod hz)) hpj) hpz

def finishWitness (context : Context) (state : RawGuard) : Option ℕ :=
  (List.range context.2.2.1.length).find? (finishTest context state)

theorem finishWitness_polyTime : ComputableInPolyTime
    (fun p : FinishInput => finishWitness p.1 p.2) finishEncoding (encOption encNat) := by
  have hm : ComputableInPolyTime (fun p : FinishInput => p.1.2.2.1) finishEncoding encBits := by fun_prop
  exact findWithInput (test := fun (p : FinishInput) z => finishTest p.1 p.2 z)
    (indices_polyTime.comp (length_bits.comp hm)) finishTest_polyTime

def finish (context : Context) (state : RawGuard) : Bool :=
  permitted context.1 context.2.1 state || (finishWitness context state).isSome

theorem finish_polyTime : ComputableInPolyTime
    (fun p : FinishInput => finish p.1 p.2) finishEncoding encBool := by
  have ht : ComputableInPolyTime (fun p : FinishInput => p.1.1) finishEncoding tableEncoding := by fun_prop
  have hj : ComputableInPolyTime (fun p : FinishInput => p.1.2.1) finishEncoding encNat := by fun_prop
  have hs := snd contextEncoding guardEncoding
  exact bool_or.comp ((permitted_polyTime.comp (ht.prod (hj.prod hs))).prod
    finishWitness_polyTime.optionIsSome)

def accepts (context : Context) : Bool :=
  decide (context.2.1 = context.1.1) || finish context (run context).1

theorem accepts_polyTime : ComputableInPolyTime accepts contextEncoding encBool := by
  have hj : ComputableInPolyTime (fun p : Context => p.2.1) contextEncoding encNat := by fun_prop
  have hr : ComputableInPolyTime (fun p : Context => p.1.1) contextEncoding encNat := by fun_prop
  have hs := (fst guardEncoding (encList (encPair encNat encNat))).comp run_polyTime
  exact bool_or.comp ((decide_eq' hj hr).prod (finish_polyTime.comp (id'.prod hs)))
theorem finishTest_view {n : ℕ} (T : Owner.GuardTable (Fin n)) (j : Fin n)
    (g : Owner.GuardPair (Fin n)) (S : Owner.SaturationState (Fin n)) (z : Fin n) :
    finishTest (tableView T, entryView (j, g)) (stateView S) z.val =
      decide (z ∈ Owner.GuardTable.target j g ∧
        T.Permitted j S.many (S.outside ∪ {j, z}) ∧
        T.Permitted z S.many (S.outside ∪ {j, z})) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  simp only [finishTest, entryView, stateView, Bitset.length_encode, single_encode,
    union_encode, member_encode, permitted_view, Bool.and_eq_true]
  simp only [decide_eq_true_eq]
  simp only [Owner.GuardTable.target, Finset.union_assoc, Finset.singleton_union]
  tauto

theorem finishWitness_view {n : ℕ} (T : Owner.GuardTable (Fin n)) (j : Fin n)
    (g : Owner.GuardPair (Fin n)) (S : Owner.SaturationState (Fin n)) :
    finishWitness (tableView T, entryView (j, g)) (stateView S) =
      (T.finishWitness (List.finRange n) j g S).map Fin.val := by
  simp only [finishWitness, entryView, Bitset.length_encode, ← finRange_values n, List.find?_map]
  unfold Owner.GuardTable.finishWitness
  congr 2
  funext z
  exact finishTest_view T j g S z

theorem finish_view {n : ℕ} (T : Owner.GuardTable (Fin n)) (j : Fin n)
    (g : Owner.GuardPair (Fin n)) (S : Owner.SaturationState (Fin n)) :
    finish (tableView T, entryView (j, g)) (stateView S) = decide (T.Finish j g S) := by
  unfold finish
  change (permitted (tableView T) j.val (stateView S) ||
    (finishWitness (tableView T, entryView (j, g)) (stateView S)).isSome) = _
  rw [show permitted (tableView T) j.val (stateView S) =
    decide (T.Permitted j S.many S.outside) from permitted_view T j S.many S.outside]
  rw [finishWitness_view]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, decide_eq_true_eq, Option.isSome_map,
    Owner.GuardTable.finishWitness, List.find?_isSome, List.mem_finRange, true_and,
    Owner.GuardTable.Finish]

theorem accepts_view {n : ℕ} (T : Owner.GuardTable (Fin n)) (j : Fin n)
    (g : Owner.GuardPair (Fin n)) :
    accepts (tableView T, entryView (j, g)) = T.accepts (List.finRange n) j g := by
  unfold accepts
  rw [run_view]
  change (decide (j.val = T.root.val) ||
    finish (tableView T, entryView (j, g)) (stateView (T.run (List.finRange n) j g (2 * n)).1)) = _
  rw [finish_view]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, decide_eq_true_eq, Fin.val_inj, Owner.GuardTable.accepts,
    List.length_finRange]

def emptyGuard (guard : RawGuard) : Bool :=
  (guard.1.all (!·)) && (guard.2.all (!·))

private theorem emptyGuard_polyTime : ComputableInPolyTime emptyGuard guardEncoding encBool := by
  have ha := allWithInput (test := fun (_ : RawGuard) (b : Bool) => !b)
    ((bits_encList_polyTime encBool).1.comp (fst encBits encBits))
    (bool_not.comp (snd guardEncoding encBool))
  have hb := allWithInput (test := fun (_ : RawGuard) (b : Bool) => !b)
    ((bits_encList_polyTime encBool).1.comp (snd encBits encBits))
    (bool_not.comp (snd guardEncoding encBool))
  exact bool_and' ha hb

def dominates (p q : RawEntry) : Bool :=
  decide (q.1 = p.1) && ReachMachine.subset p.2.1 q.2.1 &&
    ReachMachine.subset p.2.2 (union (q.2.1, union (q.2.2, single (p.2.1.length, p.1))))

private theorem dominates_polyTime : ComputableInPolyTime
    (fun p : RawEntry × RawEntry => dominates p.1 p.2) (encPair entryEncoding entryEncoding) encBool := by
  let input := encPair entryEncoding entryEncoding
  have hsource : ComputableInPolyTime (fun p : RawEntry × RawEntry => p.1.1) input encNat := by fun_prop
  have htarget : ComputableInPolyTime (fun p : RawEntry × RawEntry => p.2.1) input encNat := by fun_prop
  have hpm : ComputableInPolyTime (fun p : RawEntry × RawEntry => p.1.2.1) input encBits := by fun_prop
  have hpo : ComputableInPolyTime (fun p : RawEntry × RawEntry => p.1.2.2) input encBits := by fun_prop
  have hqm : ComputableInPolyTime (fun p : RawEntry × RawEntry => p.2.2.1) input encBits := by fun_prop
  have hqo : ComputableInPolyTime (fun p : RawEntry × RawEntry => p.2.2.2) input encBits := by fun_prop
  have hs := single_polyTime.comp ((length_bits.comp hpm).prod hsource)
  have hu := union_polyTime.comp (hqm.prod (union_polyTime.comp (hqo.prod hs)))
  exact bool_and' (bool_and' (decide_eq' htarget hsource)
    (ReachMachine.subset_polyTime.comp (hpm.prod hqm)))
    (ReachMachine.subset_polyTime.comp (hpo.prod hu))

def otherGuard (table : RawTable) (p : RawEntry) : Bool :=
  if p.1 = table.1 then true else
    member (p.2.1, table.1) && !(member (p.2.1, p.1)) &&
      ReachMachine.subset p.2.2 ((union (p.2.1, single (p.2.1.length, p.1))).map (!·)) &&
      table.2.all (fun q => !(dominates p q) || decide (p.2 = q.2))

private theorem otherGuard_polyTime : ComputableInPolyTime
    (fun p : RawTable × RawEntry => otherGuard p.1 p.2)
    (encPair tableEncoding entryEncoding) encBool := by
  let input := encPair tableEncoding entryEncoding
  have hr : ComputableInPolyTime (fun p : RawTable × RawEntry => p.1.1) input encNat := by fun_prop
  have hi : ComputableInPolyTime (fun p : RawTable × RawEntry => p.2.1) input encNat := by fun_prop
  have hm : ComputableInPolyTime (fun p : RawTable × RawEntry => p.2.2.1) input encBits := by fun_prop
  have ho : ComputableInPolyTime (fun p : RawTable × RawEntry => p.2.2.2) input encBits := by fun_prop
  have hroot := member_polyTime.comp (hm.prod hr)
  have hself := bool_not.comp (member_polyTime.comp (hm.prod hi))
  have hsingle := single_polyTime.comp ((length_bits.comp hm).prod hi)
  have hu := union_polyTime.comp (hm.prod hsingle)
  have hnot := mapToBitsWithInput (f := fun (_ : RawTable × RawEntry) (b : Bool) => !b)
    ((bits_encList_polyTime encBool).1.comp hu) (bool_not.comp (snd input encBool))
  have hdisjoint := ReachMachine.subset_polyTime.comp (ho.prod hnot)
  have hrecords : ComputableInPolyTime (fun p : RawTable × RawEntry => p.1.2) input
      (encList entryEncoding) := by fun_prop
  have hp : ComputableInPolyTime (fun p : (RawTable × RawEntry) × RawEntry => p.1.2)
      (encPair input entryEncoding) entryEncoding := by fun_prop
  have hq := snd input entryEncoding
  have hdom := dominates_polyTime.comp (hp.prod hq)
  have hpg : ComputableInPolyTime (fun p : (RawTable × RawEntry) × RawEntry => p.1.2.2)
      (encPair input entryEncoding) guardEncoding := by fun_prop
  have hqg : ComputableInPolyTime (fun p : (RawTable × RawEntry) × RawEntry => p.2.2)
      (encPair input entryEncoding) guardEncoding := by fun_prop
  have htest := bool_or.comp ((bool_not.comp hdom).prod (decide_eq' hpg hqg))
  have hall := allWithInput (test := fun (p : RawTable × RawEntry) q =>
    !(dominates p.2 q) || decide (p.2.2 = q.2)) hrecords htest
  have h := (decide_eq' hi hr).ite (const true)
    (bool_and' (bool_and' (bool_and' hroot hself) hdisjoint) hall)
  convert h using 1
  funext p
  simp only [otherGuard, Function.comp_def, decide_eq_true_eq]

def canonical (table : RawTable) : Bool :=
  decide table.2.Nodup &&
    table.2.any (fun p => decide (p.1 = table.1) && emptyGuard p.2) &&
    table.2.all (fun p => !(decide (p.1 = table.1)) || emptyGuard p.2) &&
    table.2.all (otherGuard table)

private theorem canonical_polyTime : ComputableInPolyTime canonical tableEncoding encBool := by
  have hl := snd encNat (encList entryEncoding)
  have hi : ComputableInPolyTime (fun p : RawTable × RawEntry => p.2.1)
      (encPair tableEncoding entryEncoding) encNat := by fun_prop
  have hr : ComputableInPolyTime (fun p : RawTable × RawEntry => p.1.1)
      (encPair tableEncoding entryEncoding) encNat := by fun_prop
  have hg : ComputableInPolyTime (fun p : RawTable × RawEntry => p.2.2)
      (encPair tableEncoding entryEncoding) guardEncoding := by fun_prop
  have he := emptyGuard_polyTime.comp hg
  have hroot := decide_eq' hi hr
  have hex := anyWithInput (test := fun (table : RawTable) (p : RawEntry) => decide (p.1 = table.1) && emptyGuard p.2)
    hl (bool_and' hroot he)
  have hall := allWithInput (test := fun (table : RawTable) (p : RawEntry) => !(decide (p.1 = table.1)) || emptyGuard p.2)
    hl (bool_or.comp ((bool_not.comp hroot).prod he))
  exact bool_and' (bool_and' (bool_and' (decide_nodup hl) hex) hall)
    (allWithInput (test := otherGuard) hl otherGuard_polyTime)

def check (input : ℕ × RawTable) : Bool :=
  canonical input.2 && input.2.2.all (fun p => accepts (input.2, p))

theorem check_polyTime : ComputableInPolyTime check rawEncoding encBool := by
  have ht := snd encUnary tableEncoding
  have hrecords : ComputableInPolyTime (fun p : ℕ × RawTable => p.2.2) rawEncoding
      (encList entryEncoding) := by fun_prop
  have htable : ComputableInPolyTime (fun p : (ℕ × RawTable) × RawEntry => p.1.2)
      (encPair rawEncoding entryEncoding) tableEncoding := by fun_prop
  have hp := snd rawEncoding entryEncoding
  exact bool_and' (canonical_polyTime.comp ht)
    (allWithInput (test := fun (p : ℕ × RawTable) entry => accepts (p.2, entry)) hrecords
      (accepts_polyTime.comp (htable.prod hp)))

private theorem emptyGuard_view {n : ℕ} (g : Owner.GuardPair (Fin n)) :
    emptyGuard (Bitset.encode g.many, Bitset.encode g.outside) = decide (g = ⟨∅, ∅⟩) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  simp only [emptyGuard, Bool.and_eq_true, List.all_eq_true, Bitset.encode,
    List.mem_ofFn]
  constructor
  · rintro ⟨hm, ho⟩
    have ha : g.many = ∅ := by
      ext i
      simp only [Finset.notMem_empty, iff_false]
      simpa using hm _ ⟨i, rfl⟩
    have hb : g.outside = ∅ := by
      ext i
      simp only [Finset.notMem_empty, iff_false]
      simpa using ho _ ⟨i, rfl⟩
    cases g
    simp_all
  · rintro rfl
    simp

private theorem complement_encode {n : ℕ} (A : Finset (Fin n)) :
    (Bitset.encode A).map (!·) = Bitset.encode Aᶜ := by
  apply List.ext_getElem (by simp [Bitset.encode])
  intro i hi hi'
  simp [Bitset.encode]

private theorem disjoint_encode {n : ℕ} (A B : Finset (Fin n)) :
    ReachMachine.subset (Bitset.encode A) ((Bitset.encode B).map (!·)) = decide (Disjoint A B) := by
  rw [complement_encode, ReachMachine.subset_encode]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Finset.subset_compl_iff_disjoint_left]
  exact disjoint_comm

private theorem dominates_view {n : ℕ} (p q : Fin n × Owner.GuardPair (Fin n)) :
    dominates (entryView p) (entryView q) =
      decide (q.1 = p.1 ∧ p.2.many ⊆ q.2.many ∧
        p.2.outside ⊆ q.2.many ∪ q.2.outside ∪ {p.1}) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  simp only [dominates, entryView, Bitset.length_encode, single_encode, union_encode,
    ReachMachine.subset_encode, Bool.and_eq_true, decide_eq_true_eq, Fin.val_inj]
  simp only [Finset.union_assoc]
  tauto

private theorem guardView_eq {n : ℕ} (p q : Fin n × Owner.GuardPair (Fin n)) :
    (entryView p).2 = (entryView q).2 ↔ p.2 = q.2 := by
  constructor
  · intro h
    have hm := Bitset.encode_injective (congrArg Prod.fst h)
    have ho := Bitset.encode_injective (congrArg Prod.snd h)
    change Owner.GuardPair.mk p.2.many p.2.outside = Owner.GuardPair.mk q.2.many q.2.outside
    exact congrArg₂ Owner.GuardPair.mk hm ho
  · intro h
    simp only [entryView, h]

private theorem otherGuard_view {n : ℕ} (T : Owner.GuardTable (Fin n))
    (p : Fin n × Owner.GuardPair (Fin n)) :
    otherGuard (tableView T) (entryView p) = decide (p.1 ≠ T.root →
      (T.root ∈ p.2.many ∧ p.1 ∉ p.2.many ∧ Disjoint p.2.outside (insert p.1 p.2.many)) ∧
      ∀ q ∈ T.entries, q.1 = p.1 → p.2.many ⊆ q.2.many →
        p.2.outside ⊆ q.2.many ∪ q.2.outside ∪ {p.1} → p.2 = q.2) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  unfold otherGuard
  split
  next hr =>
    have hr : p.1 = T.root := Fin.ext hr
    simp [hr]
  next hr =>
    have hne : p.1 ≠ T.root := fun h => hr (congrArg Fin.val h)
    rw [show (entryView p).2.1.length = n from Bitset.length_encode p.2.many]
    change (((member (Bitset.encode p.2.many, T.root.val) &&
      !(member (Bitset.encode p.2.many, p.1.val))) &&
      ReachMachine.subset (Bitset.encode p.2.outside)
        ((union (Bitset.encode p.2.many, single (n, p.1.val))).map (!·))) &&
      (T.entries.map entryView).all (fun q => !(dominates (entryView p) q) ||
        decide ((entryView p).2 = q.2))) = true ↔ _
    rw [single_encode, union_encode, disjoint_encode]
    simp only [member_encode, List.all_map, Function.comp_def, List.all_eq_true,
      dominates_view, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
    simp only [decide_eq_true_eq, decide_eq_false_iff_not, guardView_eq]
    have he : p.2.many ∪ {p.1} = insert p.1 p.2.many := by ext i; simp
    rw [he]
    constructor
    · rintro ⟨⟨⟨hroot, hself⟩, hd⟩, hall⟩ _
      refine ⟨⟨hroot, hself, hd⟩, ?_⟩
      intro q hq hsource hm ho
      exact (hall q hq).resolve_left (not_not_intro ⟨hsource, hm, ho⟩)
    · intro h
      obtain ⟨⟨hroot, hself, hd⟩, hall⟩ := h hne
      refine ⟨⟨⟨hroot, hself⟩, hd⟩, ?_⟩
      intro q hq
      by_cases he : q.1 = p.1 ∧ p.2.many ⊆ q.2.many ∧
          p.2.outside ⊆ q.2.many ∪ q.2.outside ∪ {p.1}
      · exact Or.inr (hall q hq he.1 he.2.1 he.2.2)
      · exact Or.inl he


private theorem root_guards_eq {n : ℕ} (T : Owner.GuardTable (Fin n)) :
    ((∃ p ∈ T.entries, p.1 = T.root ∧ p.2 = ⟨∅, ∅⟩) ∧
      ∀ p ∈ T.entries, p.1 = T.root → p.2 = ⟨∅, ∅⟩) ↔
      T.guards T.root = {⟨∅, ∅⟩} := by
  constructor
  · rintro ⟨⟨p, hp, hr, hg⟩, hall⟩
    apply Finset.ext
    intro g
    simp only [Finset.mem_singleton, mem_guards]
    constructor
    · intro hm
      exact hall (T.root, g) hm rfl
    · rintro rfl
      have he : p = (T.root, ⟨∅, ∅⟩) := Prod.ext hr hg
      simpa only [he] using hp
  · intro h
    have hempty : (T.root, (⟨∅, ∅⟩ : Owner.GuardPair (Fin n))) ∈ T.entries := by
      rw [← mem_guards, h]
      simp
    refine ⟨⟨(T.root, ⟨∅, ∅⟩), hempty, rfl, rfl⟩, ?_⟩
    intro p hp hr
    have hm : p.2 ∈ T.guards T.root := by
      rw [mem_guards]
      have he : p = (T.root, p.2) := Prod.ext hr rfl
      rw [he] at hp
      exact hp
    simpa only [h, Finset.mem_singleton] using hm

/-- Canonicality is checked by explicit finite record scans, with exactly the
independent owner-table definition as its proposition. -/
theorem canonical_view {n : ℕ} (T : Owner.GuardTable (Fin n)) :
    canonical (tableView T) = T.canonicalB := by
  apply Bool.eq_iff_iff.mpr
  unfold Owner.GuardTable.canonicalB
  rw [decide_eq_true_eq]
  change (((decide (T.entries.map entryView).Nodup &&
    (T.entries.map entryView).any (fun p => decide (p.1 = T.root.val) && emptyGuard p.2)) &&
    (T.entries.map entryView).all (fun p => !(decide (p.1 = T.root.val)) || emptyGuard p.2)) &&
    (T.entries.map entryView).all (otherGuard (tableView T))) = true ↔ _
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_map, List.all_map,
    Function.comp_def, List.any_eq_true, List.all_eq_true]
  have he : ∀ p : Fin n × Owner.GuardPair (Fin n),
      emptyGuard (entryView p).2 = decide (p.2 = ⟨∅, ∅⟩) := fun p => emptyGuard_view p.2
  simp_rw [he]
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not]
  have hrval : ∀ p : Fin n × Owner.GuardPair (Fin n),
      (entryView p).1 = T.root.val ↔ p.1 = T.root := fun p => Fin.val_inj
  simp_rw [hrval]
  rw [List.nodup_map_iff entryView_injective]

  have ho : ∀ p, otherGuard (tableView T) (entryView p) = true ↔
      (p.1 ≠ T.root →
      (T.root ∈ p.2.many ∧ p.1 ∉ p.2.many ∧ Disjoint p.2.outside (insert p.1 p.2.many)) ∧
      ∀ q ∈ T.entries, q.1 = p.1 → p.2.many ⊆ q.2.many →
        p.2.outside ⊆ q.2.many ∪ q.2.outside ∪ {p.1} → p.2 = q.2) := by
    intro p
    rw [otherGuard_view, decide_eq_true_eq]
  simp_rw [ho]
  have hr := root_guards_eq T
  constructor
  · rintro ⟨⟨⟨hnd, hex⟩, hall⟩, hother⟩
    refine ⟨hnd, hr.mp ⟨hex, ?_⟩, hother⟩
    intro p hp hroot
    exact (hall p hp).resolve_left (not_not_intro hroot)
  · rintro ⟨hnd, hroot, hother⟩
    obtain ⟨hex, hall⟩ := hr.mpr hroot
    refine ⟨⟨⟨hnd, hex⟩, ?_⟩, hother⟩
    intro p hp
    by_cases hroot : p.1 = T.root
    · exact Or.inr (hall p hp hroot)
    · exact Or.inl hroot

/-- Exact whole-checker bridge, including noncanonical and duplicate records. -/
theorem check_view {n : ℕ} (T : Owner.GuardTable (Fin n)) :
    check (n, tableView T) = T.check (List.finRange n) := by
  symm
  change T.check (List.finRange n) =
    (canonical (tableView T) && (tableView T).2.all (fun p => accepts (tableView T, p)))
  rw [canonical_view]
  have hlisted : T.Listed (List.finRange n) := by
    constructor
    · simp
    · intro p hp
      simp
  simp only [Owner.GuardTable.check, decide_eq_true hlisted, Bool.and_true,
    tableView, List.all_map, Function.comp_def]
  apply congrArg (fun b => T.canonicalB && b)
  apply List.all_congr
  · rfl
  · intro p
    exact (accepts_view T p.1 p.2).symm

/-- The actual independent complete finite owner checker has a native machine
certificate; no promise about canonical input is assumed. -/
theorem source_check_polyTime : ComputableInPolyTime
    (fun input : Input => input.2.check (List.finRange input.1)) inputEncoding encBool := by
  have h := check_polyTime.comp view_polyTime
  convert h using 1
  funext input
  exact (check_view input.2).symm

end KFOL.Complexity.OwnerRuntime
