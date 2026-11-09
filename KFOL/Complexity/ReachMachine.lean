module

public import KFOL.Complexity.RawRecords
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-! # Native polynomial-time greedy closure of listed prerequisites -/

@[expose] public section

namespace KFOL.Complexity.ReachMachine

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.Algorithms KFOL.Complexity.RawRecords

def subset (a b : List Bool) : Bool := (GuardWords.subsetWord a b).headD false

@[fun_prop] theorem subset_polyTime : ComputableInPolyTime
    (fun p : List Bool × List Bool => subset p.1 p.2) (encPair encBits encBits) encBool := by
  have hargs : ComputableInPolyTime
      (fun p : List Bool × List Bool => fun i : Fin 2 => if i = 0 then p.1 else p.2)
      (encPair encBits encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    by_cases hi : i = 0
    · simp only [hi, ite_true]; exact fst _ _
    · simp only [hi, ite_false]; exact snd _ _
  exact (headD (encA := encBool) (encL := encBits) false).comp
    (GuardSubset.subsetFn_polyTime.comp hargs)

@[simp] theorem subset_encode {n : ℕ} (A B : Finset (Fin n)) :
    subset (Bitset.encode A) (Bitset.encode B) = decide (A ⊆ B) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  have h := GuardWords.subsetWord_encode A B
  simpa only [subset, GuardWords.subsetWord, List.headD_cons, List.cons.injEq, and_true] using h

abbrev Context := List Record × List Bool
private abbrev contextEncoding := encPair (encList recordEncoding) encBits
private abbrev StepInput := Context × List Bool
private abbrev stepInputEncoding := encPair contextEncoding encBits

def advance (context : Context) (reached : List Bool) : List Bool :=
  (List.range context.2.length).map fun i => reached.getD i false ||
    (context.2.getD i false && context.1.any (fun r => decide (r.1 = i) && subset r.2 reached))

private theorem advance_polyTime : ComputableInPolyTime
    (fun p : StepInput => advance p.1 p.2) stepInputEncoding encBits := by
  have htarget : ComputableInPolyTime (fun p : StepInput => p.1.2) stepInputEncoding encBits := by fun_prop
  have hrange := ComputableInPolyTime.range.comp (length_bits.comp htarget)
  let scanEncoding := encPair stepInputEncoding encUnary
  have hreached : ComputableInPolyTime (fun p : StepInput × ℕ => p.1.2) scanEncoding encBits := by fun_prop
  have hindex : ComputableInPolyTime (fun p : StepInput × ℕ => p.2) scanEncoding encUnary := snd _ _
  have htarget' : ComputableInPolyTime (fun p : StepInput × ℕ => p.1.1.2) scanEncoding encBits := by fun_prop
  have hold := bitsGetDWithInput hreached hindex false
  have hin := bitsGetDWithInput htarget' hindex false
  have hrecords : ComputableInPolyTime (fun p : StepInput × ℕ => p.1.1.1) scanEncoding (encList recordEncoding) := by fun_prop
  let innerEncoding := encPair scanEncoding recordEncoding
  have hout : ComputableInPolyTime (fun p : (StepInput × ℕ) × Record => p.2.1) innerEncoding encNat := by fun_prop
  have hidx : ComputableInPolyTime (fun p : (StepInput × ℕ) × Record => p.1.2) innerEncoding encUnary := by fun_prop
  have hguard : ComputableInPolyTime (fun p : (StepInput × ℕ) × Record => p.2.2) innerEncoding encBits := by fun_prop
  have hstate : ComputableInPolyTime (fun p : (StepInput × ℕ) × Record => p.1.1.2) innerEncoding encBits := by fun_prop
  have htest := bool_and' (decide_eq' hout (unary_to_binary.comp hidx))
    (subset_polyTime.comp (hguard.prod hstate))
  have hany := anyWithInput (test := fun (p : StepInput × ℕ) (r : Record) =>
    decide (r.1 = p.2) && subset r.2 p.1.2) hrecords htest
  have hbit := bool_or.comp (hold.prod (bool_and' hin hany))
  have hmap := mapWithInput (f := fun (p : StepInput) (i : ℕ) => p.2.getD i false ||
    (p.1.2.getD i false && p.1.1.any (fun r => decide (r.1 = i) && subset r.2 p.2))) hrange hbit
  exact (bits_encList_polyTime encBool).2.comp hmap

private theorem advance_length (context : Context) (reached : List Bool) :
    (advance context reached).length = context.2.length := by
  simp [advance]

def reach (context : Context) : List Bool :=
  (advance context)^[context.2.length] (List.replicate context.2.length false)

private theorem reach_polyTime : ComputableInPolyTime reach contextEncoding encBits := by
  have htarget : ComputableInPolyTime (fun p : Context => p.2) contextEncoding encBits := snd _ _
  have hcount := length_bits.comp htarget
  have hwidth := length_bits.comp htarget
  have hinit := (bitsReplicate false).comp hwidth
  have hpoly := hwidth.polyBounded
  have h := ComputableInPolyTime.iterateWith_of_bounded_growth id' hcount hinit advance_polyTime hpoly
    (fun context state => by simp only [encBits_apply, advance_length, Function.comp_def]; omega)
  exact h


private theorem advance_view (d : GuardDescriptor) (r : Fin d.labels.length)
    (A B : Finset (Fin d.labels.length)) :
    advance (d.records.map recordView, Bitset.encode A) (Bitset.encode B) =
      Bitset.encode ((d.table r).advance A B) := by
  apply List.ext_getElem (by simp [advance, Bitset.encode])
  intro i hi hi'
  have hin : i < d.labels.length := by simpa [advance, Bitset.encode] using hi
  have hget (S : Finset (Fin d.labels.length)) :
      (Bitset.encode S).getD i false = decide ((⟨i, hin⟩ : Fin d.labels.length) ∈ S) := by
    simpa only [GuardWords.readBit, List.getD_eq_getElem?_getD] using
      Bitset.read_encode S ⟨i, hin⟩
  simp only [advance, List.getElem_map, List.getElem_range]
  conv_rhs => simp only [Bitset.encode, List.getElem_ofFn]
  change ((Bitset.encode B).getD i false ||
    ((Bitset.encode A).getD i false && (d.records.map recordView).any
      (fun q => decide (q.1 = i) && subset q.2 (Bitset.encode B)))) =
    decide ((⟨i, hin⟩ : Fin d.labels.length) ∈ (d.table r).advance A B)
  rw [hget, hget]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
    List.mem_map, recordView]
  rw [Reset.GuardTable.mem_advance]
  simp only [GuardDescriptor.table, Reset.GuardTable.Enabled, GuardDescriptor.mem_guards]
  constructor
  · rintro (h | ⟨ha, p, ⟨q, hq, rfl⟩, he, hs⟩)
    · exact Or.inl h
    · refine Or.inr ⟨ha, q.2, ?_, ?_⟩
      · have hqi : q.1 = ⟨i, hin⟩ := Fin.ext he
        simpa only [← hqi, Prod.eta] using hq
      · change q.2 ⊆ B
        simpa only [subset_encode, decide_eq_true_eq] using hs
  · rintro (h | ⟨ha, S, hs, hsub⟩)
    · exact Or.inl h
    · exact Or.inr ⟨ha, _, ⟨(⟨i, hin⟩, S), hs, rfl⟩, rfl,
        by simpa only [subset_encode, decide_eq_true_eq] using (show S ⊆ B from hsub)⟩

theorem empty_encode (n : ℕ) :
    List.replicate n false = Bitset.encode (∅ : Finset (Fin n)) := by
  apply List.ext_getElem (by simp [Bitset.encode])
  intro i hi hi'
  simp [Bitset.encode]

private theorem reach_view (d : GuardDescriptor) (r : Fin d.labels.length)
    (A : Finset (Fin d.labels.length)) :
    reach (d.records.map recordView, Bitset.encode A) =
      Bitset.encode ((d.table r).reached A d.labels.length) := by
  have hiter (k : ℕ) :
      (advance (d.records.map recordView, Bitset.encode A))^[k]
        (List.replicate d.labels.length false) = Bitset.encode ((d.table r).reached A k) := by
    induction k with
    | zero => exact empty_encode _
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, advance_view]
      rfl
  simpa only [reach, Bitset.length_encode] using hiter d.labels.length

/-- Greedy constructibility test on the native listed-record representation.
Its clock is the prerequisite word width, independent of all binary names. -/
def constructible (context : List Record × List Bool) : Bool :=
  decide (reach context = context.2)

@[fun_prop] theorem constructible_polyTime : ComputableInPolyTime constructible
    (encPair (encList recordEncoding) encBits) encBool :=
  decide_eq' reach_polyTime (snd _ _)

/-- This native scan tests the independently defined construction predicate
for the exact prerequisite table, without assuming well-formedness. -/
theorem constructible_view (d : GuardDescriptor) (r : Fin d.labels.length)
    (A : Finset (Fin d.labels.length)) :
    constructible (d.records.map recordView, Bitset.encode A) = true ↔
      (d.table r).Constructible A := by
  rw [constructible, decide_eq_true_eq, reach_view d r, Bitset.encode_injective.eq_iff]
  constructor
  · intro he
    rw [← he]
    exact (d.table r).constructible_reached A _
  · intro hc
    have hm : Monotone ((d.table r).reached A) :=
      monotone_nat_of_le_succ (fun k => (d.table r).reached_mono_step A k)
    have hcard : A.card ≤ d.labels.length := by simpa using Finset.card_le_univ A
    apply Finset.Subset.antisymm ((d.table r).reached_subset A _)
    have hh := hm hcard
    rwa [(d.table r).reached_eq_of_constructible hc] at hh

end KFOL.Complexity.ReachMachine
