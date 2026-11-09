module

public import KFOL.Complexity.OwnerRuntime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-! # Complete owner saturation runs with recorded construction frames -/

@[expose] public section

namespace KFOL.Complexity.OwnerRuntime

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.Algorithms

abbrev RawRun := RawGuard × List (ℕ × ℕ)
abbrev runEncoding := encPair guardEncoding (encList (encPair encNat encNat))

def advance (context : Context) (state : RawRun) : RawRun :=
  match next context state.1 with
  | none => state
  | some p => (update state.1 p.1 p.2, state.2 ++ [p])

theorem advance_polyTime : ComputableInPolyTime
    (fun p : Context × RawRun => advance p.1 p.2)
    (encPair contextEncoding runEncoding) runEncoding := by
  let input := encPair contextEncoding runEncoding
  have hc := fst contextEncoding runEncoding
  have hs : ComputableInPolyTime (fun p : Context × RawRun => p.2.1) input guardEncoding := by fun_prop
  have hn := next_polyTime.comp (hc.prod hs)
  have hstate : ComputableInPolyTime (fun p : (Context × RawRun) × (ℕ × ℕ) => p.1.2.1)
      (encPair input (encPair encNat encNat)) guardEncoding := by fun_prop
  have hp := snd input (encPair encNat encNat)
  have hu := update_polyTime.comp (hstate.prod hp)
  have hold : ComputableInPolyTime (fun p : (Context × RawRun) × (ℕ × ℕ) => p.1.2.2)
      (encPair input (encPair encNat encNat)) (encList (encPair encNat encNat)) := by fun_prop
  have hadd := listAppend' hold (cons' hp (const []))
  have h := hn.optionElimWithInput (body := fun (p : Context × RawRun) (q : ℕ × ℕ) =>
    (update p.2.1 q.1 q.2, p.2.2 ++ [q]))
    (snd contextEncoding runEncoding) (hu.prod hadd)
  convert h using 1
  funext p
  change advance p.1 p.2 = (next p.1 p.2.1).elim p.2 _
  unfold advance
  cases next p.1 p.2.1 <;> rfl

private theorem update_length (state : RawGuard) (w z : ℕ) :
    (guardEncoding (update state w z)).length ≤ (guardEncoding state).length := by
  simp only [guardEncoding, length_encPair, encBits_apply, update, union, difference,
    single, List.length_zipWith, List.length_map, List.length_range]
  omega

private theorem next_bounds {context : Context} {state : RawGuard} {w z : ℕ}
    (h : next context state = some (w, z)) :
    w < context.2.2.1.length ∧ z < context.2.2.1.length := by
  have hm := List.mem_of_find?_eq_some h
  simpa only [candidates, List.product, List.mem_flatMap, List.mem_map, List.mem_range,
    Prod.mk.injEq, exists_eq_right_right, exists_eq_right] using hm

private theorem advance_growth (context : Context) (state : RawRun) :
    (runEncoding (advance context state)).length ≤
      (runEncoding state).length + (6 * context.2.2.1.length + 3) := by
  unfold advance
  cases hn : next context state.1 with
  | none => simp only; omega
  | some p =>
    have hb := next_bounds hn
    have hw : (encNat p.1).length ≤ context.2.2.1.length := by
      have h : p.1.size ≤ context.2.2.1.length :=
        Nat.size_le.mpr (Nat.lt_trans hb.1 Nat.lt_two_pow_self)
      have he := Nat.size_eq_bits_len p.1
      simp only [encNat_apply]
      omega
    have hz : (encNat p.2).length ≤ context.2.2.1.length := by
      have h : p.2.size ≤ context.2.2.1.length :=
        Nat.size_le.mpr (Nat.lt_trans hb.2 Nat.lt_two_pow_self)
      have he := Nat.size_eq_bits_len p.2
      simp only [encNat_apply]
      omega
    have hu := update_length state.1 p.1 p.2
    simp only [runEncoding, length_encPair, encList_append, List.length_append,
      encList_cons, encList_nil, List.append_nil, length_frame, length_encPair] at *
    omega

def initialRun (context : Context) : RawRun :=
  ((single (context.2.2.1.length, context.1.1), List.replicate context.2.2.1.length false), [])

def run (context : Context) : RawRun :=
  (advance context)^[2 * context.2.2.1.length] (initialRun context)

private theorem initialRun_polyTime : ComputableInPolyTime initialRun contextEncoding runEncoding := by
  have hm : ComputableInPolyTime (fun context : Context => context.2.2.1) contextEncoding encBits := by fun_prop
  have hr : ComputableInPolyTime (fun context : Context => context.1.1) contextEncoding encNat := by fun_prop
  have hw := length_bits.comp hm
  have hindices := ComputableInPolyTime.range.comp hw
  have hi := unary_to_binary.comp (snd contextEncoding encUnary)
  have hroot := hr.comp (fst contextEncoding encUnary)
  have hsingle := mapToBitsWithInput (f := fun (context : Context) (i : ℕ) => decide (i = context.1.1))
    hindices (decide_eq' hi hroot)
  exact (hsingle.prod ((bitsReplicate false).comp hw)).prod (const [])

/-- The complete twice-width saturation run, including every construction frame,
uses native polynomial time. Width and all retained frames are charged from the
original encoded context on every loop iteration. -/
theorem run_polyTime : ComputableInPolyTime run contextEncoding runEncoding := by
  have hm : ComputableInPolyTime (fun context : Context => context.2.2.1) contextEncoding encBits := by fun_prop
  have hw := length_bits.comp hm
  have hcount := unary_mul.comp ((const 2).prod hw)
  have hgrowth := (unary_add.comp ((unary_mul.comp ((const 6).prod hw)).prod (const 3))).polyBounded
  exact ComputableInPolyTime.iterateWith_of_bounded_growth id' hcount initialRun_polyTime
    advance_polyTime hgrowth advance_growth

def runView {n : ℕ} (result : Owner.SaturationState (Fin n) × List (Fin n × Fin n)) : RawRun :=
  (stateView result.1, result.2.map (fun p => (p.1.val, p.2.val)))

private theorem initialRun_view {n : ℕ} (T : Owner.GuardTable (Fin n)) (j : Fin n)
    (g : Owner.GuardPair (Fin n)) :
    initialRun (tableView T, entryView (j, g)) =
      runView (Owner.SaturationState.initial T.root, []) := by
  simp only [initialRun, entryView, tableView, Bitset.length_encode, runView, stateView,
    Owner.SaturationState.initial, List.map_nil]
  congr 2
  · apply List.ext_getElem (by simp [single, Bitset.encode])
    intro i hi hi'
    simp [single, Bitset.encode, Fin.ext_iff]
  · apply List.ext_getElem (by simp [Bitset.encode])
    intro i hi hi'
    simp [Bitset.encode]

/-- All states and recorded frames coincide with the independent finite owner
program, for every clock value and every table. -/
theorem iterate_view {n : ℕ} (T : Owner.GuardTable (Fin n)) (j : Fin n)
    (g : Owner.GuardPair (Fin n)) (clock : ℕ) :
    (advance (tableView T, entryView (j, g)))^[clock]
      (initialRun (tableView T, entryView (j, g))) =
      runView (T.run (List.finRange n) j g clock) := by
  induction clock with
  | zero => simpa only [Function.iterate_zero_apply, Owner.GuardTable.run] using initialRun_view T j g
  | succ clock ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [advance, runView]
    rw [next_view]
    simp only [Owner.GuardTable.run]
    cases hn : T.next (List.finRange n) j g (T.run (List.finRange n) j g clock).1 with
    | none => rfl
    | some p =>
      simp only [Option.map_some, update_view, List.map_append, List.map_cons, List.map_nil]

/-- The complete native program is exactly the source run at its actual clock. -/
theorem run_view {n : ℕ} (T : Owner.GuardTable (Fin n)) (j : Fin n)
    (g : Owner.GuardPair (Fin n)) :
    run (tableView T, entryView (j, g)) =
      runView (T.run (List.finRange n) j g (2 * n)) := by
  simpa only [run, entryView, Bitset.length_encode] using iterate_view T j g (2 * n)

end KFOL.Complexity.OwnerRuntime
