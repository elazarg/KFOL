module

public import KFOL.Complexity.TermSupport

/-! # Native guard extraction from original binary syntax -/

@[expose] public section

namespace KFOL.Complexity.GuardExtraction

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.Algorithms

abbrev Entry := ℕ × List ℕ
abbrev Collection := ℕ × List Entry
abbrev entryEncoding := encPair encNat (encList encNat)
abbrev collectionEncoding := encPair encNat (encList entryEncoding)

/-- Raw occurrence guards retain prerequisite names as lists until the one
shared support dictionary converts them into membership words. -/
def collect : Reset.Term ℕ → Collection
  | .var j => (j, [(j, [])])
  | .func .reset args =>
    let left := collect (args 0)
    let right := collect (args 1)
    (right.1, right.2 ++ left.2.map (fun p => (p.1, right.1 :: p.2)))

@[simp] theorem collect_var (j : ℕ) : collect (.var j) = (j, [(j, [])]) := rfl

theorem collect_step (s t : Reset.Term ℕ) :
    collect (Reset.Term.step s t) =
      ((collect t).1, (collect t).2 ++ (collect s).2.map (fun p => (p.1, (collect t).1 :: p.2))) := by
  simp [collect, Reset.Term.step]

@[simp] theorem collect_root (t : Reset.Term ℕ) : (collect t).1 = t.root := by
  induction t using Reset.Term.induction_reset with
  | var j => rfl
  | step s t hs ht => simp only [collect_step, Reset.Term.root_step, ht]

@[simp] theorem collect_count (t : Reset.Term ℕ) : (collect t).2.length = t.leafCount := by
  induction t using Reset.Term.induction_reset with
  | var j => rfl
  | step s t hs ht =>
    simp only [collect_step, List.length_append, List.length_map, hs, ht, Reset.Term.leafCount_step]
    omega

/-- Set interpretation recovers the exact established occurrence list. -/
theorem collect_entries (t : Reset.Term ℕ) :
    (collect t).2.map (fun p => (p.1, p.2.toFinset)) = t.guardEntries := by
  induction t using Reset.Term.induction_reset with
  | var j => rfl
  | step s t hs ht =>
    simp only [collect_step, Reset.Term.guardEntries_step, List.map_append, ht, List.map_map,
      Function.comp_def, List.toFinset_cons, collect_root]
    rw [← hs, List.map_map]
    rfl

private theorem root_length_le (t : Reset.Term ℕ) :
    (encNat (collect t).1).length ≤ (TermCode.encode t).length := by
  induction t using Reset.Term.induction_reset with
  | var j =>
    simp only [collect_var, encNat_apply, TermCode.encode_var, List.length_cons,
      Words.delimit_length, Words.BinaryNatCode.length_encode, ← Nat.size_eq_bits_len]
    omega
  | step s t hs ht =>
    simp only [collect_step, TermCode.encode_step, List.length_cons, List.length_append]
    omega

private theorem length_add_guard (records : List Entry) (root : ℕ) :
    (encList entryEncoding (records.map (fun p => (p.1, root :: p.2)))).length =
      (encList entryEncoding records).length + records.length * (4 * (encNat root).length + 2) := by
  induction records with
  | nil => simp
  | cons p records ih =>
    simp only [List.map_cons, encList_cons, List.length_append, length_frame, entryEncoding,
      length_encPair, List.length_cons, ih, Nat.add_mul, Nat.one_mul]
    omega

private theorem collect_length_le (t : Reset.Term ℕ) :
    (collectionEncoding (collect t)).length ≤ 12 * ((TermCode.encode t).length + 1) ^ 2 := by
  induction t using Reset.Term.induction_reset with
  | var j =>
    simp only [collect_var, collectionEncoding, length_encPair, encList_cons, encList_nil,
      List.append_nil, length_frame, entryEncoding, encNat_apply, List.length_nil,
      TermCode.encode_var, List.length_cons, Words.delimit_length, Words.BinaryNatCode.length_encode,
      ← Nat.size_eq_bits_len]
    nlinarith
  | step s t hs ht =>
    have hroot := root_length_le t
    have hcount : (collect s).2.length ≤ (TermCode.encode s).length := by
      rw [collect_count]
      exact TermCode.leafCount_le_length_encode s
    have hb : (collectionEncoding (collect (Reset.Term.step s t))).length ≤
        (collectionEncoding (collect s)).length + (collectionEncoding (collect t)).length +
        (collect s).2.length * (4 * (encNat (collect t).1).length + 2) := by
      simp only [collect_step, collectionEncoding, length_encPair, encList_append,
        List.length_append, length_add_guard]
      omega
    have hm := Nat.mul_le_mul hcount (show 4 * (encNat (collect t).1).length + 2 ≤
        4 * (TermCode.encode t).length + 2 by omega)
    simp only [TermCode.encode_step, List.length_cons, List.length_append]
    nlinarith

private theorem leaf_polyTime : ComputableInPolyTime
    (fun j : ℕ => (j, [(j, [])]) : ℕ → Collection) encNat collectionEncoding :=
  id'.prod (cons' (id'.prod (const [])) (const []))

private def join (p : Collection × Collection) : Collection :=
  (p.2.1, p.2.2 ++ p.1.2.map (fun q => (q.1, p.2.1 :: q.2)))

private theorem join_polyTime : ComputableInPolyTime join
    (encPair collectionEncoding collectionEncoding) collectionEncoding := by
  let input := encPair collectionEncoding collectionEncoding
  have hr : ComputableInPolyTime (fun p : Collection × Collection => p.2.1) input encNat := by fun_prop
  have hl : ComputableInPolyTime (fun p : Collection × Collection => p.1.2) input (encList entryEncoding) := by fun_prop
  have ht : ComputableInPolyTime (fun p : Collection × Collection => p.2.2) input (encList entryEncoding) := by fun_prop
  have hj : ComputableInPolyTime (fun p : (Collection × Collection) × Entry => p.2.1)
      (encPair input entryEncoding) encNat := by fun_prop
  have hroot : ComputableInPolyTime (fun p : (Collection × Collection) × Entry => p.1.2.1)
      (encPair input entryEncoding) encNat := by fun_prop
  have hguard : ComputableInPolyTime (fun p : (Collection × Collection) × Entry => p.2.2)
      (encPair input entryEncoding) (encList encNat) := by fun_prop
  have hm := mapWithInput (f := fun (p : Collection × Collection) (q : Entry) => (q.1, p.2.1 :: q.2))
    hl (hj.prod (cons' hroot hguard))
  exact hr.prod (listAppend' ht hm)

/-- Every prerequisite name and repeated occurrence is computed by one
certified bottom-up traversal, with a quadratic binary storage bound. -/
@[fun_prop] theorem collect_polyTime : ComputableInPolyTime collect TermMachine.termEncoding collectionEncoding :=
  TermMachine.fold_polyTime collectionEncoding collect (fun j => (j, [(j, [])])) join collect_var
    (fun s t => collect_step s t) leaf_polyTime join_polyTime 12 2 collect_length_le

end KFOL.Complexity.GuardExtraction
