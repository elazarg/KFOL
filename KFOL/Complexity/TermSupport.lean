module

public import KFOL.Complexity.TermMachine

/-! # Polynomial-time collection of binary variable occurrences and support -/

@[expose] public section

namespace KFOL.Complexity.TermSupport

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.Algorithms

private def outputs (t : Reset.Term ℕ) : List ℕ := t.guardEntries.map Prod.fst

private theorem outputs_var (j : ℕ) : outputs (.var j) = [j] := rfl

private theorem outputs_step (s t : Reset.Term ℕ) :
    outputs (Reset.Term.step s t) = outputs t ++ outputs s := by
  simp only [outputs, Reset.Term.guardEntries_step, List.map_append, List.map_map, Function.comp_def]

private theorem outputs_length_le (t : Reset.Term ℕ) :
    (encList encNat (outputs t)).length ≤ (TermCode.encode t).length := by
  induction t using Reset.Term.induction_reset with
  | var j =>
    simp only [outputs_var, encList_cons, encList_nil, List.append_nil, length_frame,
      encNat_apply, TermCode.encode_var, List.length_cons, Words.delimit_length,
      Words.BinaryNatCode.length_encode, ← Nat.size_eq_bits_len]
    omega
  | step s t hs ht =>
    simp only [outputs_step, encList_append, List.length_append, TermCode.encode_step, List.length_cons]
    omega

private theorem outputs_polyTime : ComputableInPolyTime outputs TermMachine.termEncoding (encList encNat) := by
  apply TermMachine.fold_polyTime (encList encNat) outputs (fun j => [j])
    (fun p : List ℕ × List ℕ => p.2 ++ p.1) outputs_var outputs_step
    (cons' id' (const [])) (listAppend' (snd _ _) (fst _ _)) 1 1
  intro t
  simpa only [Nat.pow_one, Nat.one_mul] using
    (outputs_length_le t).trans (Nat.le_add_right _ 1)

private def insertFresh (seen : List ℕ) (j : ℕ) : List ℕ :=
  if j ∈ seen then seen else j :: seen

private theorem dedup_eq_fold (labels : List ℕ) :
    labels.dedup = labels.reverse.foldl insertFresh [] := by
  have hfold (labels : List ℕ) : labels.dedup = labels.foldr (fun j seen => insertFresh seen j) [] := by
    induction labels with
    | nil => rfl
    | cons j labels ih => rw [List.dedup_cons', List.foldr_cons, ← ih]; rfl
  rw [hfold, List.foldr_eq_foldl_reverse]

private theorem insertFresh_polyTime : ComputableInPolyTime
    (fun p : (List ℕ × List ℕ) × ℕ => insertFresh p.1.2 p.2)
    (encPair (encPair (encList encNat) (encList encNat)) encNat) (encList encNat) := by
  let input := encPair (encPair (encList encNat) (encList encNat)) encNat
  have hs : ComputableInPolyTime (fun p : (List ℕ × List ℕ) × ℕ => p.1.2) input (encList encNat) := by fun_prop
  have hj := snd (encPair (encList encNat) (encList encNat)) encNat
  have hl : ComputableInPolyTime (fun p : ((List ℕ × List ℕ) × ℕ) × ℕ => p.1.2)
      (encPair input encNat) encNat := by fun_prop
  have hq := snd input encNat
  have hmem := anyWithInput (test := fun (p : (List ℕ × List ℕ) × ℕ) (q : ℕ) => decide (p.2 = q))
    hs (decide_eq' hl hq)
  have h := hmem.ite hs (cons' hj hs)
  convert h using 1
  funext p
  have hm : (∃ x ∈ p.1.2, p.2 = x) ↔ p.2 ∈ p.1.2 := by
    constructor
    · rintro ⟨x, hx, he⟩; exact he.symm ▸ hx
    · intro hj; exact ⟨p.2, hj, rfl⟩
  simp only [insertFresh, List.any_eq_true, decide_eq_true_eq, hm]

/-- Erase repeated binary names in the exact rightmost-occurrence order used
by mathlib's `List.dedup`. The loop charges name bit lengths, never their values. -/
@[fun_prop] theorem dedup_polyTime : ComputableInPolyTime (List.dedup (α := ℕ))
    (encList encNat) (encList encNat) := by
  have hr := (id' (encIn := encList encNat)).listReverseWithInput
  have h := foldlWithInput_of_bounded_growth (encIn := encList encNat) (encA := encNat)
    (encB := encList encNat) (list := List.reverse) (init := fun _ => [])
    (step := fun (_ : List ℕ) seen j => insertFresh seen j)
    (const []) ⟨hr, insertFresh_polyTime, inferInstance, inferInstance⟩
    (growth := fun labels => 2 * (encList encNat labels).length + 1)
    ⟨((PolyBounded.const 2).mul (id' (encIn := encList encNat)).polyBounded_length).add (.const 1),
      fun labels seen j hj => by
        have hj' : j ∈ labels := List.mem_reverse.mp hj
        have hb := SizedListEncoding.length_elem_le (encA := encNat) (encL := encList encNat) labels j hj'
        unfold insertFresh
        split
        · omega
        · simp only [encList_cons, List.length_append, length_frame]
          omega⟩
  convert h using 1
  funext labels
  exact dedup_eq_fold labels

/-- The actual support dictionary, including its established order, is
computed uniformly in time polynomial in the original binary term code. -/
@[fun_prop] theorem labels_polyTime : ComputableInPolyTime SupportIndex.labels
    TermMachine.termEncoding (encList encNat) := dedup_polyTime.comp outputs_polyTime

end KFOL.Complexity.TermSupport
