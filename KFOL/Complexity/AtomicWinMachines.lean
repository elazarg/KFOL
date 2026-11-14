module

public import KFOL.Reductions.AtomicWin
public import KFOL.Algorithms.FullTermCode.View
public import KFOL.Complexity.FullTermMachines
public import KFOL.Complexity.ResetUnionReduction

/-! # Native polynomial-time compilation of atomic winner satisfiability -/

@[expose] public section

namespace KFOL.Complexity.AtomicWinMachines

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FullTermCode KFOL.Reductions

variable {K : ℕ}

abbrev Tree (K : ℕ) := Term (Fin K) ℕ

/-- The original explicit-array term code, without enumerating permutations. -/
def termEncoding (K : ℕ) : Tree K ↪ List Bool :=
  ⟨fun term => FullTermCode.encode (FullTermCode.view term),
    fun _ _ equal => FullTermCode.view_injective (FullTermCode.encode_injective equal)⟩

@[simp] theorem termEncoding_apply (term : Tree K) :
    termEncoding K term = FullTermCode.encode (FullTermCode.view term) := rfl

theorem view_polyTime : ComputableInPolyTime (@FullTermCode.view K)
    (termEncoding K) FullTermMachines.termEncoding := .of_eq (fun _ => rfl)

theorem var_polyTime : ComputableInPolyTime (fun name => (.var name : Tree K))
    encNat (termEncoding K) :=
  FullTermMachines.var_polyTime.of_enc_eq (fun _ => rfl)

theorem choice_polyTime (owner : Fin K) : ComputableInPolyTime
    (fun pair : Tree K × Tree K => .choice owner pair.1 pair.2)
    (encPair (termEncoding K) (termEncoding K)) (termEncoding K) := by
  have hl := view_polyTime.comp (fst (termEncoding K) (termEncoding K))
  have hr := view_polyTime.comp (snd (termEncoding K) (termEncoding K))
  have h := FullTermMachines.construct_polyTime.comp
    ((const (⟨2, .choice owner.val⟩ : FullTermCode.Operation)).prod
      (cons' hl (cons' hr (const []))))
  apply h.of_enc_eq
  intro pair
  change encode (view (.choice owner pair.1 pair.2)) =
    encode (FullTermMachines.construct ⟨2, .choice owner.val⟩ [view pair.1, view pair.2])
  congr 1
  simp only [FullTermCode.view, FullTermMachines.construct]
  congr 1
  funext i
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl <;> simp

theorem rename_polyTime (permutation : Equiv.Perm (Fin K)) : ComputableInPolyTime
    (fun term : Tree K => .rename permutation term) (termEncoding K) (termEncoding K) := by
  have h := FullTermMachines.construct_polyTime.comp
    ((const (⟨1, .rename (FullTermCode.permutationArray permutation)⟩ : FullTermCode.Operation)).prod
      (cons' (view_polyTime (K := K)) (const [])))
  apply h.of_enc_eq
  intro term
  change encode (view (.rename permutation term)) =
    encode (FullTermMachines.construct ⟨1, .rename (permutationArray permutation)⟩ [view term])
  congr 1
  simp only [FullTermCode.view, FullTermMachines.construct]
  congr 1
  funext i
  have hi : i = 0 := by omega
  subst i
  simp

def choiceHeader (owner : Fin K) : ℕ :=
  1 + (Words.delimit (FullTermCode.encodeOperation ⟨2, .choice owner.val⟩)).length

theorem choice_length (owner : Fin K) (left right : Tree K) :
    (termEncoding K (.choice owner left right)).length =
      (termEncoding K left).length + (termEncoding K right).length + choiceHeader owner := by
  simp [FullTermCode.view,
    List.ofFn_succ, choiceHeader, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem fold_polyTime (owner : Fin K) : ComputableInPolyTime
    (fun pair : List (Tree K) × Tree K => pair.1.foldr (.choice owner) pair.2)
    (encPair (encList (termEncoding K)) (termEncoding K)) (termEncoding K) := by
  let input := encPair (encList (termEncoding K)) (termEncoding K)
  have hl := fst (encList (termEncoding K)) (termEncoding K)
  have hr := (ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.listReverse (termEncoding K))).comp hl
  have hs : ComputableInPolyTime
      (fun pair : ((List (Tree K) × Tree K) × Tree K) × Tree K => pair.1.2)
      (encPair (encPair input (termEncoding K)) (termEncoding K)) (termEncoding K) := by fun_prop
  have ht := snd (encPair input (termEncoding K)) (termEncoding K)
  have hstep := (choice_polyTime owner).comp (ht.prod hs)
  have hg := hl.polyBounded_length.add (PolyBounded.const (choiceHeader owner))
  have h := foldlWithInput_of_bounded_growth
    (list := fun pair : List (Tree K) × Tree K => pair.1.reverse)
    (init := fun pair => pair.2)
    (step := fun _ state term => .choice owner term state)
    (snd (encList (termEncoding K)) (termEncoding K)) ⟨hr, hstep, inferInstance, inferInstance⟩
    (growth := fun pair => (encList (termEncoding K) pair.1).length + choiceHeader owner) ⟨hg, ?_⟩
  · convert h using 1
    funext pair
    rw [List.foldl_reverse]
  · intro pair state term member
    have ht := SizedListEncoding.length_elem_le (encA := termEncoding K)
      (encL := encList (termEncoding K)) pair.1 term (List.mem_reverse.mp member)
    rw [choice_length]
    omega

theorem positive_polyTime (test : Term (Fin K) Unit) : ComputableInPolyTime
    (AtomicWin.positive test) encNat (termEncoding K) := by
  induction test with
  | winner role => exact const (Term.winner role : Tree K)
  | var name => exact var_polyTime
  | choice owner left right ihl ihr => exact (choice_polyTime owner).comp (ihl.prod ihr)
  | rename permutation term ih => exact (rename_polyTime permutation).comp ih

theorem literal_polyTime (a b : Fin K) (test : Term (Fin K) Unit) :
    ComputableInPolyTime (AtomicWin.literal a b test) ResetUnionReduction.literalEncoding (termEncoding K) := by
  classical
  have hp := (positive_polyTime test).comp (fst encNat encBool)
  have hn := (rename_polyTime (AtomicWin.negation a b)).comp hp
  convert (snd encNat encBool).ite hp hn using 1
  funext input
  rfl

theorem clause_polyTime (a b : Fin K) (test : Term (Fin K) Unit) :
    ComputableInPolyTime (AtomicWin.clause a b test) ResetUnionReduction.clauseEncoding (termEncoding K) := by
  have terms := mapWithInput (f := fun (_ : Clause) item => AtomicWin.literal a b test item)
    (id' (encIn := ResetUnionReduction.clauseEncoding))
    ((literal_polyTime a b test).comp (snd ResetUnionReduction.clauseEncoding ResetUnionReduction.literalEncoding))
  have h := (fold_polyTime a).comp (terms.prod (const (.winner b)))
  convert h using 1
  funext input
  simp [AtomicWin.clause, List.foldr_map]

theorem formula_polyTime (a b : Fin K) (test : Term (Fin K) Unit) :
    ComputableInPolyTime (AtomicWin.formula a b test)
      ResetUnionReduction.cnfEncoding (termEncoding K) := by
  have terms := mapWithInput (f := fun (_ : CNF) item => AtomicWin.clause a b test item)
    (id' (encIn := ResetUnionReduction.cnfEncoding))
    ((clause_polyTime a b test).comp (snd ResetUnionReduction.cnfEncoding ResetUnionReduction.clauseEncoding))
  have h := (fold_polyTime b).comp (terms.prod (const (.winner a)))
  convert h using 1
  funext input
  simp [AtomicWin.formula, List.foldr_map]

end KFOL.Complexity.AtomicWinMachines
