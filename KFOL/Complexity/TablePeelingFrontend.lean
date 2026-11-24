module

public import KFOL.Complexity.AddressedPointLanguage
public import KFOL.Complexity.AddressedPointCorrectness
public import KFOL.Core.Peeling
public import KFOL.Complexity.RecognitionHardness

/-! # Explicit rows for the row-deletion upper bound

A row supplies one input menu per variable and one upper output menu. The
language requires agreement with the output menu on every listed row.
Binary owner identifiers outside the role set are ignored in this intermediate
presentation. The full-table frontend rejects such outputs.
-/

@[expose] public section
namespace KFOL.Complexity.TablePeeling

open Turing.MultiTapeTM ComputableInPolyTime Core.ProfileBudgets AddressedPoint FullSparseEvaluation
open AddressTableOutput
attribute [local instance] Equational.coreStructure

abbrev Row := Menus × List ℕ
abbrev Input := ℕ × List Row
abbrev rowEncoding := encPair menusEncoding AddressedEnvelope.namesEncoding
abbrev inputEncoding := encPair encUnary (encList rowEncoding)

def allowed {K : ℕ} (xs : List ℕ) : Set (Fin K) := {r | r.val ∈ xs}

/-- Unused and malformed input columns have the full menu. -/
noncomputable def readMenu {K : ℕ} (hK : 0 < K) (xs : List ℕ) : WinnerSet (Fin K) :=
by
  classical
  exact if h : (allowed xs : Set (Fin K)).Nonempty then ⟨allowed xs,h⟩ else
    ⟨Set.univ,⟨⟨0,hK⟩,Set.mem_univ _⟩⟩

noncomputable def values {K : ℕ} (hK : 0 < K) (p : Input) (i : Fin p.2.length)
    (j : Fin p.1) : WinnerSet (Fin K) :=
  readMenu hK (p.2[i.val].1.getD j.val [])

def bounds (K : ℕ) (p : Input) (i : Fin p.2.length) : Set (Fin K) := allowed p.2[i.val].2

/-- Exact interpolation of the explicitly listed rows. -/
def Accepts {K : ℕ} (hK : 0 < K) (p : Input) : Prop :=
  ∃ t : CoreTerm (Fin K) (Fin p.1), ∀ i, (t.realize (values hK p i)).val = bounds K p i

def rows (k : ℕ) (p : TableInput) : List Row :=
  (List.range p.2.length).map fun i => (tuple k p.1 i, p.2.getD i [])

def valid (k : ℕ) (p : TableInput) : Bool :=
  decide (p.2.length = (2^k-1)^p.1) && p.2.all (fun xs => xs.all (fun x => decide (x < k)))

def expand (k : ℕ) (p : TableInput) : Input := if valid k p then (p.1, rows k p) else (0,[])

@[simp] theorem rows_length (k : ℕ) (p : TableInput) : (rows k p).length = p.2.length := by simp [rows]

theorem valid_iff (k : ℕ) (p : TableInput) : valid k p = true ↔
    p.2.length = (2^k-1)^p.1 ∧ ∀ xs ∈ p.2, ∀ x ∈ xs, x < k := by simp [valid,List.all_eq_true]

theorem read_represents {k : ℕ} (hk : 0 < k) (i j : ℕ) :
    Represents (menu k i j) (readMenu hk (menu k i j)) := by
  let m := mask k i j
  have base : 0 < 2^k-1 := by
    have : 2^1 ≤ 2^k := Nat.pow_le_pow_right (by decide) hk
    omega
  have cap : m < 2^k := by
    have small := Nat.mod_lt (i / (2^k-1)^j) base
    change i / (2^k-1)^j % (2^k-1) + 1 < 2^k
    omega
  have nn : m ≠ 0 := Nat.succ_ne_zero _
  have bit := Nat.testBit_log2 nn
  have small : m.log2 < k := (Nat.log2_lt nn).mpr cap
  have present : (allowed (menu k i j) : Set (Fin k)).Nonempty :=
    ⟨⟨m.log2,small⟩,(menu_mem ..).mpr ⟨small,bit⟩⟩
  rw [readMenu, dite_eq_left present]
  apply represents_ext
  · exact fun n mem => ((menu_mem ..).mp mem).1
  · intro _; rfl

private theorem read_row {k : ℕ} (hk : 0 < k) (p : TableInput)
    (i : Fin (rows k p).length) (j : Fin p.1) :
    values hk (p.1, rows k p) i j = readMenu hk (menu k i.val j.val) := by
  unfold values
  simp only [rows, List.getElem_map, List.getElem_range]
  rw [tuple_getD _ _ _ _ j.isLt]

private theorem bounds_row (k : ℕ) (p : TableInput) (i : Fin (rows k p).length) :
    bounds k (p.1, rows k p) i = allowed (p.2.getD i.val []) := by
  simp only [bounds,rows,List.getElem_map,List.getElem_range]

private theorem no_nullary (k : ℕ) (hk : 0 < k) : ¬ Accepts hk (0,[]) := by
  rintro ⟨t,_⟩
  have impossible (word : CoreTerm (Fin k) (Fin 0)) : False := by
    induction word using Core.induction_choice with
    | var j => exact Fin.elim0 j
    | choice _ _ _ hl _ => exact hl
  exact impossible t

private theorem valid_of_raw {k : ℕ} (hk : 0 < k) {p : TableInput} (yes : RawAccepts k p) :
    valid k p = true := by
  obtain ⟨length,t,ht⟩ := yes
  refine (valid_iff k p).mpr ⟨length,?_⟩
  intro xs mem n hn
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp mem
  have rep := ht i (length ▸ hi) (fun j => readMenu hk (menu k i j.val)) (fun j => read_represents hk i j.val)
  rw [List.getD_eq_getElem _ _ hi] at rep
  exact represents_lt rep hn

theorem expand_iff {k : ℕ} (hk : 0 < k) (p : TableInput) : Accepts hk (expand k p) ↔ RawAccepts k p := by
  by_cases validP : valid k p = true
  · obtain ⟨length,validRows⟩ := (valid_iff k p).mp validP
    rw [expand,ite_eq_left validP]
    constructor
    · rintro ⟨t,ht⟩
      refine ⟨length,t,fun i hi v all => ?_⟩
      have mem : i < p.2.length := length.symm ▸ hi
      let ii : Fin (rows k p).length := ⟨i,by simpa using mem⟩
      have hv : v = values hk (p.1, rows k p) ii := by
        funext j
        rw [read_row]
        exact (represents_equal_iff (all j) (read_represents hk _ _)).mp rfl
      rw [hv]
      have target := ht ii
      rw [bounds_row] at target
      apply represents_ext
      · rw [List.getD_eq_getElem _ _ mem]
        exact validRows _ (List.getElem_mem ..)
      · intro r
        rw [target]
        rfl
    · rintro ⟨_,t,ht⟩
      refine ⟨t,fun ii => ?_⟩
      have mem : ii.val < p.2.length := by simpa using ii.isLt
      have rep := ht ii.val (length ▸ mem) (values hk (p.1, rows k p) ii)
        (fun j => by rw [read_row]; exact read_represents hk _ _)
      ext r
      rw [bounds_row]
      exact (represents_mem rep r).symm
  · rw [expand,ite_eq_right validP]
    exact iff_of_false (no_nullary k hk) (fun h => validP (valid_of_raw hk h))

private theorem valid_poly (k : ℕ) : ComputableInPolyTime (valid k) tableEncoding encBool := by
  let num := fst encUnary menusEncoding
  let data := snd encUnary menusEncoding
  have size := (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.length
    AddressedEnvelope.namesEncoding)).comp data
  have target := binary_pow' (const (2^k-1)) num
  have same := decide_eq' (unary_to_binary.comp size) target
  have bits : ComputableInPolyTime (fun v : List ℕ => v.all (fun j => decide (j < k)))
      AddressedEnvelope.namesEncoding encBool :=
    allWithInput (test := fun (_ : List ℕ) j => decide (j < k)) id'
      (binary_lt' (snd _ _) (const k))
  have inRange := allWithInput (test := fun (_ : TableInput) xs =>
    xs.all (fun j => decide (j < k))) data (bits.comp (snd _ _))
  exact bool_and' same inRange

private theorem rows_poly (k : ℕ) : ComputableInPolyTime (rows k) tableEncoding (encList rowEncoding) := by
  let vals := snd encUnary menusEncoding
  have size := (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.length
    AddressedEnvelope.namesEncoding)).comp vals
  have i := snd tableEncoding encUnary
  have raw := fst tableEncoding encUnary
  have indexed := tuple_poly k ((fst encUnary menusEncoding).comp raw) i
  have role : ComputableInPolyTime (fun r : ℕ => r) encUnary encNat := unary_to_binary
  have menuId : ComputableInPolyTime (fun v : List ℕ => v) (encList encUnary) AddressedEnvelope.namesEncoding := by
    rw [show (fun v : List ℕ => v) = List.map (fun i : ℕ => i) by funext v; exact (List.map_id' v).symm]
    exact ComputableInPolyTime.map role
  have tupleId : ComputableInPolyTime (fun v : Menus => v) (encList (encList encUnary)) menusEncoding := by
    rw [show (fun v : Menus => v) = List.map (fun m : List ℕ => m) by funext v; exact (List.map_id' v).symm]
    exact ComputableInPolyTime.map menuId
  exact mapWithInput (f := fun (p : TableInput) (i : ℕ) => (tuple k p.1 i, p.2.getD i [])) (ComputableInPolyTime.range.comp size)
    ((tupleId.comp indexed).prod ((listGetD (encA := AddressedEnvelope.namesEncoding)
      (encL := menusEncoding) []).comp ((vals.comp raw).prod i)))

theorem expand_poly (k : ℕ) : ComputableInPolyTime (expand k) tableEncoding inputEncoding :=
  (valid_poly k).ite ((fst encUnary menusEncoding).prod (rows_poly k)) (const (0,[]))

theorem raw_reducible {k : ℕ} (hk : 0 < k) :
    Cslib.Complexity.PolyTimeReducible tableEncoding inputEncoding
      {p | RawAccepts k p} {p | Accepts hk p} :=
  ⟨expand k,expand_poly k,fun p => (expand_iff hk p).symm⟩

end KFOL.Complexity.TablePeeling
