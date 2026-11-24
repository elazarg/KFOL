module

public import KFOL.Complexity.AddressedPoint
public import KFOL.Complexity.FullSparseSemantics
public import KFOL.Core.ProfileBudgets.Pruning
public import KFOL.Core.AddressedRails

/-! # Full-table recognition as a language of explicit arrays

The input is an arity and a list of winner menus. Its index convention is the
base-(2^K-1) order of AddressTableOutput. Recognition quantifies over core
words on exactly the specified coordinates. -/

@[expose] public section
namespace KFOL.Complexity.AddressedPoint

open AddressTableOutput FullSparseEvaluation Core.ProfileBudgets Core.AddressedRails
open Turing.MultiTapeTM
attribute [local instance] Equational.coreStructure

abbrev TableInput := ℕ × Menus
abbrev tableEncoding := encPair encUnary menusEncoding

/-- At every valuation the word returns exactly the listed winning roles. -/
def RawAccepts (k : ℕ) (p : TableInput) : Prop :=
  p.2.length = (2^k-1)^p.1 ∧ ∃ t : CoreTerm (Fin k) (Fin p.1),
    ∀ (i : ℕ), i < (2^k-1)^p.1 → ∀ v : Fin p.1 → WinnerSet (Fin k),
      (∀ j, Represents (menu k i j.val) (v j)) →
      Represents (p.2.getD i []) (t.realize v)

theorem tuple_covers {k d : ℕ} (hk : 0 < k) (v : Fin d → WinnerSet (Fin k)) :
    ∃ i < (2^k-1)^d, ∀ j : Fin d, Represents (menu k i j.val) (v j) := by
  classical
  let flags := fun j r => decide (r ∈ (v j).val)
  have nonempty (j : Fin d) : ∃ r, flags j r = true := by
    obtain ⟨r,hr⟩ := (v j).property
    exact ⟨r,decide_eq_true hr⟩
  obtain ⟨i,hit,_⟩ := tuple_index_unique k d hk flags nonempty
  refine ⟨i.val,i.isLt,fun j => ?_⟩
  ext n
  constructor
  · intro hn
    obtain ⟨bound,bit⟩ := (menu_mem k i.val j.val n).mp hn
    refine ⟨⟨n,bound⟩,?_,rfl⟩
    exact of_decide_eq_true ((hit j ⟨n,bound⟩).symm.trans bit)
  · rintro ⟨r,yes,rfl⟩
    exact (menu_mem k i.val j.val r.val).mpr ⟨r.isLt,(hit j r).trans (decide_eq_true yes)⟩

/-- Correctly filling every row reduces recognition of the array to realizability
of its operation, with the variables transported by the coordinate numbering. -/
theorem rawAccepts_iff {k d : ℕ} (hk : 0 < k) {V : Type*} (index : V ≃ Fin d)
    {rows : Menus} (length : rows.length = (2^k-1)^d)
    (op : (V → WinnerSet (Fin k)) → WinnerSet (Fin k))
    (correct : ∀ i < (2^k-1)^d, ∀ v, (∀ j : V, Represents (menu k i (index j).val) (v j)) →
      Represents (rows.getD i []) (op v)) :
    RawAccepts k (d,rows) ↔ ∃ t : CoreTerm (Fin k) V, ∀ v, t.realize v = op v := by
  constructor
  · rintro ⟨_,t,word⟩
    refine ⟨t.relabel index.symm,fun v => ?_⟩
    obtain ⟨i,hi,all⟩ := tuple_covers hk (v ∘ index.symm)
    have agree := word i hi (v ∘ index.symm) all
    have result := correct i hi v (fun j => by simpa using all (index j))
    rw [FirstOrder.Language.Term.realize_relabel]
    exact (represents_equal_iff agree result).mp rfl
  · rintro ⟨t,word⟩
    refine ⟨length,t.relabel index,fun i hi v all => ?_⟩
    rw [FirstOrder.Language.Term.realize_relabel,word]
    exact correct i hi (v ∘ index) (fun j => all (index j))

/-- Flatten track, bit position, and side after the retained selector. -/
def position (width track bit : ℕ) (side : Bool) : ℕ := 1 + 2*(track*width+bit) + side.toNat

private theorem pair_inj (width : ℕ) {a b i j : ℕ} (hi : i < width) (hj : j < width)
    (eq : a*width+i = b*width+j) : a = b ∧ i = j := by
  have less (s t u v : ℕ) (hu : u < width) (st : s < t) : s*width+u < t*width+v := by
    have h := Nat.mul_le_mul_right width (show s+1 ≤ t from st)
    rw [Nat.add_mul,Nat.one_mul] at h
    omega
  have ab : a = b := by
    rcases lt_trichotomy a b with h|h|h
    · exact False.elim ((Nat.ne_of_lt (less a b i j hi h)) eq)
    · exact h
    · exact False.elim ((Nat.ne_of_lt (less b a j i hj h)) eq.symm)
  exact ⟨ab,by subst b; omega⟩

def coordinate {Track : Type*} {q : ℕ} (track : Track ≃ Fin q) (width : ℕ)
    (v : Option (Rail Track (Fin width))) : Fin (1+2*q*width) :=
  match v with
  | none => ⟨0,by omega⟩
  | some (g,i,b) => ⟨position width (track g).val i.val b,by
      have h := Nat.mul_le_mul_right width (show (track g).val+1 ≤ q from (track g).isLt)
      rw [Nat.add_mul,Nat.one_mul] at h
      have hb : b.toNat ≤ 1 := by cases b <;> decide
      have hi := i.isLt
      simp only [position,Nat.mul_assoc]
      omega⟩

theorem coordinate_injective {Track : Type*} {q : ℕ} (track : Track ≃ Fin q) (width : ℕ) :
    Function.Injective (coordinate track width) := by
  intro u v eq
  have value := congrArg Fin.val eq
  cases u with
  | none =>
    cases v with
    | none => rfl
    | some v => obtain ⟨g,i,b⟩ := v; simp [coordinate,position] at value; omega
  | some u =>
    obtain ⟨g,i,b⟩ := u
    cases v with
    | none => simp [coordinate,position] at value
    | some v =>
      obtain ⟨g',i',b'⟩ := v
      change 1+2*((track g).val*width+i.val)+b.toNat =
        1+2*((track g').val*width+i'.val)+b'.toNat at value
      have bb : b = b' := by cases b <;> cases b' <;> simp_all <;> omega
      subst b'
      have p := pair_inj width i.isLt i'.isLt (show
        (track g).val*width+i.val = (track g').val*width+i'.val by omega)
      have ge : g = g' := track.injective (Fin.ext p.1)
      have ie : i = i' := Fin.ext p.2
      cases ge; cases ie; rfl

noncomputable def coordEquiv {Track : Type*} [Fintype Track] {q : ℕ} (track : Track ≃ Fin q)
    (width : ℕ) : Option (Rail Track (Fin width)) ≃ Fin (1+2*q*width) :=
  Equiv.ofBijective (coordinate track width) ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨coordinate_injective track width,by
      have card : Fintype.card Track = q := (Fintype.card_congr track).trans (Fintype.card_fin q)
      simp [Rail,card]
      ring⟩)

@[simp] theorem coordEquiv_none {Track : Type*} [Fintype Track] {q : ℕ} (track : Track ≃ Fin q)
    (width : ℕ) : (coordEquiv track width none).val = 0 := rfl

@[simp] theorem coordEquiv_some {Track : Type*} [Fintype Track] {q : ℕ} (track : Track ≃ Fin q)
    (width : ℕ) (g : Track) (i : Fin width) (b : Bool) :
    (coordEquiv track width (some (g,i,b))).val = position width (track g).val i.val b := rfl

end KFOL.Complexity.AddressedPoint
