module

public import KFOL.Complexity.ReachMachine
public import KFOL.Definitions.Owner

/-! # Uniform native runtime for owner tables on explicit finite positions -/

@[expose] public section

namespace KFOL.Complexity.OwnerRuntime

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.Algorithms

abbrev RawGuard := List Bool × List Bool
abbrev RawEntry := ℕ × RawGuard
abbrev RawTable := ℕ × List RawEntry
abbrev Input := (n : ℕ) × Owner.GuardTable (Fin n)
abbrev guardEncoding := encPair encBits encBits
abbrev entryEncoding := encPair encNat guardEncoding
abbrev tableEncoding := encPair encNat (encList entryEncoding)
abbrev rawEncoding := encPair encUnary tableEncoding

def entryView {n : ℕ} (p : Fin n × Owner.GuardPair (Fin n)) : RawEntry :=
  (p.1.val, Bitset.encode p.2.many, Bitset.encode p.2.outside)

def tableView {n : ℕ} (T : Owner.GuardTable (Fin n)) : RawTable :=
  (T.root.val, T.entries.map entryView)

def view (input : Input) : ℕ × RawTable := (input.1, tableView input.2)

theorem entryView_injective {n : ℕ} : Function.Injective (@entryView n) := by
  rintro ⟨i, ⟨A, B⟩⟩ ⟨j, ⟨C, D⟩⟩ he
  have hi := Fin.ext (congrArg Prod.fst he)
  have hA := Bitset.encode_injective (congrArg (fun p => p.2.1) he)
  have hB := Bitset.encode_injective (congrArg (fun p => p.2.2) he)
  cases hi
  cases hA
  cases hB
  rfl

private theorem tableView_injective {n : ℕ} : Function.Injective (@tableView n) := by
  rintro ⟨r, entries⟩ ⟨s, other⟩ he
  have hr := Fin.ext (congrArg Prod.fst he)
  have hl : entries = other :=
    (List.map_inj_right (fun _ _ h => entryView_injective h)).mp (congrArg Prod.snd he)
  cases hr
  cases hl
  rfl

/-- The input includes its unary dimension. Roots and record outputs stay
binary; every prerequisite is the full explicit membership word. -/
def inputEncoding : Input ↪ List Bool :=
  ⟨fun input => rawEncoding (view input), by
    rintro ⟨n, T⟩ ⟨m, U⟩ he
    have hd := rawEncoding.injective he
    have hn : n = m := congrArg Prod.fst hd
    cases hn
    have hT := tableView_injective (congrArg Prod.snd hd)
    cases hT
    rfl⟩

@[fun_prop] theorem view_polyTime : ComputableInPolyTime view inputEncoding rawEncoding :=
  .of_eq (fun _ => rfl)

def union (p : List Bool × List Bool) : List Bool := p.1.zipWith (· || ·) p.2
def difference (p : List Bool × List Bool) : List Bool := p.1.zipWith (fun a b => a && !b) p.2

theorem union_polyTime : ComputableInPolyTime union (encPair encBits encBits) encBits :=
  bitsZipWith (· || ·)

private theorem difference_polyTime : ComputableInPolyTime difference (encPair encBits encBits) encBits :=
  bitsZipWith (fun a b => a && !b)

theorem union_encode {n : ℕ} (A B : Finset (Fin n)) :
    union (Bitset.encode A, Bitset.encode B) = Bitset.encode (A ∪ B) := by
  apply List.ext_getElem (by simp [union, Bitset.encode])
  intro i hi hi'
  simp [union, Bitset.encode]

private theorem difference_encode {n : ℕ} (A B : Finset (Fin n)) :
    difference (Bitset.encode A, Bitset.encode B) = Bitset.encode (A \ B) := by
  apply List.ext_getElem (by simp [difference, Bitset.encode])
  intro i hi hi'
  simp [difference, Bitset.encode]

def single (p : ℕ × ℕ) : List Bool := (List.range p.1).map (fun i => decide (i = p.2))

theorem single_polyTime : ComputableInPolyTime single (encPair encUnary encNat) encBits := by
  let input := encPair encUnary encNat
  have hindices := ComputableInPolyTime.range.comp (fst encUnary encNat)
  have hi := unary_to_binary.comp (snd input encUnary)
  have hj : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => p.1.2) (encPair input encUnary) encNat := by fun_prop
  exact mapToBitsWithInput (f := fun (p : ℕ × ℕ) i => decide (i = p.2)) hindices (decide_eq' hi hj)

theorem single_encode {n : ℕ} (j : Fin n) :
    single (n, j.val) = Bitset.encode {j} := by
  apply List.ext_getElem (by simp [single, Bitset.encode])
  intro i hi hi'
  simp [single, Bitset.encode, Fin.ext_iff]

def member (p : List Bool × ℕ) : Bool :=
  p.1.getD (min p.1.length p.2) false

theorem member_polyTime : ComputableInPolyTime member (encPair encBits encNat) encBool := by
  have hw := fst encBits encNat
  have hi := binary_min_unary' (length_bits.comp hw) (snd encBits encNat)
  exact bitsGetDWithInput hw hi false

theorem member_encode {n : ℕ} (A : Finset (Fin n)) (j : Fin n) :
    member (Bitset.encode A, j.val) = decide (j ∈ A) := by
  simp only [member, Bitset.length_encode, Nat.min_eq_right (Nat.le_of_lt j.isLt),
    List.getD_eq_getElem?_getD]
  exact Bitset.read_encode A j


def permitted (table : RawTable) (j : ℕ) (state : RawGuard) : Bool :=
  let available := union (state.1, union (state.2, single (state.1.length, j)))
  table.2.any (fun p => decide (p.1 = j) && ReachMachine.subset p.2.1 state.1 &&
    ReachMachine.subset p.2.2 available)

abbrev PermitInput := RawTable × (ℕ × RawGuard)
abbrev permitEncoding := encPair tableEncoding (encPair encNat guardEncoding)

theorem permitted_polyTime : ComputableInPolyTime
    (fun p : PermitInput => permitted p.1 p.2.1 p.2.2) permitEncoding encBool := by
  have hc : ComputableInPolyTime (fun p : PermitInput => p.2.2.1) permitEncoding encBits := by fun_prop
  have hd : ComputableInPolyTime (fun p : PermitInput => p.2.2.2) permitEncoding encBits := by fun_prop
  have hj : ComputableInPolyTime (fun p : PermitInput => p.2.1) permitEncoding encNat := by fun_prop
  have hsingle := single_polyTime.comp ((length_bits.comp hc).prod hj)
  have havailable := union_polyTime.comp (hc.prod (union_polyTime.comp (hd.prod hsingle)))
  have hrecords : ComputableInPolyTime (fun p : PermitInput => p.1.2) permitEncoding (encList entryEncoding) := by fun_prop
  have hi : ComputableInPolyTime (fun p : PermitInput × RawEntry => p.2.1)
      (encPair permitEncoding entryEncoding) encNat := by fun_prop
  have hm : ComputableInPolyTime (fun p : PermitInput × RawEntry => p.2.2.1)
      (encPair permitEncoding entryEncoding) encBits := by fun_prop
  have ho : ComputableInPolyTime (fun p : PermitInput × RawEntry => p.2.2.2)
      (encPair permitEncoding entryEncoding) encBits := by fun_prop
  have hcontext := fst permitEncoding entryEncoding
  have htest := bool_and' (bool_and' (decide_eq' hi (hj.comp hcontext))
    (ReachMachine.subset_polyTime.comp (hm.prod (hc.comp hcontext))))
    (ReachMachine.subset_polyTime.comp (ho.prod (havailable.comp hcontext)))
  exact anyWithInput (test := fun (p : PermitInput) (entry : RawEntry) =>
    decide (entry.1 = p.2.1) && ReachMachine.subset entry.2.1 p.2.2.1 &&
      ReachMachine.subset entry.2.2 (union (p.2.2.1, union (p.2.2.2, single (p.2.2.1.length, p.2.1)))))
    hrecords htest

theorem mem_guards {n : ℕ} (T : Owner.GuardTable (Fin n)) (j : Fin n)
    (g : Owner.GuardPair (Fin n)) : g ∈ T.guards j ↔ (j, g) ∈ T.entries := by
  simp only [Owner.GuardTable.guards, List.mem_toFinset, List.mem_map, List.mem_filter,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨k, h⟩, ⟨hp, rfl⟩, rfl⟩
    exact hp
  · intro hp
    exact ⟨(j, g), ⟨hp, rfl⟩, rfl⟩

theorem permitted_view {n : ℕ} (T : Owner.GuardTable (Fin n)) (j : Fin n)
    (C D : Finset (Fin n)) :
    permitted (tableView T) j.val (Bitset.encode C, Bitset.encode D) = decide (T.Permitted j C D) := by
  simp only [permitted, Bitset.length_encode, single_encode, union_encode]
  apply Bool.eq_iff_iff.mpr
  simp only [tableView, List.any_map, List.any_eq_true, Function.comp_def, entryView,
    Bool.and_eq_true, decide_eq_true_eq, ReachMachine.subset_encode, Fin.val_inj,
    Owner.GuardTable.Permitted, mem_guards]
  constructor
  · rintro ⟨p, hp, ⟨hj, hc⟩, hd⟩
    refine ⟨p.2, ?_, hc, ?_⟩
    · simpa only [← hj, Prod.eta] using hp
    · simpa only [Finset.union_assoc] using hd
  · rintro ⟨g, hg, hc, hd⟩
    exact ⟨(j, g), hg, ⟨rfl, hc⟩, by simpa only [Finset.union_assoc] using hd⟩


def stateView {n : ℕ} (S : Owner.SaturationState (Fin n)) : RawGuard :=
  (Bitset.encode S.many, Bitset.encode S.outside)

private theorem stateView_injective {n : ℕ} : Function.Injective (@stateView n) := by
  rintro ⟨A, B⟩ ⟨C, D⟩ he
  have hA := Bitset.encode_injective (congrArg Prod.fst he)
  have hB := Bitset.encode_injective (congrArg Prod.snd he)
  cases hA
  cases hB
  rfl

def update (state : RawGuard) (w z : ℕ) : RawGuard :=
  let many := union (state.1, single (state.1.length, w))
  let added := union (single (state.1.length, w), single (state.1.length, z))
  (many, difference (union (state.2, added), many))

theorem update_polyTime : ComputableInPolyTime
    (fun p : RawGuard × (ℕ × ℕ) => update p.1 p.2.1 p.2.2)
    (encPair guardEncoding (encPair encNat encNat)) guardEncoding := by
  let input := encPair guardEncoding (encPair encNat encNat)
  have hm : ComputableInPolyTime (fun p : RawGuard × (ℕ × ℕ) => p.1.1) input encBits := by fun_prop
  have ho : ComputableInPolyTime (fun p : RawGuard × (ℕ × ℕ) => p.1.2) input encBits := by fun_prop
  have hw : ComputableInPolyTime (fun p : RawGuard × (ℕ × ℕ) => p.2.1) input encNat := by fun_prop
  have hz : ComputableInPolyTime (fun p : RawGuard × (ℕ × ℕ) => p.2.2) input encNat := by fun_prop
  have hwidth := length_bits.comp hm
  have hsw := single_polyTime.comp (hwidth.prod hw)
  have hsz := single_polyTime.comp (hwidth.prod hz)
  have hmany := union_polyTime.comp (hm.prod hsw)
  have hadded := union_polyTime.comp (hsw.prod hsz)
  have houtside := difference_polyTime.comp ((union_polyTime.comp (ho.prod hadded)).prod hmany)
  exact hmany.prod houtside

theorem update_view {n : ℕ} (S : Owner.SaturationState (Fin n)) (w z : Fin n) :
    update (stateView S) w.val z.val = stateView (S.update w z) := by
  simp only [update, stateView, Bitset.length_encode, single_encode, union_encode, difference_encode,
    Owner.SaturationState.update]
  congr 1
  · congr 1
    ext i
    simp
  · congr 1
    ext i
    simp

abbrev Context := RawTable × RawEntry
abbrev contextEncoding := encPair tableEncoding entryEncoding
abbrev AllowedInput := Context × (RawGuard × (ℕ × ℕ))
abbrev allowedEncoding := encPair contextEncoding (encPair guardEncoding (encPair encNat encNat))

def allowed (context : Context) (state : RawGuard) (w z : ℕ) : Bool :=
  let target := union (context.2.2.1, union (context.2.2.2, single (context.2.2.1.length, context.2.1)))
  let outside := union (state.2, union (single (state.1.length, w), single (state.1.length, z)))
  member (context.2.2.1, w) && member (target, z) &&
    permitted context.1 w (state.1, outside) && permitted context.1 z (state.1, outside) &&
    decide (update state w z ≠ state)

theorem allowed_polyTime : ComputableInPolyTime
    (fun p : AllowedInput => allowed p.1 p.2.1 p.2.2.1 p.2.2.2) allowedEncoding encBool := by
  have hm : ComputableInPolyTime (fun p : AllowedInput => p.2.1.1) allowedEncoding encBits := by fun_prop
  have ho : ComputableInPolyTime (fun p : AllowedInput => p.2.1.2) allowedEncoding encBits := by fun_prop
  have hstate := (fst guardEncoding (encPair encNat encNat)).comp (snd contextEncoding _)
  have hw : ComputableInPolyTime (fun p : AllowedInput => p.2.2.1) allowedEncoding encNat := by fun_prop
  have hz : ComputableInPolyTime (fun p : AllowedInput => p.2.2.2) allowedEncoding encNat := by fun_prop
  have hgm : ComputableInPolyTime (fun p : AllowedInput => p.1.2.2.1) allowedEncoding encBits := by fun_prop
  have hgo : ComputableInPolyTime (fun p : AllowedInput => p.1.2.2.2) allowedEncoding encBits := by fun_prop
  have hj : ComputableInPolyTime (fun p : AllowedInput => p.1.2.1) allowedEncoding encNat := by fun_prop
  have ht : ComputableInPolyTime (fun p : AllowedInput => p.1.1) allowedEncoding tableEncoding := by fun_prop
  have hsw := single_polyTime.comp ((length_bits.comp hm).prod hw)
  have hsz := single_polyTime.comp ((length_bits.comp hm).prod hz)
  have hsj := single_polyTime.comp ((length_bits.comp hgm).prod hj)
  have htarget := union_polyTime.comp (hgm.prod (union_polyTime.comp (hgo.prod hsj)))
  have houtside := union_polyTime.comp (ho.prod (union_polyTime.comp (hsw.prod hsz)))
  have hpermittedW := permitted_polyTime.comp (ht.prod (hw.prod (hm.prod houtside)))
  have hpermittedZ := permitted_polyTime.comp (ht.prod (hz.prod (hm.prod houtside)))
  have hupdate := update_polyTime.comp (hstate.prod (hw.prod hz))
  have hne := bool_not.comp (decide_eq' hupdate hstate)
  exact bool_and' (bool_and' (bool_and' (bool_and'
    (member_polyTime.comp (hgm.prod hw)) (member_polyTime.comp (htarget.prod hz)))
    hpermittedW) hpermittedZ) hne

theorem allowed_view {n : ℕ} (T : Owner.GuardTable (Fin n)) (j : Fin n)
    (g : Owner.GuardPair (Fin n)) (S : Owner.SaturationState (Fin n)) (w z : Fin n) :
    allowed (tableView T, entryView (j, g)) (stateView S) w.val z.val =
      decide (T.UpdateAllowed j g S w z) := by
  simp only [allowed, update_view, stateView_injective.ne_iff]
  simp only [entryView, stateView, Bitset.length_encode, single_encode, union_encode, member_encode, permitted_view]
  simp only [Owner.GuardTable.UpdateAllowed, Owner.GuardTable.target, Finset.union_assoc,
    Finset.singleton_union]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, he⟩
    exact ⟨ha, hb, of_decide_eq_true hc, of_decide_eq_true hd, he⟩
  · rintro ⟨ha, hb, hc, hd, he⟩
    exact ⟨⟨⟨⟨ha, hb⟩, decide_eq_true hc⟩, decide_eq_true hd⟩, he⟩


theorem indices_polyTime : ComputableInPolyTime List.range encUnary (encList encNat) := by
  have h := mapWithInput (f := fun (_ : ℕ) (i : ℕ) => i) ComputableInPolyTime.range
    (unary_to_binary.comp (snd encUnary encUnary))
  convert h using 1
  funext width
  exact (congrFun List.map_id_fun (List.range width)).symm

def candidates (width : ℕ) : List (ℕ × ℕ) := (List.range width).product (List.range width)

private theorem candidates_polyTime : ComputableInPolyTime candidates encUnary
    (encList (encPair encNat encNat)) := by
  have hwidth := fst encUnary encNat
  have hfirst : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => p.1.2)
      (encPair (encPair encUnary encNat) encNat) encNat := by fun_prop
  have hsecond := snd (encPair encUnary encNat) encNat
  have hrow := mapWithInput (f := fun (p : ℕ × ℕ) (j : ℕ) => (p.2, j))
    (indices_polyTime.comp hwidth) (hfirst.prod hsecond)
  have h := flatMapWithInput (f := fun (width : ℕ) (i : ℕ) => (List.range width).map (i, ·))
    indices_polyTime hrow
  exact h

def next (context : Context) (state : RawGuard) : Option (ℕ × ℕ) :=
  (candidates context.2.2.1.length).find? (fun p => allowed context state p.1 p.2)

theorem next_polyTime : ComputableInPolyTime
    (fun p : Context × RawGuard => next p.1 p.2) (encPair contextEncoding guardEncoding)
    (encOption (encPair encNat encNat)) := by
  let input := encPair contextEncoding guardEncoding
  have hwidth : ComputableInPolyTime (fun p : Context × RawGuard => p.1.2.2.1) input encBits := by fun_prop
  have hlist := candidates_polyTime.comp (length_bits.comp hwidth)
  have hc : ComputableInPolyTime (fun p : (Context × RawGuard) × (ℕ × ℕ) => p.1.1)
      (encPair input (encPair encNat encNat)) contextEncoding := by fun_prop
  have hs : ComputableInPolyTime (fun p : (Context × RawGuard) × (ℕ × ℕ) => p.1.2)
      (encPair input (encPair encNat encNat)) guardEncoding := by fun_prop
  have hp := snd input (encPair encNat encNat)
  have htest := allowed_polyTime.comp (hc.prod (hs.prod hp))
  exact findWithInput (test := fun (p : Context × RawGuard) (pair : ℕ × ℕ) =>
    allowed p.1 p.2 pair.1 pair.2) hlist htest


private theorem product_map {A B C D : Type} (f : A → C) (g : B → D) (xs : List A) (ys : List B) :
    (xs.product ys).map (fun p => (f p.1, g p.2)) = (xs.map f).product (ys.map g) := by
  simp only [List.product, List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def]

theorem finRange_values (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp

/-- The native next-update scan is exactly the existing deterministic owner
scan, in the same complete finite position order. -/
theorem next_view {n : ℕ} (T : Owner.GuardTable (Fin n)) (j : Fin n)
    (g : Owner.GuardPair (Fin n)) (S : Owner.SaturationState (Fin n)) :
    next (tableView T, entryView (j, g)) (stateView S) =
      (T.next (List.finRange n) j g S).map (fun p => (p.1.val, p.2.val)) := by
  have hc : candidates n =
      ((List.finRange n).product (List.finRange n)).map (fun p => (p.1.val, p.2.val)) := by
    rw [product_map, finRange_values]
    rfl
  simp only [next, entryView, Bitset.length_encode, hc, List.find?_map]
  unfold Owner.GuardTable.next
  congr 2
  funext p
  exact allowed_view T j g S p.1 p.2

end KFOL.Complexity.OwnerRuntime
