module

public import KFOL.Reductions.RowLists
public import KFOL.Core.QuantifiedRecognition

/-! # Listing the normal form of the operation of a formula

The vertices and labels of a prenex formula are coded by triples of numbers,
and the incidences of the rows are computed on these triples. The resulting
list program writes the prime guards of the operation of the formula. Some
core term has the listed prime guards exactly when the formula is true.
-/

@[expose] public section

namespace KFOL.Recognition.Lists

open Bichain Bichain.Quantified Core.Sources Problems

/-! ### Triples -/

/-- A kind, an index and a bit. -/
abbrev Tup := ℕ × ℕ × ℕ

/-- The triple of a vertex. -/
def tupV : Vtx → Tup
  | .br i s => (0, i, s.toNat)
  | .relay i => (1, i, 0)
  | .res i s => (2, i, s.toNat)
  | .cl c => (3, c, 0)

/-- The triple of a label. -/
def tupL : Lab → Tup
  | .ch i s => (0, i, s.toNat)
  | .rl i => (1, i, 0)
  | .perm i s => (2, i, s.toNat)
  | .lit i s => (3, i, s.toNat)
  | .kap c => (4, c, 0)

theorem toNat_eq_iff (s t : Bool) : s.toNat = t.toNat ↔ s = t := by
  cases s <;> cases t <;> simp

theorem tupV_injective : Function.Injective tupV := by
  intro a b h
  cases a <;> cases b <;> simp_all [tupV, toNat_eq_iff]

theorem tupL_injective : Function.Injective tupL := by
  intro a b h
  cases a <;> cases b <;> simp_all [tupL, toNat_eq_iff]

/-- The name of a selector (`side = 0`) or of a row input (`side = 1`). -/
def nm (side : ℕ) (t : Tup) : ℕ := Nat.pair side (Nat.pair t.1 (Nat.pair t.2.1 t.2.2))

theorem nm_inj {s s' : ℕ} {t t' : Tup} : nm s t = nm s' t' ↔ s = s' ∧ t = t' := by
  simp only [nm, Nat.pair_eq_pair, Prod.ext_iff]

/-- The padding input. -/
def pad : Tup := (5, 0, 0)

/-! ### The list program -/

/-- Triples of vertices with index below a bound. -/
def candV (N : ℕ) : List Tup :=
  (List.range N).flatMap fun i =>
    [(0, i, 1), (0, i, 0), (1, i, 0), (2, i, 1), (2, i, 0), (3, i, 0)]

/-- The rows among the triples of vertices. -/
def isRowB (n m : ℕ) (t : Tup) : Bool :=
  (t.1 == 0 && ((decide (1 ≤ t.2.1) && decide (t.2.1 ≤ n)) ||
    (decide (n < t.2.1) && decide (t.2.1 < n + m) && t.2.2 == 1))) ||
  (t.1 == 1 && decide (1 ≤ t.2.1) && (decide (t.2.1 ≤ n) || decide (t.2.1 < n + m))) ||
  (t.1 == 2 && decide (1 ≤ t.2.1) && decide (t.2.1 ≤ n)) ||
  (t.1 == 3 && decide (t.2.1 < m))

/-- The triples of the rows. -/
def rowsT (n m : ℕ) : List Tup := (candV (n + m + 1)).filter (isRowB n m)

/-- Triples of labels with index below a bound. -/
def candL (N : ℕ) : List Tup :=
  (List.range N).flatMap fun i =>
    [(0, i, 1), (0, i, 0), (1, i, 0), (2, i, 1), (2, i, 0), (3, i, 1), (3, i, 0), (4, i, 0)]

/-- The coordinates among the triples of labels. -/
def isLabB (n m : ℕ) (t : Tup) : Bool :=
  (t.1 == 0 && decide (1 ≤ t.2.1) && decide (t.2.1 ≤ n)) ||
  (t.1 == 1 && decide (1 ≤ t.2.1) && (decide (t.2.1 ≤ n) || decide (t.2.1 < n + m))) ||
  (t.1 == 2 && decide (1 ≤ t.2.1) && decide (t.2.1 ≤ n)) ||
  (t.1 == 3 && decide (1 ≤ t.2.1) && decide (t.2.1 ≤ n)) ||
  (t.1 == 4 && (decide (t.2.1 < m) || t.2.1 == 0))

/-- The triples of the coordinates. -/
def labsT (n m : ℕ) : List Tup := (candL (n + m + 1)).filter (isLabB n m)

/-- Odd stages up to `2 n + 1` are existential. -/
def exB (n i : ℕ) : Bool := (List.range (n + 1)).any fun r => 2 * r + 1 == i

/-- The triple of the label marked by a row. -/
def markT (n : ℕ) (t : Tup) : Tup :=
  if t.1 == 0 then
    (if t.2.1 ≤ n then (0, t.2.1, if exB n t.2.1 then t.2.2 else 1) else (4, t.2.1 - n - 1, 0))
  else if t.1 == 1 then (1, t.2.1, 0)
  else if t.1 == 2 then (3, t.2.1, t.2.2)
  else (4, t.2.1, 0)

/-- Equality of triples. -/
def tupEq (s t : Tup) : Bool := s.1 == t.1 && s.2.1 == t.2.1 && s.2.2 == t.2.2

/-- A label lies on the rectangle of a left vertex. -/
def inIB (n : ℕ) (cls : List (List (ℕ × ℕ))) (z e : Tup) : Bool :=
  (z.1 == 0 && e.1 == 0 && e.2.1 == z.2.1 + 1) ||
  (z.1 == 0 && e.1 == 1 && e.2.1 == z.2.1) ||
  (z.1 == 0 && e.1 == 2 && e.2.1 == z.2.1 && e.2.2 == z.2.2) ||
  (z.1 == 0 && e.1 == 4 && z.2.1 == n + e.2.1) ||
  (z.1 == 3 && e.1 == 3 && (cls.getD z.2.1 []).any fun l => l.1 == e.2.1 && l.2 == e.2.2)

/-- A label lies on the rectangle of a right vertex. -/
def inJB (n : ℕ) (z e : Tup) : Bool :=
  (z.1 == 1 && e.1 == 0 && e.2.1 == z.2.1 + 1 && decide (e.2.1 ≤ n) &&
    (e.2.2 == 1 || exB n e.2.1)) ||
  (z.1 == 1 && e.1 == 1 && e.2.1 == z.2.1 + 1) ||
  (z.1 == 1 && e.1 == 3 && decide (n ≤ z.2.1)) ||
  (z.1 == 1 && e.1 == 4 && z.2.1 == n + e.2.1) ||
  (z.1 == 2 && e.1 == 2 && e.2.1 == z.2.1 && e.2.2 == z.2.2)

/-- The names of the selectors: two rows without marks, then the rows. -/
def selN (n m : ℕ) : List ℕ := [nm 0 (4, 0, 0), nm 0 (4, 0, 1)] ++ (rowsT n m).map (nm 0)

/-- The names of the row inputs: the padding input, then the coordinates. -/
def coN (n m : ℕ) : List ℕ := nm 1 pad :: (labsT n m).map (nm 1)

/-- The first endpoint. -/
def xN (n m : ℕ) (cls : List (List (ℕ × ℕ))) : List ℕ :=
  ((labsT n m).filter fun e => inIB n cls (0, 0, 0) e).map (nm 1)

/-- The complement of the second endpoint. -/
def yN (n m : ℕ) : List ℕ :=
  nm 1 pad :: ((labsT n m).filter fun e => inJB n (1, 0, 0) e).map (nm 1)

/-- The marks of the rows. -/
def mkN (n m : ℕ) : List (ℕ × ℕ) :=
  (rowsT n m).flatMap fun z =>
    ((labsT n m).filter fun e => tupEq (markT n z) e).map fun e => (nm 0 z, nm 1 e)

/-- The fixed inputs of the rows with their owners. -/
def fxN (c1 c2 n m : ℕ) (cls : List (List (ℕ × ℕ))) : List (ℕ × ℕ × ℕ) :=
  ((selN n m).map fun u => (u, nm 1 pad, c1)) ++
  (rowsT n m).flatMap fun z => (labsT n m).flatMap fun e =>
    if tupEq (markT n z) e then []
    else if inIB n cls z e then [(nm 0 z, nm 1 e, c2)]
    else if inJB n z e then [(nm 0 z, nm 1 e, c1)]
    else []

/-- The losses of every input of the operation of a formula. -/
def sourcesOf (c0 c1 c2 n : ℕ) (cls : List (List (ℕ × ℕ))) :
    List (ℕ × List (List (ℕ × ℕ))) :=
  sourcesN c0 c1 c2 (selN n cls.length) (coN n cls.length) (xN n cls.length cls)
    (yN n cls.length) (mkN n cls.length) (fxN c1 c2 n cls.length cls)

/-- The names of the inputs and the prime guards of the operation of a formula. -/
def instanceOf (K c0 c1 c2 n : ℕ) (cls : List (List (ℕ × ℕ))) : GuardList :=
  ((sourcesOf c0 c1 c2 n cls).map fun s => s.1, entriesOf K (sourcesOf c0 c1 c2 n cls))

/-! ### The program computes the incidences of the formula -/

section Mirror

variable (F : Formula)

/-- The clauses with signs as numbers. -/
def numCls : List (List (ℕ × ℕ)) := F.cls.map fun C => C.map fun l => (l.1, l.2.toNat)

theorem exB_iff (n i : ℕ) (hi : i ≤ n) : exB n i = decide (i % 2 = 1) := by
  rw [Bool.eq_iff_iff]
  simp only [exB, List.any_eq_true, List.mem_range, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨r, -, rfl⟩
    omega
  · intro h
    exact ⟨i / 2, by omega, by omega⟩

theorem isRowB_tupV (z : Vtx) : isRowB F.n F.cls.length (tupV z) = true ↔ IsRow F z := by
  cases z with
  | br i s => cases s <;> simp only [tupV] <;> simp [isRowB, IsRow]
  | relay i => simp only [tupV]; simp [isRowB, IsRow]
  | res i s => simp only [tupV]; simp [isRowB, IsRow]
  | cl c => simp only [tupV]; simp [isRowB, IsRow]

theorem isLabB_tupL (e : Lab) : isLabB F.n F.cls.length (tupL e) = true ↔ IsLab F e := by
  cases e <;> simp only [tupL] <;> simp [isLabB, IsLab]

theorem mem_candV (N : ℕ) (t : Tup) : t ∈ candV N ↔ ∃ z ∈ vertices N, tupV z = t := by
  constructor
  · intro h
    obtain ⟨i, hi, ht⟩ := List.mem_flatMap.1 h
    have hi' := List.mem_range.1 hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨.br i true, by simp [vertices, hi'], rfl⟩
    · exact ⟨.br i false, by simp [vertices, hi'], rfl⟩
    · exact ⟨.relay i, by simp [vertices, hi'], rfl⟩
    · exact ⟨.res i true, by simp [vertices, hi'], rfl⟩
    · exact ⟨.res i false, by simp [vertices, hi'], rfl⟩
    · exact ⟨.cl i, by simp [vertices, hi'], rfl⟩
  · rintro ⟨z, hz, rfl⟩
    simp only [vertices, Finset.mem_union, Finset.mem_image, Finset.mem_range] at hz
    rcases hz with ((((⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩) |
      ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩ <;>
      exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by simp [tupV]⟩

theorem mem_candL (N : ℕ) (t : Tup) : t ∈ candL N ↔ ∃ e ∈ coordinates N, tupL e = t := by
  constructor
  · intro h
    obtain ⟨i, hi, ht⟩ := List.mem_flatMap.1 h
    have hi' := List.mem_range.1 hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨.ch i true, by simp [coordinates, hi'], rfl⟩
    · exact ⟨.ch i false, by simp [coordinates, hi'], rfl⟩
    · exact ⟨.rl i, by simp [coordinates, hi'], rfl⟩
    · exact ⟨.perm i true, by simp [coordinates, hi'], rfl⟩
    · exact ⟨.perm i false, by simp [coordinates, hi'], rfl⟩
    · exact ⟨.lit i true, by simp [coordinates, hi'], rfl⟩
    · exact ⟨.lit i false, by simp [coordinates, hi'], rfl⟩
    · exact ⟨.kap i, by simp [coordinates, hi'], rfl⟩
  · rintro ⟨e, he, rfl⟩
    simp only [coordinates, Finset.mem_union, Finset.mem_image, Finset.mem_range] at he
    rcases he with ((((((⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩) |
      ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩ <;>
      exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by simp [tupL]⟩

theorem mem_rowsT (t : Tup) : t ∈ rowsT F.n F.cls.length ↔ ∃ z ∈ allRows F, tupV z = t := by
  simp only [rowsT, List.mem_filter, mem_candV, allRows, Finset.mem_filter]
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, hrow⟩
    exact ⟨z, ⟨hz, (isRowB_tupV F z).1 hrow⟩, rfl⟩
  · rintro ⟨z, ⟨hz, hrow⟩, rfl⟩
    exact ⟨⟨z, hz, rfl⟩, (isRowB_tupV F z).2 hrow⟩

theorem mem_labsT (t : Tup) : t ∈ labsT F.n F.cls.length ↔ ∃ e ∈ labels F, tupL e = t := by
  simp only [labsT, List.mem_filter, mem_candL, labels, Finset.mem_filter]
  constructor
  · rintro ⟨⟨e, he, rfl⟩, hlab⟩
    exact ⟨e, ⟨he, (isLabB_tupL F e).1 hlab⟩, rfl⟩
  · rintro ⟨e, ⟨he, hlab⟩, rfl⟩
    exact ⟨⟨e, he, rfl⟩, (isLabB_tupL F e).2 hlab⟩

theorem tupEq_iff (s t : Tup) : tupEq s t = true ↔ s = t := by
  simp only [tupEq, Bool.and_eq_true, beq_iff_eq, Prod.ext_iff, and_assoc]

variable (hex : ∀ i, i ≤ F.n → F.ex i = exB F.n i)
include hex

theorem markT_tupV (z : Vtx) : markT F.n (tupV z) = tupL (mark F z) := by
  cases z with
  | br i s =>
    by_cases hi : i ≤ F.n
    · rw [show mark F (.br i s) = .ch i (if F.ex i then s else true) by simp [mark, hi]]
      simp only [tupV, tupL]
      simp only [markT, beq_self_eq_true, ↓reduceIte, hi, ← hex i hi]
      cases F.ex i <;> simp
    · simp only [tupV]
      simp [markT, tupL, mark, hi]
  | relay i => simp only [tupV]; simp [markT, tupL, mark]
  | res i s => simp only [tupV]; simp [markT, tupL, mark]
  | cl c => simp only [tupV]; simp [markT, tupL, mark]

theorem inJB_tup (z : Vtx) (e : Lab) : inJB F.n (tupV z) (tupL e) = inJ F z e := by
  rw [Bool.eq_iff_iff]
  cases z with
  | br i s => cases e <;> simp only [tupV, tupL] <;> simp [inJB, inJ]
  | relay k =>
    cases e with
    | ch j t =>
      simp only [tupV, tupL]
      by_cases hj : j ≤ F.n
      · simp only [inJB, inJ, ← hex j hj]
        cases t <;> simp [hj]
      · simp [inJB, inJ, hj]
    | rl j => simp only [tupV, tupL]; simp [inJB, inJ]
    | perm j t => simp only [tupV, tupL]; simp [inJB, inJ]
    | lit j t => simp only [tupV, tupL]; simp [inJB, inJ]
    | kap c => simp only [tupV, tupL]; simp [inJB, inJ]
  | res i s => cases e <;> simp only [tupV, tupL] <;> simp [inJB, inJ, toNat_eq_iff]
  | cl c => cases e <;> simp only [tupV, tupL] <;> simp [inJB, inJ]

omit hex in
theorem inIB_tup (z : Vtx) (e : Lab) : inIB F.n (numCls F) (tupV z) (tupL e) = inI F z e := by
  rw [Bool.eq_iff_iff]
  cases z with
  | br i s => cases e <;> simp only [tupV, tupL] <;> simp [inIB, inI, toNat_eq_iff]
  | relay k => cases e <;> simp only [tupV, tupL] <;> simp [inIB, inI]
  | res i s => cases e <;> simp only [tupV, tupL] <;> simp [inIB, inI]
  | cl c =>
    cases e with
    | lit j t =>
      have hget : (numCls F).getD c [] = (F.cls.getD c []).map fun l => (l.1, l.2.toNat) := by
        simp only [numCls, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases F.cls[c]? <;> rfl
      simp only [tupV, tupL]
      simp only [inIB, inI, hget, List.any_map]
      simp only [List.any_eq_true, Function.comp, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
        toNat_eq_iff, decide_eq_true_eq]
      constructor
      · rintro (h | ⟨-, ⟨l1, l2⟩, hl, rfl, rfl⟩)
        · simp at h
        · exact hl
      · intro h
        exact Or.inr ⟨⟨trivial, trivial⟩, (j, t), h, rfl, rfl⟩
    | ch j t => simp only [tupV, tupL]; simp [inIB, inI]
    | rl j => simp only [tupV, tupL]; simp [inIB, inI]
    | perm j t => simp only [tupV, tupL]; simp [inIB, inI]
    | kap c' => simp only [tupV, tupL]; simp [inIB, inI]

end Mirror

/-! ### The coded rows of a formula -/

section Code

variable {K : ℕ} (three : Fin 3 ↪ Fin K) (F : Formula)

/-- The names of the selectors. -/
def nameZ : RowIx F → ℕ
  | .inl b => nm 0 (4, 0, b.toNat)
  | .inr z => nm 0 (tupV z.val)

/-- The names of the row inputs. -/
def nameP : Option (FLab F) → ℕ
  | none => nm 1 pad
  | some e => nm 1 (tupL e.val)

theorem tupV_fst_lt (z : Vtx) : (tupV z).1 < 4 := by
  cases z <;> simp [tupV]

theorem tupL_fst_lt (e : Lab) : (tupL e).1 < 5 := by
  cases e <;> simp [tupL]

theorem name_injective : Function.Injective (Sum.elim (nameZ F) (nameP F)) := by
  rintro (z | x) (z' | x') h
  · have h' : nameZ F z = nameZ F z' := h
    cases z with
    | inl b =>
      cases z' with
      | inl b' =>
        have e : (4, 0, b.toNat) = ((4, 0, b'.toNat) : Tup) := (nm_inj.1 h').2
        have e' : b.toNat = b'.toNat := congrArg (fun t : Tup => t.2.2) e
        rw [(toNat_eq_iff b b').1 e']
      | inr z' =>
        have e : (4, 0, b.toNat) = tupV z'.val := (nm_inj.1 h').2
        have h4 := tupV_fst_lt z'.val
        rw [← e] at h4
        exact absurd h4 (lt_irrefl 4)
    | inr z =>
      cases z' with
      | inl b' =>
        have e : tupV z.val = (4, 0, b'.toNat) := (nm_inj.1 h').2
        have h4 := tupV_fst_lt z.val
        rw [e] at h4
        exact absurd h4 (lt_irrefl 4)
      | inr z' =>
        have e : tupV z.val = tupV z'.val := (nm_inj.1 h').2
        rw [Subtype.ext (tupV_injective e)]
  · have h' : nameZ F z = nameP F x' := h
    cases z <;> cases x' <;> exact absurd (nm_inj.1 h').1 (by decide)
  · have h' : nameP F x = nameZ F z' := h
    cases x <;> cases z' <;> exact absurd (nm_inj.1 h').1 (by decide)
  · have h' : nameP F x = nameP F x' := h
    cases x with
    | none =>
      cases x' with
      | none => rfl
      | some e' =>
        have e : pad = tupL e'.val := (nm_inj.1 h').2
        have h5 := tupL_fst_lt e'.val
        rw [← e] at h5
        exact absurd h5 (by decide)
    | some e₀ =>
      cases x' with
      | none =>
        have e : tupL e₀.val = pad := (nm_inj.1 h').2
        have h5 := tupL_fst_lt e₀.val
        rw [e] at h5
        exact absurd h5 (by decide)
      | some e' =>
        have e : tupL e₀.val = tupL e'.val := (nm_inj.1 h').2
        rw [Subtype.ext (tupL_injective e)]

theorem rows_eq_c_iff (z : Vtx) (e : FLab F) :
    rows F z e = .c ↔ mark F z ≠ e.val ∧ inI F z e.val = true := by
  unfold rows
  split_ifs <;> simp_all

theorem rows_eq_b_iff (z : Vtx) (e : FLab F) :
    rows F z e = .b ↔ mark F z ≠ e.val ∧ inI F z e.val = false ∧ inJ F z e.val = true := by
  unfold rows
  split_ifs <;> simp_all

theorem mem_selN (a : ℕ) : a ∈ selN F.n F.cls.length ↔ ∃ z, nameZ F z = a := by
  simp only [selN, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map]
  constructor
  · rintro ((rfl | rfl) | ⟨t, ht, rfl⟩)
    · exact ⟨.inl false, rfl⟩
    · exact ⟨.inl true, rfl⟩
    · obtain ⟨z, hz, rfl⟩ := (mem_rowsT F t).1 ht
      exact ⟨.inr ⟨z, hz⟩, rfl⟩
  · rintro ⟨z | z, rfl⟩
    · cases z
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr rfl)
    · exact Or.inr ⟨tupV z.val, (mem_rowsT F _).2 ⟨z.val, z.property, rfl⟩, rfl⟩

/-- The lists of the program code the rows of the formula. -/
theorem rowCode (hex : ∀ i, i ≤ F.n → F.ex i = exB F.n i) :
    RowCode three (paddedRows F) (fun e : FLab F => inI F (.br 0 false) e.val)
      (fun e : FLab F => !inJ F (.relay 0) e.val) (nameZ F) (nameP F)
      (selN F.n F.cls.length) (coN F.n F.cls.length) (xN F.n F.cls.length (numCls F))
      (yN F.n F.cls.length) (mkN F.n F.cls.length)
      (fxN (three 1).val (three 2).val F.n F.cls.length (numCls F)) where
  inj := name_injective F
  sel := mem_selN F
  co := by
    intro a
    simp only [coN, List.mem_cons, List.mem_map]
    constructor
    · rintro (rfl | ⟨t, ht, rfl⟩)
      · exact ⟨none, rfl⟩
      · obtain ⟨e, he, rfl⟩ := (mem_labsT F t).1 ht
        exact ⟨some ⟨e, he⟩, rfl⟩
    · rintro ⟨x | e, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨tupL e.val, (mem_labsT F _).2 ⟨e.val, e.property, rfl⟩, rfl⟩
  xs := by
    intro a
    simp only [xN, List.mem_map, List.mem_filter]
    constructor
    · rintro ⟨t, ⟨ht, hI⟩, rfl⟩
      obtain ⟨e, he, rfl⟩ := (mem_labsT F t).1 ht
      refine ⟨some ⟨e, he⟩, ?_, rfl⟩
      change inI F (.br 0 false) e = true
      rw [← inIB_tup]
      exact hI
    · rintro ⟨x | e, hx, rfl⟩
      · cases hx
      · refine ⟨tupL e.val, ⟨(mem_labsT F _).2 ⟨e.val, e.property, rfl⟩, ?_⟩, rfl⟩
        have h : inI F (.br 0 false) e.val = true := hx
        rw [← inIB_tup] at h
        exact h
  ys := by
    intro a
    simp only [yN, List.mem_cons, List.mem_map, List.mem_filter]
    constructor
    · rintro (rfl | ⟨t, ⟨ht, hJ⟩, rfl⟩)
      · exact ⟨none, rfl, rfl⟩
      · obtain ⟨e, he, rfl⟩ := (mem_labsT F t).1 ht
        refine ⟨some ⟨e, he⟩, ?_, rfl⟩
        have h : inJ F (.relay 0) e = true := by
          rw [← inJB_tup F hex]
          exact hJ
        change (!inJ F (.relay 0) e) = false
        rw [h]
        rfl
    · rintro ⟨x | e, hx, rfl⟩
      · exact Or.inl rfl
      · refine Or.inr ⟨tupL e.val, ⟨(mem_labsT F _).2 ⟨e.val, e.property, rfl⟩, ?_⟩, rfl⟩
        have h : (!inJ F (.relay 0) e.val) = false := hx
        have h' : inJ F (.relay 0) e.val = true := by simpa using h
        rw [← inJB_tup F hex] at h'
        exact h'
  mks := by
    intro a b
    simp only [mkN, List.mem_flatMap, List.mem_map, List.mem_filter, Prod.mk.injEq]
    constructor
    · rintro ⟨t, ht, e', ⟨he', hmark⟩, rfl, rfl⟩
      obtain ⟨z, hz, rfl⟩ := (mem_rowsT F t).1 ht
      obtain ⟨e, he, rfl⟩ := (mem_labsT F e').1 he'
      rw [tupEq_iff, markT_tupV F hex] at hmark
      exact ⟨.inr ⟨z, hz⟩, some ⟨e, he⟩,
        (rows_eq_possible_iff F z ⟨e, he⟩).2 (tupL_injective hmark), rfl, rfl⟩
    · rintro ⟨z | z, x | e, hrow, rfl, rfl⟩
      · cases hrow
      · cases hrow
      · cases hrow
      · have hm := (rows_eq_possible_iff F z.val e).1 hrow
        exact ⟨tupV z.val, (mem_rowsT F _).2 ⟨z.val, z.property, rfl⟩, tupL e.val,
          ⟨(mem_labsT F _).2 ⟨e.val, e.property, rfl⟩,
            by rw [tupEq_iff, markT_tupV F hex, hm]⟩, rfl, rfl⟩
  fx := by
    intro a b r
    simp only [fxN, List.mem_append, List.mem_map, List.mem_flatMap, Prod.mk.injEq]
    constructor
    · rintro (⟨u, hu, rfl, rfl, rfl⟩ | ⟨t, ht, e', he', hmem⟩)
      · obtain ⟨z, rfl⟩ := (mem_selN F u).1 hu
        exact ⟨z, none, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
      · obtain ⟨z, hz, rfl⟩ := (mem_rowsT F t).1 ht
        obtain ⟨e, he, rfl⟩ := (mem_labsT F e').1 he'
        rw [markT_tupV F hex, inIB_tup, inJB_tup F hex] at hmem
        have hne : tupEq (tupL (mark F z)) (tupL e) = true ↔ mark F z = e :=
          (tupEq_iff _ _).trans tupL_injective.eq_iff
        split_ifs at hmem with h1 h2 h3
        · cases hmem
        · obtain ⟨rfl, rfl, rfl⟩ : a = _ ∧ b = _ ∧ r = _ := by simpa using hmem
          exact ⟨.inr ⟨z, hz⟩, some ⟨e, he⟩, rfl, rfl, Or.inr
            ⟨(rows_eq_c_iff F z ⟨e, he⟩).2 ⟨fun hm => h1 (hne.2 hm), h2⟩, rfl⟩⟩
        · obtain ⟨rfl, rfl, rfl⟩ : a = _ ∧ b = _ ∧ r = _ := by simpa using hmem
          exact ⟨.inr ⟨z, hz⟩, some ⟨e, he⟩, rfl, rfl, Or.inl
            ⟨(rows_eq_b_iff F z ⟨e, he⟩).2 ⟨fun hm => h1 (hne.2 hm), by simpa using h2, h3⟩,
              rfl⟩⟩
        · cases hmem
    · rintro ⟨z, x, rfl, rfl, hrow⟩
      cases x with
      | none =>
        left
        rcases hrow with ⟨-, rfl⟩ | ⟨hrow, -⟩
        · exact ⟨nameZ F z, (mem_selN F _).2 ⟨z, rfl⟩, rfl, rfl, rfl⟩
        · cases hrow
      | some e =>
        cases z with
        | inl b0 => rcases hrow with ⟨hrow, -⟩ | ⟨hrow, -⟩ <;> cases hrow
        | inr z =>
          right
          refine ⟨tupV z.val, (mem_rowsT F _).2 ⟨z.val, z.property, rfl⟩, tupL e.val,
            (mem_labsT F _).2 ⟨e.val, e.property, rfl⟩, ?_⟩
          rw [markT_tupV F hex, inIB_tup, inJB_tup F hex]
          have hne : ∀ hm : mark F z.val ≠ e.val,
              tupEq (tupL (mark F z.val)) (tupL e.val) = false := fun hm => by
            rw [Bool.eq_false_iff]
            exact fun h => hm (tupL_injective ((tupEq_iff _ _).1 h))
          rcases hrow with ⟨hrow, rfl⟩ | ⟨hrow, rfl⟩
          · obtain ⟨hm, hI, hJ⟩ := (rows_eq_b_iff F z.val e).1 hrow
            simp [hne hm, hI, hJ, nameZ, nameP]
          · obtain ⟨hm, hI⟩ := (rows_eq_c_iff F z.val e).1 hrow
            simp [hne hm, hI, nameZ, nameP]
  two := by
    classical
    intro x
    cases x with
    | none => exact ⟨.inl true, .inl true, fun z h => by cases h⟩
    | some e =>
      obtain ⟨z1, z2, hz⟩ := mark_two F e.val
      let lift : Vtx → RowIx F := fun z => if h : z ∈ allRows F then .inr ⟨z, h⟩ else .inl true
      have hlift : ∀ z : {z : Vtx // z ∈ allRows F}, lift z.val = .inr z := fun z => by
        simp only [lift, z.property, ↓reduceDIte]
      refine ⟨lift z1, lift z2, fun z hrow => ?_⟩
      cases z with
      | inl b => cases hrow
      | inr z =>
        have hm := (rows_eq_possible_iff F z.val e).1 hrow
        rcases hz z.val z.property hm with h | h
        · left
          rw [← h, hlift]
        · right
          rw [← h, hlift]

theorem isCore_rename {Role Var Var' : Type*} (σ : Var → Var') :
    ∀ t : KFOL.Term Role Var, t.IsCore → (t.subst fun j => .var (σ j)).IsCore
  | .winner _, h => h
  | .var _, _ => trivial
  | .choice _ s t, h => ⟨isCore_rename σ s h.1, isCore_rename σ t h.2⟩
  | .rename _ _, h => h

/-- **The listed normal form.** Some core term has the listed prime guards
exactly when the formula is true. -/
theorem instanceOf_mem_iff (hwf : F.WF) (hex : ∀ i, i ≤ F.n → F.ex i = exB F.n i) :
    instanceOf K (three 0).val (three 1).val (three 2).val F.n (numCls F) ∈
        coreNormalForms three ↔ sat F F.n 0 (fun _ => false) := by
  have hlen : (numCls F).length = F.cls.length := by simp [numCls]
  obtain ⟨hs1, hs2⟩ := sourcesN_spec (rowCode three F hex)
  have hloss := operation_lossSystem three F (fun _ => false)
  have hpres := presents_entriesOf three hloss _ (name_injective F) _ hs1 hs2
  have hvars : ∀ a, a ∈ (sourcesOf (three 0).val (three 1).val (three 2).val F.n
      (numCls F)).map (fun s => s.1) ↔ ∃ j, Sum.elim (nameZ F) (nameP F) j = a := by
    intro a
    simp only [sourcesOf, hlen, List.mem_map]
    constructor
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨j, hj, -⟩ := hs2 s hs
      exact ⟨j, hj.symm⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨s, hs, hj⟩ := hs1 j
      exact ⟨s, hs, hj⟩
  have hentries : entriesOf K (sourcesOf (three 0).val (three 1).val (three 2).val F.n
      (numCls F)) = entriesOf K (sourcesN (three 0).val (three 1).val (three 2).val
        (selN F.n F.cls.length) (coN F.n F.cls.length) (xN F.n F.cls.length (numCls F))
        (yN F.n F.cls.length) (mkN F.n F.cls.length)
        (fxN (three 1).val (three 2).val F.n F.cls.length (numCls F))) := by
    simp only [sourcesOf, hlen]
  constructor
  · rintro ⟨Var, inst, name', t, hrange, hcore, hp⟩
    have hex' : ∀ j : Var, ∃ i : Input F, Sum.elim (nameZ F) (nameP F) i = name' j :=
      fun j => (hvars _).1 ((hrange _).2 ⟨j, rfl⟩)
    choose σ hσ using hex'
    have hsurj : Function.Surjective σ := by
      intro i
      obtain ⟨j, hj⟩ := (hrange _).1 ((hvars _).2 ⟨i, rfl⟩)
      exact ⟨j, name_injective F ((hσ j).trans hj)⟩
    refine (sat_iff_operation three F (fun _ => false) hwf).2
      ⟨t.subst (fun j => .var (σ j)), isCore_rename σ t hcore, fun v => ?_⟩
    rw [Term.eval_subst]
    apply Subtype.ext
    change (t.eval fun j => v (σ j)).val = _
    rw [← normalForm_correct three t hcore]
    rw [meaning_eq_of_presents (name_injective F) name'.injective hpres (hentries ▸ hp) σ hσ
      hsurj v, hloss.meaning_normalForm three v]
  · intro hsat
    obtain ⟨t, hcore, hnf⟩ := (sat_iff_normalForm three F (fun _ => false) hwf).1 hsat
    refine ⟨Input F, inferInstance, ⟨_, name_injective F⟩, t, hvars, hcore, ?_⟩
    change Presents _ (entriesOf K _) _
    rw [hentries, hnf]
    exact hpres

end Code

end KFOL.Recognition.Lists
