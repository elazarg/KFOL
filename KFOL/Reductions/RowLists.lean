module

public import KFOL.Reductions.GuardLists
public import KFOL.Core.RowLosses

/-! # Listing the losses of the operation of rows

A family of marked rows is coded by lists of numbers: the names of the
selectors and of the row inputs, the two endpoints, the marks and the fixed
inputs of the rows. The list program below writes the losses of every input
of the operation of the rows. When every row input is marked by at most two
rows, each input has at most four listed losses.
-/

@[expose] public section

namespace KFOL.Recognition.Lists

open Core.Sources Problems

/-! ### Two members of a list -/

/-- The first member of a list and the first member different from it. -/
def twoOf (ms : List ℕ) : List ℕ :=
  if ms.isEmpty then [] else
    [ms.headD 0, ((ms.filter fun r => !(r == ms.headD 0)) ++ [ms.headD 0]).headD 0]

theorem length_twoOf_le (ms : List ℕ) : (twoOf ms).length ≤ 2 := by
  unfold twoOf
  split_ifs <;> simp

theorem mem_twoOf (ms : List ℕ) (h : ∃ z1 z2, ∀ r ∈ ms, r = z1 ∨ r = z2) (r : ℕ) :
    r ∈ twoOf ms ↔ r ∈ ms := by
  cases ms with
  | nil => simp [twoOf]
  | cons a l =>
    obtain ⟨z1, z2, hz⟩ := h
    have hF : ∀ b, b ∈ ((a :: l).filter fun r => !(r == a)) ↔ b ∈ a :: l ∧ b ≠ a := by
      intro b
      rw [List.mem_filter]
      exact and_congr_right fun _ => by simp
    simp only [twoOf, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.headD_cons,
      List.mem_cons, List.not_mem_nil, or_false]
    generalize ((a :: l).filter fun r => !(r == a)) = F at hF
    cases F with
    | nil =>
      simp only [List.nil_append, List.headD_cons, or_self]
      constructor
      · exact fun h => Or.inl h
      · rintro (h | h)
        · exact h
        · by_contra hra
          exact absurd ((hF r).2 ⟨List.mem_cons_of_mem _ h, hra⟩) List.not_mem_nil
    | cons b F' =>
      obtain ⟨hbm, hba⟩ := (hF b).1 List.mem_cons_self
      simp only [List.cons_append, List.headD_cons]
      constructor
      · rintro (rfl | rfl)
        · exact Or.inl rfl
        · exact List.mem_cons.1 hbm
      · rintro (rfl | hr)
        · exact Or.inl rfl
        · by_cases hra : r = a
          · exact Or.inl hra
          · right
            have h1 := hz a List.mem_cons_self
            have h2 := hz b hbm
            have h3 := hz r (List.mem_cons_of_mem _ hr)
            rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
              rcases h3 with rfl | rfl <;> first | rfl | exact absurd rfl hra | exact absurd rfl hba

/-! ### The list program -/

/-- Every row input at the first owner. -/
def lossCapN (c0 : ℕ) (coN : List ℕ) : List (ℕ × ℕ) := coN.map fun x => (x, c0)

/-- The code of the first endpoint and the endpoint at the third owner. -/
def lossXN (c2 : ℕ) (selN xN : List ℕ) : List (ℕ × ℕ) :=
  (selN.map fun u => (u, c2)) ++ xN.map fun x => (x, c2)

/-- The code of the second endpoint and its complement at the second owner. -/
def lossYN (c1 : ℕ) (selN yN : List ℕ) : List (ℕ × ℕ) :=
  (selN.map fun u => (u, c1)) ++ yN.map fun x => (x, c1)

/-- The code of a row and its fixed inputs at their atoms. -/
def lossRowN (c1 c2 : ℕ) (selN : List ℕ) (fxN : List (ℕ × ℕ × ℕ)) (z : ℕ) : List (ℕ × ℕ) :=
  (selN.map fun u => (u, if u == z then c1 else c2)) ++
    (fxN.filter fun f => f.1 == z).map fun f => f.2

/-- The losses of every input. -/
def sourcesN (c0 c1 c2 : ℕ) (selN coN xN yN : List ℕ) (mkN : List (ℕ × ℕ))
    (fxN : List (ℕ × ℕ × ℕ)) : List (ℕ × List (List (ℕ × ℕ))) :=
  (selN.map fun u => (u, [lossCapN c0 coN])) ++
  coN.map fun x => (x,
    (if xN.any (fun a => a == x) then [] else [lossXN c2 selN xN]) ++
    (if yN.any (fun a => a == x) then [] else [lossYN c1 selN yN]) ++
    (twoOf ((mkN.filter fun mk => mk.2 == x).map fun mk => mk.1)).map
      (lossRowN c1 c2 selN fxN))

/-! ### Coded rows -/

section Coded

variable {K : ℕ} (three : Fin 3 ↪ Fin K) {Z W : Type} [Fintype Z] [DecidableEq Z] [Fintype W]
  (rows : Z → W → Bichain.Value) (X Y : W → Bool) (nameZ : Z → ℕ) (nameP : Option W → ℕ)

/-- Lists of numbers code a family of marked rows with two endpoints. -/
structure RowCode (selN coN xN yN : List ℕ) (mkN : List (ℕ × ℕ))
    (fxN : List (ℕ × ℕ × ℕ)) : Prop where
  inj : Function.Injective (Sum.elim nameZ nameP)
  sel : ∀ a, a ∈ selN ↔ ∃ z, nameZ z = a
  co : ∀ a, a ∈ coN ↔ ∃ x, nameP x = a
  xs : ∀ a, a ∈ xN ↔ ∃ x, endP X x = true ∧ nameP x = a
  ys : ∀ a, a ∈ yN ↔ ∃ x, endP Y x = false ∧ nameP x = a
  mks : ∀ a b, (a, b) ∈ mkN ↔ ∃ z x, rowP rows z x = .possible ∧ nameZ z = a ∧ nameP x = b
  fx : ∀ a b r, (a, b, r) ∈ fxN ↔ ∃ z x, nameZ z = a ∧ nameP x = b ∧
    ((rowP rows z x = .b ∧ r = (three 1).val) ∨ (rowP rows z x = .c ∧ r = (three 2).val))
  two : ∀ x : Option W, ∃ z1 z2 : Z, ∀ z, rowP rows z x = .possible → z = z1 ∨ z = z2

variable {three rows X Y nameZ nameP} {selN coN xN yN : List ℕ} {mkN : List (ℕ × ℕ)}
  {fxN : List (ℕ × ℕ × ℕ)}

omit [Fintype Z] [DecidableEq Z] [Fintype W] in
theorem RowCode.injZ (hc : RowCode three rows X Y nameZ nameP selN coN xN yN mkN fxN) :
    Function.Injective nameZ := fun _ _ h => Sum.inl.inj (hc.inj (a₁ := .inl _) (a₂ := .inl _) h)

omit [Fintype Z] [DecidableEq Z] [Fintype W] in
theorem RowCode.injP (hc : RowCode three rows X Y nameZ nameP selN coN xN yN mkN fxN) :
    Function.Injective nameP := fun _ _ h => Sum.inr.inj (hc.inj (a₁ := .inr _) (a₂ := .inr _) h)

omit [Fintype Z] [DecidableEq Z] in
theorem postsMatch_cap (hc : RowCode three rows X Y nameZ nameP selN coN xN yN mkN fxN) :
    PostsMatch (Sum.elim nameZ nameP) (lossCapN (three 0).val coN) (lossCap three) := by
  intro a r
  simp only [lossCapN, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨x, hx, rfl, rfl⟩
    obtain ⟨y, rfl⟩ := (hc.co x).1 hx
    exact ⟨(.inr y, three 0), (mem_lossCap three _).2 ⟨y, rfl⟩, rfl, rfl⟩
  · rintro ⟨q, hq, rfl, rfl⟩
    obtain ⟨y, rfl⟩ := (mem_lossCap three q).1 hq
    exact ⟨nameP y, (hc.co _).2 ⟨y, rfl⟩, rfl, rfl⟩

omit [DecidableEq Z] in
theorem postsMatch_X (hc : RowCode three rows X Y nameZ nameP selN coN xN yN mkN fxN) :
    PostsMatch (Sum.elim nameZ nameP) (lossXN (three 2).val selN xN) (lossX three X) := by
  intro a r
  simp only [lossXN, List.mem_append, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro (⟨u, hu, rfl, rfl⟩ | ⟨x, hx, rfl, rfl⟩)
    · obtain ⟨z, rfl⟩ := (hc.sel u).1 hu
      exact ⟨(.inl z, three 2), (mem_lossX three X _).2 (Or.inl ⟨z, rfl⟩), rfl, rfl⟩
    · obtain ⟨y, hy, rfl⟩ := (hc.xs x).1 hx
      exact ⟨(.inr y, three 2), (mem_lossX three X _).2 (Or.inr ⟨y, hy, rfl⟩), rfl, rfl⟩
  · rintro ⟨q, hq, rfl, rfl⟩
    rcases (mem_lossX three X q).1 hq with ⟨z, rfl⟩ | ⟨y, hy, rfl⟩
    · exact Or.inl ⟨nameZ z, (hc.sel _).2 ⟨z, rfl⟩, rfl, rfl⟩
    · exact Or.inr ⟨nameP y, (hc.xs _).2 ⟨y, hy, rfl⟩, rfl, rfl⟩

omit [DecidableEq Z] in
theorem postsMatch_Y (hc : RowCode three rows X Y nameZ nameP selN coN xN yN mkN fxN) :
    PostsMatch (Sum.elim nameZ nameP) (lossYN (three 1).val selN yN) (lossY three Y) := by
  intro a r
  simp only [lossYN, List.mem_append, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro (⟨u, hu, rfl, rfl⟩ | ⟨x, hx, rfl, rfl⟩)
    · obtain ⟨z, rfl⟩ := (hc.sel u).1 hu
      exact ⟨(.inl z, three 1), (mem_lossY three Y _).2 (Or.inl ⟨z, rfl⟩), rfl, rfl⟩
    · obtain ⟨y, hy, rfl⟩ := (hc.ys x).1 hx
      exact ⟨(.inr y, three 1), (mem_lossY three Y _).2 (Or.inr ⟨y, hy, rfl⟩), rfl, rfl⟩
  · rintro ⟨q, hq, rfl, rfl⟩
    rcases (mem_lossY three Y q).1 hq with ⟨z, rfl⟩ | ⟨y, hy, rfl⟩
    · exact Or.inl ⟨nameZ z, (hc.sel _).2 ⟨z, rfl⟩, rfl, rfl⟩
    · exact Or.inr ⟨nameP y, (hc.ys _).2 ⟨y, hy, rfl⟩, rfl, rfl⟩

theorem postsMatch_row (hc : RowCode three rows X Y nameZ nameP selN coN xN yN mkN fxN)
    (z : Z) :
    PostsMatch (Sum.elim nameZ nameP)
      (lossRowN (three 1).val (three 2).val selN fxN (nameZ z)) (lossRow three rows z) := by
  intro a r
  simp only [lossRowN, List.mem_append, List.mem_map, List.mem_filter, Prod.mk.injEq,
    beq_iff_eq]
  constructor
  · rintro (⟨u, hu, rfl, rfl⟩ | ⟨⟨a', b', r'⟩, ⟨hf, hz⟩, he⟩)
    · obtain ⟨z', rfl⟩ := (hc.sel u).1 hu
      refine ⟨(.inl z', if z' = z then three 1 else three 2),
        (mem_lossRow three rows z _).2 (Or.inl ⟨z', rfl⟩), rfl, ?_⟩
      by_cases e : z' = z
      · simp [e]
      · have hne : nameZ z' ≠ nameZ z := fun h => e (hc.injZ h)
        simp [e, hne]
    · obtain ⟨rfl, rfl⟩ : b' = a ∧ r' = r := Prod.mk.inj he
      obtain rfl : a' = nameZ z := hz
      obtain ⟨z', x, hz', rfl, hrow⟩ := (hc.fx _ _ _).1 hf
      obtain rfl : z' = z := hc.injZ hz'
      rcases hrow with ⟨hrow, rfl⟩ | ⟨hrow, rfl⟩
      · exact ⟨(.inr x, three 1),
          (mem_lossRow three rows z' _).2 (Or.inr (Or.inl ⟨x, hrow, rfl⟩)), rfl, rfl⟩
      · exact ⟨(.inr x, three 2),
          (mem_lossRow three rows z' _).2 (Or.inr (Or.inr ⟨x, hrow, rfl⟩)), rfl, rfl⟩
  · rintro ⟨q, hq, rfl, rfl⟩
    rcases (mem_lossRow three rows z q).1 hq with ⟨u, rfl⟩ | ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
    · refine Or.inl ⟨nameZ u, (hc.sel _).2 ⟨u, rfl⟩, rfl, ?_⟩
      by_cases e : u = z
      · simp [e]
      · have hne : nameZ u ≠ nameZ z := fun h => e (hc.injZ h)
        simp [e, hne]
    · exact Or.inr ⟨(nameZ z, nameP x, (three 1).val),
        ⟨(hc.fx _ _ _).2 ⟨z, x, rfl, rfl, Or.inl ⟨hx, rfl⟩⟩, rfl⟩, rfl⟩
    · exact Or.inr ⟨(nameZ z, nameP x, (three 2).val),
        ⟨(hc.fx _ _ _).2 ⟨z, x, rfl, rfl, Or.inr ⟨hx, rfl⟩⟩, rfl⟩, rfl⟩

omit [Fintype Z] [DecidableEq Z] [Fintype W] in
theorem mem_markers (hc : RowCode three rows X Y nameZ nameP selN coN xN yN mkN fxN)
    (x : Option W) (r : ℕ) :
    r ∈ twoOf ((mkN.filter fun mk => mk.2 == nameP x).map fun mk => mk.1) ↔
      ∃ z, rowP rows z x = .possible ∧ nameZ z = r := by
  have hmem : ∀ r, r ∈ ((mkN.filter fun mk => mk.2 == nameP x).map fun mk => mk.1) ↔
      ∃ z, rowP rows z x = .possible ∧ nameZ z = r := by
    intro r
    simp only [List.mem_map, List.mem_filter, beq_iff_eq]
    constructor
    · rintro ⟨⟨a, b⟩, ⟨hm, hb⟩, rfl⟩
      obtain rfl : b = nameP x := hb
      obtain ⟨z, y, hrow, rfl, hy⟩ := (hc.mks _ _).1 hm
      obtain rfl : y = x := hc.injP hy
      exact ⟨z, hrow, rfl⟩
    · rintro ⟨z, hrow, rfl⟩
      exact ⟨(nameZ z, nameP x), ⟨(hc.mks _ _).2 ⟨z, x, hrow, rfl, rfl⟩, rfl⟩, rfl⟩
  rw [mem_twoOf _ ?_ r, hmem]
  obtain ⟨z1, z2, hz⟩ := hc.two x
  refine ⟨nameZ z1, nameZ z2, fun r hr => ?_⟩
  obtain ⟨z, hrow, rfl⟩ := (hmem r).1 hr
  rcases hz z hrow with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **The listed losses.** Every input is listed once for each of its names,
with at most four losses, and these are the losses of the operation. -/
theorem sourcesN_spec (hc : RowCode three rows X Y nameZ nameP selN coN xN yN mkN fxN) :
    (∀ j : Inp Z W, ∃ s ∈ sourcesN (three 0).val (three 1).val (three 2).val selN coN xN yN
      mkN fxN, s.1 = Sum.elim nameZ nameP j) ∧
    ∀ s ∈ sourcesN (three 0).val (three 1).val (three 2).val selN coN xN yN mkN fxN,
      ∃ j : Inp Z W, s.1 = Sum.elim nameZ nameP j ∧ s.2.length ≤ 4 ∧
        LossesMatch (Sum.elim nameZ nameP) s.2 (losses three rows X Y j) := by
  have hXany : ∀ x : Option W, (xN.any fun a => a == nameP x) = endP X x := by
    intro x
    rw [Bool.eq_iff_iff, List.any_eq_true]
    constructor
    · rintro ⟨a, ha, he⟩
      obtain ⟨y, hy, hya⟩ := (hc.xs a).1 ha
      obtain rfl : y = x := hc.injP (hya.trans (beq_iff_eq.1 he))
      exact hy
    · intro hx
      exact ⟨nameP x, (hc.xs _).2 ⟨x, hx, rfl⟩, beq_self_eq_true _⟩
  have hYany : ∀ x : Option W, (yN.any fun a => a == nameP x) = !endP Y x := by
    intro x
    rw [Bool.eq_iff_iff, List.any_eq_true]
    constructor
    · rintro ⟨a, ha, he⟩
      obtain ⟨y, hy, hya⟩ := (hc.ys a).1 ha
      obtain rfl : y = x := hc.injP (hya.trans (beq_iff_eq.1 he))
      simp [hy]
    · intro hx
      exact ⟨nameP x, (hc.ys _).2 ⟨x, by simpa using hx, rfl⟩, beq_self_eq_true _⟩
  constructor
  · rintro (u | x)
    · exact ⟨(nameZ u, [lossCapN (three 0).val coN]), List.mem_append_left _
        (List.mem_map.2 ⟨nameZ u, (hc.sel _).2 ⟨u, rfl⟩, rfl⟩), rfl⟩
    · exact ⟨_, List.mem_append_right _
        (List.mem_map.2 ⟨nameP x, (hc.co _).2 ⟨x, rfl⟩, rfl⟩), rfl⟩
  · intro s hs
    rcases List.mem_append.1 hs with hs | hs
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hs
      obtain ⟨u, rfl⟩ := (hc.sel a).1 ha
      refine ⟨.inl u, rfl, by simp, ?_, ?_⟩
      · intro z hz
        rw [(mem_losses_inl three rows X Y u z).1 hz]
        exact ⟨_, List.mem_singleton.2 rfl, postsMatch_cap hc⟩
      · intro z' hz'
        rw [List.mem_singleton.1 hz']
        exact ⟨_, (mem_losses_inl three rows X Y u _).2 rfl, postsMatch_cap hc⟩
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hs
      obtain ⟨x, rfl⟩ := (hc.co a).1 ha
      refine ⟨.inr x, rfl, ?_, ?_, ?_⟩
      · have h2 := length_twoOf_le ((mkN.filter fun mk => mk.2 == nameP x).map fun mk => mk.1)
        simp only [List.length_append, List.length_map]
        split_ifs <;> simp <;> omega
      · intro z hz
        simp only [hXany, hYany, List.mem_append, List.mem_map]
        rcases (mem_losses_inr three rows X Y x z).1 hz with ⟨hx, rfl⟩ | ⟨hx, rfl⟩ | ⟨z', hz', rfl⟩
        · exact ⟨_, Or.inl (Or.inl (by simp [hx])), postsMatch_X hc⟩
        · exact ⟨_, Or.inl (Or.inr (by simp [hx])), postsMatch_Y hc⟩
        · exact ⟨_, Or.inr ⟨nameZ z', (mem_markers hc x _).2 ⟨z', hz', rfl⟩, rfl⟩,
            postsMatch_row hc z'⟩
      · intro z' hz'
        simp only [hXany, hYany, List.mem_append, List.mem_map] at hz'
        rcases hz' with (hz' | hz') | ⟨r, hr, rfl⟩
        · cases hx : endP X x
          · rw [hx] at hz'
            obtain rfl : z' = _ := by simpa using hz'
            exact ⟨_, (mem_losses_inr three rows X Y x _).2 (Or.inl ⟨hx, rfl⟩), postsMatch_X hc⟩
          · rw [hx] at hz'
            simp at hz'
        · cases hx : endP Y x
          · rw [hx] at hz'
            simp at hz'
          · rw [hx] at hz'
            obtain rfl : z' = _ := by simpa using hz'
            exact ⟨_, (mem_losses_inr three rows X Y x _).2 (Or.inr (Or.inl ⟨hx, rfl⟩)),
              postsMatch_Y hc⟩
        · obtain ⟨z, hz, rfl⟩ := (mem_markers hc x r).1 hr
          exact ⟨_, (mem_losses_inr three rows X Y x _).2 (Or.inr (Or.inr ⟨z, hz, rfl⟩)),
            postsMatch_row hc z⟩

end Coded

end KFOL.Recognition.Lists
