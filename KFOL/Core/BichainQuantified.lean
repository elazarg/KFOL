module

public import KFOL.Core.BichainCubeCuts
public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.List.GetD

/-! # Quantified Boolean formulas as cube cuts

A prenex formula with a clausal matrix is true exactly when its marked rows
admit no cut, and hence exactly when a pure term omits every mark and
separates the two starting endpoints. Left and right vertices carry the
rows; a label lies on a rectangle of left and right vertices. Each stage has
two branch rows on the left and one relay row on the right.
-/

@[expose] public section
namespace KFOL.Bichain.Quantified

/-- Variables are the stages `1, …, n`. Stage `i` is existential when `ex i`
holds. A literal `(i, s)` says that variable `i` has value `s`. -/
structure Formula where
  n : ℕ
  ex : ℕ → Bool
  cls : List (List (ℕ × Bool))

/-- Input coordinates of the rows. -/
inductive Lab where
  | ch (i : ℕ) (s : Bool)
  | rl (i : ℕ)
  | perm (i : ℕ) (s : Bool)
  | lit (i : ℕ) (s : Bool)
  | kap
  deriving DecidableEq

/-- Branch and clause vertices are on the left, relays and literal resources
on the right. The vertices `br 0 s` and `relay 0` are the starting endpoints. -/
inductive Vtx where
  | br (i : ℕ) (s : Bool)
  | relay (i : ℕ)
  | res (i : ℕ) (s : Bool)
  | cl (c : ℕ)
  deriving DecidableEq

variable (F : Formula)

/-- Every literal names one of the `n` variables. -/
def Formula.WF : Prop := ∀ C ∈ F.cls, ∀ l ∈ C, 1 ≤ l.1 ∧ l.1 ≤ F.n

/-- Truth of the last `k` quantifiers and the matrix after stage `i`. -/
def sat : ℕ → ℕ → (ℕ → Bool) → Prop
  | 0, _, α => ∀ C ∈ F.cls, ∃ l ∈ C, α l.1 = l.2
  | k + 1, i, α =>
    if F.ex (i + 1) then ∃ s, sat k (i + 1) (Function.update α (i + 1) s)
    else ∀ s, sat k (i + 1) (Function.update α (i + 1) s)

/-- The labels whose rectangle contains a left vertex. -/
def inI : Vtx → Lab → Bool
  | .br i _, .ch j _ => j == i + 1
  | .br i _, .rl j => j == i
  | .br i s, .perm j t => j == i && t == s
  | .br i _, .kap => i == F.n
  | .cl c, .lit j t => decide ((j, t) ∈ F.cls.getD c [])
  | _, _ => false

/-- The labels whose rectangle contains a right vertex. -/
def inJ : Vtx → Lab → Bool
  | .relay k, .ch j t => j == k + 1 && decide (j ≤ F.n) && (t || F.ex j)
  | .relay k, .rl j => j == k + 1
  | .relay k, .lit _ _ => k == F.n
  | .relay k, .kap => k == F.n
  | .res i s, .perm j t => j == i && t == s
  | _, _ => false

/-- The coordinate marked by a row. -/
def mark : Vtx → Lab
  | .br i s => .ch i (if F.ex i then s else true)
  | .relay i => .rl i
  | .res i s => .lit i s
  | .cl _ => .kap

/-- A left row is true on its labels and free elsewhere; a right row is false
on its labels and free elsewhere. -/
def rows (z : Vtx) (e : Lab) : Value :=
  if mark F z = e then .possible else if inI F z e then .c
  else if inJ F z e then .b else .neutral

/-- Separation of a left vertex from a right vertex. -/
def cell (a b : Vtx) : CubeQuery Lab :=
  .separate (fun e => inI F a e) (fun e => !inJ F b e)

/-- The rows of the instance. -/
def IsRow : Vtx → Prop
  | .br j _ => 1 ≤ j ∧ j ≤ F.n
  | .relay j => 1 ≤ j ∧ j ≤ F.n
  | .res j _ => 1 ≤ j ∧ j ≤ F.n
  | .cl c => c < F.cls.length

/-- The finite budget of all rows. -/
def allRows : Finset Vtx :=
  ((Finset.range F.n).image fun i => Vtx.br (i + 1) true) ∪
  ((Finset.range F.n).image fun i => Vtx.br (i + 1) false) ∪
  ((Finset.range F.n).image fun i => Vtx.relay (i + 1)) ∪
  ((Finset.range F.n).image fun i => Vtx.res (i + 1) true) ∪
  ((Finset.range F.n).image fun i => Vtx.res (i + 1) false) ∪
  ((Finset.range F.cls.length).image Vtx.cl)

theorem mem_allRows (z : Vtx) : z ∈ allRows F ↔ IsRow F z := by
  cases z with
  | br j s =>
    simp only [allRows, IsRow]
    constructor
    · intro h
      simp at h
      rcases h with ⟨a, ha, rfl, -⟩ | ⟨a, ha, rfl, -⟩ <;> omega
    · intro h
      cases s <;> simp <;> exact ⟨j - 1, by omega, by omega⟩
  | relay j =>
    simp only [allRows, IsRow]
    constructor
    · intro h
      simp at h
      obtain ⟨a, ha, rfl⟩ := h
      omega
    · intro h
      simp
      exact ⟨j - 1, by omega, by omega⟩
  | res j s =>
    simp only [allRows, IsRow]
    constructor
    · intro h
      simp at h
      rcases h with ⟨a, ha, rfl, -⟩ | ⟨a, ha, rfl, -⟩ <;> omega
    · intro h
      cases s <;> simp <;> exact ⟨j - 1, by omega, by omega⟩
  | cl c => simp [allRows, IsRow]

theorem inI_mark (z : Vtx) : inI F z (mark F z) = false := by
  cases z <;> simp [inI, mark]

theorem inJ_mark (z : Vtx) : inJ F z (mark F z) = false := by
  cases z <;> simp [inJ, mark]

theorem inJ_of_inI {z : Vtx} {e : Lab} (h : inI F z e = true) : inJ F z e = false := by
  cases z <;> cases e <;> simp_all [inI, inJ]

theorem rows_possible (z : Vtx) (e : Lab) : rows F z e = .possible ↔ mark F z = e := by
  unfold rows
  split_ifs <;> simp_all

theorem cubeLower_rows (z : Vtx) : cubeLower (rows F z) = fun e => inI F z e := by
  funext e
  unfold cubeLower rows
  by_cases hm : mark F z = e
  · subst hm; simp [inI_mark]
  · cases h1 : inI F z e <;> cases h2 : inJ F z e <;> simp [hm]

theorem cubeUpper_rows (z : Vtx) : cubeUpper (rows F z) = fun e => !inJ F z e := by
  funext e
  unfold cubeUpper rows
  by_cases hm : mark F z = e
  · subst hm; simp [inJ_mark]
  · cases h1 : inI F z e
    · cases h2 : inJ F z e <;> simp [hm]
    · simp [hm, inJ_of_inI F h1]

/-- A cut at a cell selects rows whose marks cover the labels on the cell and
which can each replace the endpoint on either side. -/
theorem cut_intro {budget sel : Finset Vtx} {a b : Vtx} (hsub : sel ⊆ budget)
    (hcov : ∀ e, inI F a e = true → inJ F b e = true → ∃ z ∈ sel, mark F z = e)
    (hl : ∀ z ∈ sel, CubeCut (rows F) (sel.erase z) (cell F z b))
    (hr : ∀ z ∈ sel, CubeCut (rows F) (sel.erase z) (cell F a z)) :
    CubeCut (rows F) budget (cell F a b) := by
  refine CubeCut.cover hsub ?_ ?_ ?_
  · intro e he
    obtain ⟨h1, h2⟩ := he
    obtain ⟨z, hz, hm⟩ := hcov e h1 (by simpa using h2)
    exact ⟨z, hz, (rows_possible F z e).2 hm⟩
  · intro z hz
    have h := hl z hz
    rw [cubeLower_rows]
    exact h
  · intro z hz
    have h := hr z hz
    rw [cubeUpper_rows]
    exact h

theorem cut_inv {budget : Finset Vtx} {a b : Vtx}
    (h : CubeCut (rows F) budget (cell F a b)) :
    ∃ sel : Finset Vtx, sel ⊆ budget ∧
      (∀ e, inI F a e = true → inJ F b e = true → ∃ z ∈ sel, mark F z = e) ∧
      (∀ z ∈ sel, CubeCut (rows F) (sel.erase z) (cell F z b)) ∧
      (∀ z ∈ sel, CubeCut (rows F) (sel.erase z) (cell F a z)) := by
  generalize hq : cell F a b = q at h
  cases h with
  | cover hsub hcov hl hr =>
    subst hq
    refine ⟨_, hsub, ?_, ?_, ?_⟩
    · intro e h1 h2
      obtain ⟨z, hz, hp⟩ := hcov e ⟨h1, by simpa using h2⟩
      exact ⟨z, hz, (rows_possible F z e).1 hp⟩
    · intro z hz
      have h := hl z hz
      rw [cubeLower_rows] at h
      exact h
    · intro z hz
      have h := hr z hz
      rw [cubeUpper_rows] at h
      exact h

/-- A cell with no label has the empty cut. -/
theorem cut_empty {budget : Finset Vtx} {a b : Vtx}
    (h : ∀ e, inI F a e = true → inJ F b e = true → False) :
    CubeCut (rows F) budget (cell F a b) :=
  cut_intro F (Finset.empty_subset _) (fun e h1 h2 => (h e h1 h2).elim)
    (by simp) (by simp)

/-- No row marks a permanent label. -/
theorem mark_ne_perm (z : Vtx) (j : ℕ) (t : Bool) : mark F z ≠ .perm j t := by
  cases z <;> simp [mark]

/-- The rows that the cutting side still needs after stage `i`. -/
def Keep (i : ℕ) (α : ℕ → Bool) : Vtx → Prop
  | .br j _ => i < j ∧ j ≤ F.n
  | .relay j => i < j ∧ j ≤ F.n
  | .res j s => 1 ≤ j ∧ j ≤ F.n ∧ (j ≤ i → α j ≠ s)
  | .cl c => c < F.cls.length

/-- Resources of true literals have been released, and clause rows are real. -/
def Inv (i : ℕ) (α : ℕ → Bool) (budget : Finset Vtx) : Prop :=
  (∀ j s, 1 ≤ j → j ≤ i → α j = s → Vtx.res j s ∉ budget) ∧
  ∀ c, Vtx.cl c ∈ budget → c < F.cls.length


theorem keep_step {i : ℕ} {α : ℕ → Bool} {s : Bool} {z : Vtx}
    (h : Keep F (i + 1) (Function.update α (i + 1) s) z) : Keep F i α z := by
  cases z with
  | br j t => exact ⟨by have := h.1; omega, h.2⟩
  | relay j => exact ⟨by have := h.1; omega, h.2⟩
  | res j t =>
    refine ⟨h.1, h.2.1, fun hj => ?_⟩
    have h3 := h.2.2 (by omega)
    rwa [Function.update_of_ne (by omega)] at h3
  | cl c => exact h

theorem keep_ne {i : ℕ} {α : ℕ → Bool} {z : Vtx} (h : Keep F (i + 1) α z) :
    z ≠ .relay (i + 1) ∧ ∀ s, z ≠ .br (i + 1) s := by
  cases z with
  | br j t =>
    have := h.1
    exact ⟨by simp, fun s hs => by injection hs; omega⟩
  | relay j =>
    have := h.1
    exact ⟨fun hs => by injection hs; omega, by simp⟩
  | res j t => exact ⟨by simp, by simp⟩
  | cl c => exact ⟨by simp, by simp⟩

/-- A false formula has a cut: the cutting side keeps one falsifying branch
at each universal stage and one false clause at the end. -/
theorem cut_of_not_sat (hwf : F.WF) : ∀ (k i : ℕ) (α : ℕ → Bool), i + k = F.n →
    ¬ sat F k i α → ∀ budget : Finset Vtx, (∀ z, Keep F i α z → z ∈ budget) →
      CubeCut (rows F) budget (cell F (.br i (α i)) (.relay i)) := by
  intro k
  induction k with
  | zero =>
    intro i α hi hns budget hb
    classical
    have hin : i = F.n := by omega
    rw [sat] at hns
    push Not at hns
    obtain ⟨C, hC, hfalse⟩ := hns
    obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hC
    have hget : F.cls.getD c [] = F.cls[c] := List.getD_eq_getElem F.cls [] hc
    let sel := budget.filter fun z => Keep F i α z ∧ ∀ c', z = Vtx.cl c' → c' = c
    have hmem : ∀ z, z ∈ sel ↔
        z ∈ budget ∧ Keep F i α z ∧ ∀ c', z = Vtx.cl c' → c' = c := fun z => Finset.mem_filter
    refine cut_intro F (sel := sel) (Finset.filter_subset _ _) ?_ ?_ ?_
    · intro e h1 h2
      cases e with
      | kap =>
        refine ⟨.cl c, (hmem _).2 ⟨hb _ hc, hc, fun c' h => ?_⟩, rfl⟩
        injection h with h
        exact h.symm
      | ch j t => simp [inI, inJ] at h1 h2; omega
      | rl j => simp [inI, inJ] at h1 h2; omega
      | perm j t => simp [inJ] at h2
      | lit j t => simp [inI] at h1
    · intro z hz
      obtain ⟨hzb, hkeep, hcl⟩ := (hmem z).1 hz
      cases z with
      | br j s => exact absurd hkeep.1 (by have := hkeep.2; omega)
      | relay j => exact absurd hkeep.1 (by have := hkeep.2; omega)
      | res j s => exact cut_empty F fun e h1 _ => by cases e <;> simp [inI] at h1
      | cl c' =>
        obtain rfl := hcl c' rfl
        refine cut_intro F (sel := sel.erase (.cl c')) (Finset.Subset.refl _) ?_ ?_ ?_
        · intro e h1 h2
          cases e with
          | lit j t =>
            change decide ((j, t) ∈ F.cls.getD c' []) = true at h1
            have hjt : (j, t) ∈ F.cls[c'] := by
              rw [← hget]
              exact of_decide_eq_true h1
            have hw := hwf _ (List.getElem_mem hc) _ hjt
            refine ⟨.res j t, ?_, rfl⟩
            rw [Finset.mem_erase, hmem]
            exact ⟨by simp, hb _ ⟨hw.1, hw.2, fun _ => hfalse _ hjt⟩,
              ⟨hw.1, hw.2, fun _ => hfalse _ hjt⟩, fun c'' h => by cases h⟩
          | ch j t => simp [inI] at h1
          | rl j => simp [inI] at h1
          | perm j t => simp [inI] at h1
          | kap => simp [inI] at h1
        · intro z' hz'
          rw [Finset.mem_erase, hmem] at hz'
          obtain ⟨hne, -, hkeep', hcl'⟩ := hz'
          cases z' with
          | br j s => exact absurd hkeep'.1 (by have := hkeep'.2; omega)
          | relay j => exact absurd hkeep'.1 (by have := hkeep'.2; omega)
          | res j s => exact cut_empty F fun e h1 _ => by cases e <;> simp [inI] at h1
          | cl c'' => exact absurd (by rw [hcl' c'' rfl]) hne
        · intro z' hz'
          rw [Finset.mem_erase, hmem] at hz'
          obtain ⟨hne, -, hkeep', hcl'⟩ := hz'
          cases z' with
          | br j s => exact absurd hkeep'.1 (by have := hkeep'.2; omega)
          | relay j => exact absurd hkeep'.1 (by have := hkeep'.2; omega)
          | res j s =>
            exact cut_empty F fun e h1 h2 => by cases e <;> simp [inI, inJ] at h1 h2
          | cl c'' => exact absurd (by rw [hcl' c'' rfl]) hne
    · intro z hz
      obtain ⟨hzb, hkeep, hcl⟩ := (hmem z).1 hz
      cases z with
      | br j s => exact absurd hkeep.1 (by have := hkeep.2; omega)
      | relay j => exact absurd hkeep.1 (by have := hkeep.2; omega)
      | res j s =>
        refine cut_empty F fun e h1 h2 => ?_
        cases e <;> simp [inI, inJ] at h1 h2
        obtain ⟨rfl, rfl⟩ := h1
        obtain ⟨rfl, rfl⟩ := h2
        exact hkeep.2.2 le_rfl rfl
      | cl c' => exact cut_empty F fun e _ h2 => by cases e <;> simp [inJ] at h2
  | succ k ih =>
    intro i α hi hns budget hb
    classical
    let good : Bool → Prop := fun s => ¬ sat F k (i + 1) (Function.update α (i + 1) s)
    let sel := budget.filter fun z => Keep F i α z ∧ ∀ s, z = Vtx.br (i + 1) s → good s
    have hmem : ∀ z, z ∈ sel ↔
        z ∈ budget ∧ Keep F i α z ∧ ∀ s, z = Vtx.br (i + 1) s → good s := fun z => Finset.mem_filter
    refine cut_intro F (sel := sel) (Finset.filter_subset _ _) ?_ ?_ ?_
    · intro e h1 h2
      cases e with
      | ch j t =>
        simp [inI, inJ] at h1 h2
        subst h1
        by_cases hex : F.ex (i + 1) = true
        · rw [sat] at hns
          simp only [hex, ↓reduceIte] at hns
          have hall : ∀ s, good s := fun s hs => hns ⟨s, hs⟩
          refine ⟨.br (i + 1) t, (hmem _).2 ⟨hb _ ⟨by omega, by omega⟩,
            ⟨by omega, by omega⟩, fun s _ => hall s⟩, ?_⟩
          simp [mark, hex]
        · rw [sat] at hns
          simp only [hex] at hns
          obtain ⟨s₀, hs₀⟩ := not_forall.mp hns
          have ht : t = true := by
            rcases h2.2 with h | h
            · exact h
            · exact absurd h hex
          refine ⟨.br (i + 1) s₀, (hmem _).2 ⟨hb _ ⟨by omega, by omega⟩,
            ⟨by omega, by omega⟩, fun s h => ?_⟩, ?_⟩
          · injection h with _ h
            subst h
            exact hs₀
          · simp [mark, hex, ht]
      | rl j => simp [inI, inJ] at h1 h2; omega
      | perm j t => simp [inJ] at h2
      | lit j t => simp [inI] at h1
      | kap => simp [inI] at h1; omega
    · intro z hz
      obtain ⟨hzb, hkeep, hbr⟩ := (hmem z).1 hz
      cases z with
      | br j s =>
        by_cases hj : j = i + 1
        · subst hj
          have hg : good s := hbr s rfl
          let sel2 := (sel.erase (.br (i + 1) s)).filter fun z' =>
            Keep F (i + 1) (Function.update α (i + 1) s) z' ∨ z' = Vtx.relay (i + 1)
          have hmem2 : ∀ z', z' ∈ sel2 ↔ (z' ≠ .br (i + 1) s ∧ z' ∈ sel) ∧
              (Keep F (i + 1) (Function.update α (i + 1) s) z' ∨ z' = Vtx.relay (i + 1)) :=
            fun z' => Finset.mem_filter.trans (and_congr Finset.mem_erase Iff.rfl)
          refine cut_intro F (sel := sel2) (Finset.filter_subset _ _) ?_ ?_ ?_
          · intro e h1 h2
            cases e with
            | rl j' =>
              simp [inI, inJ] at h1 h2
              subst h1
              exact ⟨.relay (i + 1), (hmem2 _).2 ⟨⟨by simp, (hmem _).2
                ⟨hb _ ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, fun s' h => by cases h⟩⟩,
                Or.inr rfl⟩, rfl⟩
            | ch j' t => simp [inI, inJ] at h1 h2; omega
            | perm j' t => simp [inJ] at h2
            | lit j' t => simp [inI] at h1
            | kap => simp [inI, inJ] at h1 h2; omega
          · intro z' hz'
            obtain ⟨-, hk2⟩ := (hmem2 z').1 hz'
            cases z' with
            | br j' t =>
              rcases hk2 with hk2 | hk2
              · refine cut_empty F fun e h1 h2 => ?_
                have := hk2.1
                cases e <;> simp [inI, inJ] at h1 h2 <;> omega
              · cases hk2
            | relay j' => exact cut_empty F fun e h1 _ => by cases e <;> simp [inI] at h1
            | res j' t => exact cut_empty F fun e h1 _ => by cases e <;> simp [inI] at h1
            | cl c =>
              refine cut_empty F fun e h1 h2 => ?_
              cases e <;> simp [inI, inJ] at h1 h2
              omega
          · intro z' hz'
            obtain ⟨-, hk2⟩ := (hmem2 z').1 hz'
            cases z' with
            | br j' t => exact cut_empty F fun e _ h2 => by cases e <;> simp [inJ] at h2
            | relay j' =>
              by_cases hj' : j' = i + 1
              · subst hj'
                have h := ih (i + 1) (Function.update α (i + 1) s) (by omega) hg
                  (sel2.erase (.relay (i + 1))) (fun z'' hk'' => by
                    have hne := keep_ne F hk''
                    rw [Finset.mem_erase, hmem2, hmem]
                    exact ⟨hne.1, ⟨hne.2 s, hb _ (keep_step F hk''), keep_step F hk'',
                      fun s' h => absurd h (hne.2 s')⟩, Or.inl hk''⟩)
                rwa [Function.update_self] at h
              · refine cut_empty F fun e h1 h2 => ?_
                rcases hk2 with hk2 | hk2
                · have := hk2.1
                  cases e <;> simp [inI, inJ] at h1 h2 <;> omega
                · injection hk2 with h
                  exact hj' h
            | res j' t =>
              rcases hk2 with hk2 | hk2
              · refine cut_empty F fun e h1 h2 => ?_
                cases e <;> simp [inI, inJ] at h1 h2
                obtain ⟨rfl, rfl⟩ := h1
                obtain ⟨rfl, rfl⟩ := h2
                exact hk2.2.2 le_rfl (Function.update_self ..)
              · cases hk2
            | cl c => exact cut_empty F fun e _ h2 => by cases e <;> simp [inJ] at h2
        · refine cut_empty F fun e h1 h2 => ?_
          have := hkeep.1
          cases e <;> simp [inI, inJ] at h1 h2 <;> omega
      | relay j => exact cut_empty F fun e h1 _ => by cases e <;> simp [inI] at h1
      | res j s => exact cut_empty F fun e h1 _ => by cases e <;> simp [inI] at h1
      | cl c =>
        refine cut_empty F fun e h1 h2 => ?_
        cases e <;> simp [inI, inJ] at h1 h2
        omega
    · intro z hz
      obtain ⟨hzb, hkeep, hbr⟩ := (hmem z).1 hz
      cases z with
      | br j s => exact cut_empty F fun e _ h2 => by cases e <;> simp [inJ] at h2
      | relay j =>
        refine cut_empty F fun e h1 h2 => ?_
        have := hkeep.1
        cases e <;> simp [inI, inJ] at h1 h2 <;> omega
      | res j s =>
        refine cut_empty F fun e h1 h2 => ?_
        cases e <;> simp [inI, inJ] at h1 h2
        obtain ⟨rfl, rfl⟩ := h1
        obtain ⟨rfl, rfl⟩ := h2
        exact hkeep.2.2 le_rfl rfl
      | cl c => exact cut_empty F fun e _ h2 => by cases e <;> simp [inJ] at h2

/-- A true formula has no cut: every cut must offer the chosen branch, then
its relay, and can never keep the resource of a literal made true. -/
theorem not_cut_of_sat (hwf : F.WF) : ∀ (k i : ℕ) (α : ℕ → Bool), i + k = F.n →
    sat F k i α → ∀ budget : Finset Vtx, Inv F i α budget →
      ¬ CubeCut (rows F) budget (cell F (.br i (α i)) (.relay i)) := by
  intro k
  induction k with
  | zero =>
    intro i α hi hs budget hinv hcut
    have hin : i = F.n := by omega
    rw [sat] at hs
    obtain ⟨sel, hsub, hcov, hl, -⟩ := cut_inv F hcut
    obtain ⟨z, hz, hm⟩ := hcov .kap (by simp [inI, hin]) (by simp [inJ, hin])
    cases z with
    | cl c =>
      have hc : c < F.cls.length := hinv.2 c (hsub hz)
      obtain ⟨l, hlC, hval⟩ := hs _ (List.getElem_mem hc)
      obtain ⟨sel2, hsub2, hcov2, -, -⟩ := cut_inv F (hl _ hz)
      have h1 : inI F (.cl c) (.lit l.1 l.2) = true := by
        change decide ((l.1, l.2) ∈ F.cls.getD c []) = true
        rw [List.getD_eq_getElem F.cls [] hc]
        exact decide_eq_true hlC
      obtain ⟨z', hz', hm'⟩ := hcov2 (.lit l.1 l.2) h1 (by simp [inJ, hin])
      cases z' with
      | res j t =>
        injection hm' with hj ht
        subst hj
        subst ht
        have hw := hwf _ (List.getElem_mem hc) _ hlC
        exact hinv.1 l.1 l.2 hw.1 (by omega) hval
          (hsub (Finset.mem_of_mem_erase (hsub2 hz')))
      | br j t => simp [mark] at hm'
      | relay j => simp [mark] at hm'
      | cl c' => simp [mark] at hm'
    | br j t => simp [mark] at hm
    | relay j => simp [mark] at hm
    | res j t => simp [mark] at hm
  | succ k ih =>
    intro i α hi hs budget hinv hcut
    have hlab : ∃ s, inJ F (.relay i) (.ch (i + 1) s) = true ∧
        ∀ s', (if F.ex (i + 1) then s' else true) = s →
          sat F k (i + 1) (Function.update α (i + 1) s') := by
      rw [sat] at hs
      by_cases hex : F.ex (i + 1) = true
      · simp only [hex, ↓reduceIte] at hs
        obtain ⟨s, hs⟩ := hs
        refine ⟨s, by simp [inJ, hex]; omega, fun s' h => ?_⟩
        simp only [hex, ↓reduceIte] at h
        exact h ▸ hs
      · simp only [hex] at hs
        exact ⟨true, by simp [inJ]; omega, fun s' _ => hs s'⟩
    obtain ⟨s, hJ, hnext⟩ := hlab
    obtain ⟨sel, hsub, hcov, hl, -⟩ := cut_inv F hcut
    obtain ⟨z, hz, hm⟩ := hcov (.ch (i + 1) s) (by simp [inI]) hJ
    cases z with
    | br j s' =>
      injection hm with hj hs'
      subst hj
      have hsat := hnext s' hs'
      obtain ⟨sel2, hsub2, hcov2, -, hr2⟩ := cut_inv F (hl _ hz)
      have hres : Vtx.res (i + 1) s' ∉ sel2 := by
        intro hmem
        obtain ⟨sel3, -, hcov3, -, -⟩ := cut_inv F (hr2 _ hmem)
        obtain ⟨z3, -, hm3⟩ := hcov3 (.perm (i + 1) s') (by simp [inI]) (by simp [inJ])
        exact mark_ne_perm F z3 _ _ hm3
      obtain ⟨z2, hz2, hm2⟩ := hcov2 (.rl (i + 1)) (by simp [inI]) (by simp [inJ])
      cases z2 with
      | relay j2 =>
        injection hm2 with hj2
        subst hj2
        have hcut' := hr2 _ hz2
        have hbudget : ∀ z', z' ∈ sel2.erase (.relay (i + 1)) → z' ∈ budget := fun z' h =>
          hsub (Finset.mem_of_mem_erase (hsub2 (Finset.mem_of_mem_erase h)))
        refine ih (i + 1) (Function.update α (i + 1) s') (by omega) hsat
          (sel2.erase (.relay (i + 1))) ⟨fun j t hj1 hj2 hval hmem => ?_,
            fun c hc => hinv.2 c (hbudget _ hc)⟩ ?_
        · by_cases hji : j = i + 1
          · subst hji
            rw [Function.update_self] at hval
            subst hval
            exact hres (Finset.mem_of_mem_erase hmem)
          · rw [Function.update_of_ne hji] at hval
            exact hinv.1 j t hj1 (by omega) hval (hbudget _ hmem)
        · rw [Function.update_self]
          exact hcut'
      | br j2 t2 => simp [mark] at hm2
      | res j2 t2 => simp [mark] at hm2
      | cl c2 => simp [mark] at hm2
    | relay j => simp [mark] at hm
    | res j t => simp [mark] at hm
    | cl c => simp [mark] at hm

/-- The formula is false exactly when its rows admit a cut at the start. -/
theorem cut_iff_not_sat (hwf : F.WF) (α : ℕ → Bool) :
    CubeCut (rows F) (allRows F) (cell F (.br 0 (α 0)) (.relay 0)) ↔ ¬ sat F F.n 0 α := by
  constructor
  · intro hcut hs
    refine not_cut_of_sat F hwf F.n 0 α (by omega) hs (allRows F) ⟨fun j t hj1 hj2 => ?_,
      fun c hc => (mem_allRows F _).1 hc⟩ hcut
    omega
  · intro hns
    refine cut_of_not_sat F hwf F.n 0 α (by omega) hns (allRows F) fun z hz => ?_
    rw [mem_allRows]
    cases z with
    | br j s => exact ⟨hz.1, hz.2⟩
    | relay j => exact ⟨hz.1, hz.2⟩
    | res j s => exact ⟨hz.1, hz.2.1⟩
    | cl c => exact hz

/-- Truth of a quantified formula is the existence of a pure term that omits
every mark of its rows and separates the two starting endpoints. -/
theorem sat_iff_separator (hwf : F.WF) (α : ℕ → Bool) :
    sat F F.n 0 α ↔ ∃ t : Term Lab, t.IsPure ∧
      (∀ z ∈ allRows F, t.eval (rows F z) ≠ .possible) ∧
      (cell F (.br 0 (α 0)) (.relay 0)).Holds t := by
  rw [← not_iff_not, ← cut_iff_not_sat F hwf α, cubeCut_iff]
  constructor
  · rintro h ⟨t, ht, hs, hq⟩
    exact h t ht hs hq
  · intro h t ht hs hq
    exact h ⟨t, ht, hs, hq⟩

end KFOL.Bichain.Quantified
