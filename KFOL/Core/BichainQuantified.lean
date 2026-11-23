module

public import KFOL.Core.BichainCubeCuts
public import KFOL.Definitions.QuantifiedRecognition
public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.List.GetD

/-! # Quantified Boolean formulas as cube cuts

A prenex formula with a clausal matrix is true exactly when its marked rows
admit no cut, and hence exactly when a pure term omits every mark and
separates the two starting endpoints. Left and right vertices carry the
rows; a label lies on a rectangle of left and right vertices. Each stage has
two branch rows on the left and one relay row on the right. The clauses are
offered one at a time, so every label is marked by at most two rows.
-/

@[expose] public section
namespace KFOL.Bichain.Quantified

variable (F : Formula)

theorem mem_allRows (z : Vtx) : z ∈ allRows F ↔ IsRow F z := by
  rw [allRows, Finset.mem_filter, and_iff_right_iff_imp]
  intro h
  cases z with
  | br j s =>
    have hj : j < F.n + F.cls.length + 1 := by
      rcases h with h | h <;> omega
    cases s <;> simp [vertices, hj]
  | relay j =>
    have hj : j < F.n + F.cls.length + 1 := by
      obtain ⟨-, h | h⟩ := h <;> omega
    simp [vertices, hj]
  | res j s =>
    have hj : j < F.n + F.cls.length + 1 := by
      obtain ⟨-, h⟩ := h
      omega
    cases s <;> simp [vertices, hj]
  | cl c =>
    have hc : c < F.n + F.cls.length + 1 := by
      have : c < F.cls.length := h
      omega
    simp [vertices, hc]

theorem mem_labels_of_isLab {e : Lab} (h : IsLab F e) : e ∈ labels F := by
  rw [labels, Finset.mem_filter]
  refine ⟨?_, h⟩
  cases e with
  | ch j s =>
    have hj : j < F.n + F.cls.length + 1 := by
      obtain ⟨-, h⟩ := h
      omega
    cases s <;> simp [coordinates, hj]
  | rl j =>
    have hj : j < F.n + F.cls.length + 1 := by
      obtain ⟨-, h | h⟩ := h <;> omega
    simp [coordinates, hj]
  | perm j s =>
    have hj : j < F.n + F.cls.length + 1 := by
      obtain ⟨-, h⟩ := h
      omega
    cases s <;> simp [coordinates, hj]
  | lit j s =>
    have hj : j < F.n + F.cls.length + 1 := by
      obtain ⟨-, h⟩ := h
      omega
    cases s <;> simp [coordinates, hj]
  | kap c =>
    have hc : c < F.n + F.cls.length + 1 := by
      rcases h with h | h <;> omega
    simp [coordinates, hc]

theorem inI_mark (z : Vtx) : inI F z (mark F z) = false := by
  cases z with
  | br i s =>
    simp only [mark]
    split_ifs <;> simp [inI]
    omega
  | relay i => simp [inI]
  | res i s => simp [inI]
  | cl c => simp [inI, mark]

theorem inJ_mark (z : Vtx) : inJ F z (mark F z) = false := by
  cases z with
  | br i s => simp [inJ]
  | relay i => simp [inJ, mark]
  | res i s => simp [inJ, mark]
  | cl c => simp [inJ]

theorem inJ_of_inI {z : Vtx} {e : Lab} (h : inI F z e = true) : inJ F z e = false := by
  cases z <;> cases e <;> simp_all [inI, inJ]

theorem mark_eq_ch {z : Vtx} {j : ℕ} {s : Bool} (h : mark F z = .ch j s) :
    ∃ s', z = .br j s' ∧ j ≤ F.n ∧ (if F.ex j then s' else true) = s := by
  cases z with
  | br i t =>
    simp only [mark] at h
    split_ifs at h with hi hex <;> injection h with h1 h2
    · subst h1; exact ⟨t, rfl, hi, by simpa [hex] using h2⟩
    · subst h1; exact ⟨t, rfl, hi, by simpa [hex] using h2⟩
  | relay i => simp [mark] at h
  | res i t => simp [mark] at h
  | cl c => simp [mark] at h

theorem mark_eq_rl {z : Vtx} {j : ℕ} (h : mark F z = .rl j) : z = .relay j := by
  cases z with
  | br i t => simp only [mark] at h; split_ifs at h
  | relay i => simp [mark] at h; rw [h]
  | res i t => simp [mark] at h
  | cl c => simp [mark] at h

theorem mark_eq_lit {z : Vtx} {j : ℕ} {t : Bool} (h : mark F z = .lit j t) : z = .res j t := by
  cases z with
  | br i t => simp only [mark] at h; split_ifs at h
  | relay i => simp [mark] at h
  | res i s => simp [mark] at h; rw [h.1, h.2]
  | cl c => simp [mark] at h

theorem mark_eq_kap {z : Vtx} {c : ℕ} (h : mark F z = .kap c) :
    z = .cl c ∨ ∃ t, z = .br (F.n + c + 1) t := by
  cases z with
  | br i t =>
    simp only [mark] at h
    split_ifs at h with hi
    injection h with h
    right
    exact ⟨t, by congr 1; omega⟩
  | relay i => simp [mark] at h
  | res i t => simp [mark] at h
  | cl c' => simp [mark] at h; left; rw [h]

/-- No row marks a permanent label. -/
theorem mark_ne_perm (z : Vtx) (j : ℕ) (t : Bool) : mark F z ≠ .perm j t := by
  cases z with
  | br i s => simp only [mark]; split_ifs <;> simp
  | relay i => simp [mark]
  | res i s => simp [mark]
  | cl c => simp [mark]

theorem rows_possible (z : Vtx) (e : FLab F) : rows F z e = .possible ↔ mark F z = e.val := by
  unfold rows
  split_ifs <;> simp_all

theorem cubeLower_rows (z : Vtx) : cubeLower (rows F z) = fun e => inI F z e.val := by
  funext e
  unfold cubeLower rows
  by_cases hm : mark F z = e.val
  · rw [← hm]; simp [inI_mark]
  · cases h1 : inI F z e.val <;> cases h2 : inJ F z e.val <;> simp [hm]

theorem cubeUpper_rows (z : Vtx) : cubeUpper (rows F z) = fun e => !inJ F z e.val := by
  funext e
  unfold cubeUpper rows
  by_cases hm : mark F z = e.val
  · rw [← hm]; simp [inJ_mark]
  · cases h1 : inI F z e.val
    · cases h2 : inJ F z e.val <;> simp [hm]
    · simp [hm, inJ_of_inI F h1]

/-- A cut at a cell selects rows whose marks cover the labels on the cell and
which can each replace the endpoint on either side. -/
theorem cut_intro {budget sel : Finset Vtx} {a b : Vtx} (hsub : sel ⊆ budget)
    (hcov : ∀ e : FLab F, inI F a e.val = true → inJ F b e.val = true →
      ∃ z ∈ sel, mark F z = e.val)
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
      (∀ e : FLab F, inI F a e.val = true → inJ F b e.val = true →
        ∃ z ∈ sel, mark F z = e.val) ∧
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
    (h : ∀ e : Lab, inI F a e = true → inJ F b e = true → False) :
    CubeCut (rows F) budget (cell F a b) :=
  cut_intro F (Finset.empty_subset _) (fun e h1 h2 => (h e.val h1 h2).elim)
    (by simp) (by simp)

/-- The rows that the cutting side still needs after stage `i`. -/
def Keep (i : ℕ) (α : ℕ → Bool) : Vtx → Prop
  | .br j t => i < j ∧ IsRow F (.br j t)
  | .relay j => i < j ∧ IsRow F (.relay j)
  | .res j s => IsRow F (.res j s) ∧ (j ≤ i → α j ≠ s)
  | .cl c => IsRow F (.cl c)

/-- The rows needed from clause `c` on to reach and test the false clause `c₀`. -/
def KeepC (c c₀ : ℕ) (α : ℕ → Bool) : Vtx → Prop
  | .br j t => F.n + c < j ∧ j ≤ F.n + c₀ ∧ t = true
  | .relay j => F.n + c < j ∧ j ≤ F.n + c₀
  | .res j t => 1 ≤ j ∧ j ≤ F.n ∧ α j ≠ t
  | .cl c' => c' = c₀

/-- Resources of true literals have been released, and only rows remain. -/
def Inv (i : ℕ) (α : ℕ → Bool) (budget : Finset Vtx) : Prop :=
  (∀ j s, 1 ≤ j → j ≤ i → α j = s → Vtx.res j s ∉ budget) ∧ ∀ z ∈ budget, IsRow F z

theorem keep_step {i : ℕ} {α : ℕ → Bool} {s : Bool} {z : Vtx}
    (h : Keep F (i + 1) (Function.update α (i + 1) s) z) : Keep F i α z := by
  cases z with
  | br j t => exact ⟨by have := h.1; omega, h.2⟩
  | relay j => exact ⟨by have := h.1; omega, h.2⟩
  | res j t =>
    refine ⟨h.1, fun hj => ?_⟩
    have h3 := h.2 (by omega)
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

theorem keepC_step {c c₀ : ℕ} {α : ℕ → Bool} {z : Vtx} (h : KeepC F (c + 1) c₀ α z) :
    KeepC F c c₀ α z ∧ z ≠ .relay (F.n + c + 1) ∧ z ≠ .br (F.n + c + 1) true := by
  cases z with
  | br j t =>
    have := h.1
    exact ⟨⟨by omega, h.2⟩, by simp, fun hs => by injection hs; omega⟩
  | relay j =>
    have := h.1
    exact ⟨⟨by omega, h.2⟩, fun hs => by injection hs; omega, by simp⟩
  | res j t => exact ⟨h, by simp, by simp⟩
  | cl c' => exact ⟨h, by simp, by simp⟩

theorem keep_of_keepC {c₀ : ℕ} (hc₀ : c₀ < F.cls.length) {α : ℕ → Bool} {z : Vtx}
    (h : KeepC F 0 c₀ α z) : Keep F F.n α z := by
  cases z with
  | br j t =>
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨by omega, Or.inr ⟨by omega, by omega, h3⟩⟩
  | relay j =>
    obtain ⟨h1, h2⟩ := h
    exact ⟨by omega, by omega, Or.inr (by omega)⟩
  | res j t =>
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨⟨h1, h2⟩, fun _ => h3⟩
  | cl c' =>
    have h' : c' = c₀ := h
    subst h'
    exact hc₀

theorem mark_continue (c : ℕ) : mark F (.br (F.n + c + 1) true) = .kap c := by
  simp only [mark]
  split_ifs with h
  · omega
  · congr 1
    omega

/-- The literals of a false clause are covered by their resources. -/
theorem cut_lit {c₀ : ℕ} (hc₀ : c₀ < F.cls.length) (k : ℕ) {budget : Finset Vtx}
    (hres : ∀ l ∈ F.cls[c₀], Vtx.res l.1 l.2 ∈ budget) :
    CubeCut (rows F) budget (cell F (.cl c₀) (.relay k)) := by
  classical
  refine cut_intro F (sel := budget.filter fun z => ∃ j t, z = Vtx.res j t)
    (Finset.filter_subset _ _) ?_ ?_ ?_
  · rintro ⟨e, he⟩ h1 h2
    cases e with
    | lit j t =>
      change decide ((j, t) ∈ F.cls.getD c₀ []) = true at h1
      rw [List.getD_eq_getElem F.cls [] hc₀] at h1
      exact ⟨.res j t, Finset.mem_filter.2 ⟨hres _ (of_decide_eq_true h1), j, t, rfl⟩, rfl⟩
    | ch j t => simp [inI] at h1
    | rl j => simp [inI] at h1
    | perm j t => simp [inI] at h1
    | kap c => simp [inI] at h1
  · intro z hz
    obtain ⟨-, j, t, rfl⟩ := Finset.mem_filter.1 hz
    exact cut_empty F fun e h1 _ => by cases e <;> simp [inI] at h1
  · intro z hz
    obtain ⟨-, j, t, rfl⟩ := Finset.mem_filter.1 hz
    exact cut_empty F fun e h1 h2 => by cases e <;> simp [inI, inJ] at h1 h2

/-- From clause `c` the cutting side walks to a false clause `c₀` and tests it. -/
theorem cut_clause (α : ℕ → Bool) {c₀ : ℕ} (hc₀ : c₀ < F.cls.length)
    (hfalse : ∀ l ∈ F.cls[c₀], α l.1 ≠ l.2)
    (hwfc : ∀ l ∈ F.cls[c₀], 1 ≤ l.1 ∧ l.1 ≤ F.n) :
    ∀ (d c : ℕ) (s : Bool), c + d = c₀ → (c = 0 → s = α F.n) →
    ∀ budget : Finset Vtx, (∀ z, KeepC F c c₀ α z → z ∈ budget) →
      CubeCut (rows F) budget (cell F (.br (F.n + c) s) (.relay (F.n + c))) := by
  intro d
  induction d with
  | zero =>
    intro c s hc hs budget hb
    classical
    have hcc : c₀ = c := by omega
    let sel := budget.filter fun z => KeepC F c c₀ α z
    have hmem : ∀ z, z ∈ sel ↔ z ∈ budget ∧ KeepC F c c₀ α z := fun z => Finset.mem_filter
    have hresk : ∀ l ∈ F.cls[c₀], KeepC F c c₀ α (.res l.1 l.2) := fun l hl =>
      ⟨(hwfc l hl).1, (hwfc l hl).2, hfalse l hl⟩
    refine cut_intro F (sel := sel) (Finset.filter_subset _ _) ?_ ?_ ?_
    · rintro ⟨e, he⟩ h1 h2
      cases e with
      | kap c' =>
        simp [inI] at h1
        have h3 : c' = c₀ := by omega
        subst h3
        exact ⟨.cl c', (hmem _).2 ⟨hb _ rfl, rfl⟩, rfl⟩
      | ch j t => simp [inI, inJ] at h1 h2; omega
      | rl j => simp [inI, inJ] at h1 h2; omega
      | perm j t => simp [inJ] at h2
      | lit j t => simp [inI] at h1
    · intro z hz
      obtain ⟨hzb, hk⟩ := (hmem z).1 hz
      cases z with
      | br j t => exact absurd hk.1 (by have := hk.2.1; omega)
      | relay j => exact absurd hk.1 (by have := hk.2; omega)
      | res j t => exact cut_empty F fun e h1 _ => by cases e <;> simp [inI] at h1
      | cl c' =>
        have h3 : c' = c₀ := hk
        subst h3
        refine cut_lit F hc₀ _ fun l hl => ?_
        rw [Finset.mem_erase, hmem]
        exact ⟨by simp, hb _ (hresk l hl), hresk l hl⟩
    · intro z hz
      obtain ⟨hzb, hk⟩ := (hmem z).1 hz
      cases z with
      | br j t => exact absurd hk.1 (by have := hk.2.1; omega)
      | relay j => exact absurd hk.1 (by have := hk.2; omega)
      | res j t =>
        refine cut_empty F fun e h1 h2 => ?_
        cases e <;> simp [inI, inJ] at h1 h2
        obtain ⟨rfl, rfl⟩ := h1
        obtain ⟨rfl, rfl⟩ := h2
        obtain ⟨hk1, hk2, hk3⟩ := hk
        have hc0 : c = 0 := by omega
        subst hc0
        exact hk3 (hs rfl).symm
      | cl c' => exact cut_empty F fun e _ h2 => by cases e <;> simp [inJ] at h2
  | succ d ih =>
    intro c s hc hs budget hb
    classical
    let sel := budget.filter fun z => KeepC F c c₀ α z
    have hmem : ∀ z, z ∈ sel ↔ z ∈ budget ∧ KeepC F c c₀ α z := fun z => Finset.mem_filter
    have hresk : ∀ c', ∀ l ∈ F.cls[c₀], KeepC F c' c₀ α (.res l.1 l.2) := fun _ l hl =>
      ⟨(hwfc l hl).1, (hwfc l hl).2, hfalse l hl⟩
    refine cut_intro F (sel := sel) (Finset.filter_subset _ _) ?_ ?_ ?_
    · rintro ⟨e, he⟩ h1 h2
      cases e with
      | kap c' =>
        simp [inI] at h1
        have h3 : c' = c := by omega
        subst h3
        have hk : KeepC F c' c₀ α (.br (F.n + c' + 1) true) := ⟨by omega, by omega, rfl⟩
        exact ⟨.br (F.n + c' + 1) true, (hmem _).2 ⟨hb _ hk, hk⟩, mark_continue F c'⟩
      | ch j t => simp [inI, inJ] at h1 h2; omega
      | rl j => simp [inI, inJ] at h1 h2; omega
      | perm j t => simp [inJ] at h2
      | lit j t => simp [inI] at h1
    · intro z hz
      obtain ⟨hzb, hk⟩ := (hmem z).1 hz
      cases z with
      | br j t =>
        obtain ⟨hk1, hk2, rfl⟩ := hk
        by_cases hj : j = F.n + c + 1
        · subst hj
          let sel2 := (sel.erase (.br (F.n + c + 1) true)).filter fun z' =>
            KeepC F (c + 1) c₀ α z' ∨ z' = Vtx.relay (F.n + c + 1)
          have hmem2 : ∀ z', z' ∈ sel2 ↔ (z' ≠ .br (F.n + c + 1) true ∧ z' ∈ sel) ∧
              (KeepC F (c + 1) c₀ α z' ∨ z' = Vtx.relay (F.n + c + 1)) :=
            fun z' => Finset.mem_filter.trans (and_congr Finset.mem_erase Iff.rfl)
          have hin2 : ∀ z', KeepC F (c + 1) c₀ α z' → z' ∈ sel2 := fun z' hk' => by
            have h := keepC_step F hk'
            exact (hmem2 _).2 ⟨⟨h.2.2, (hmem _).2 ⟨hb _ h.1, h.1⟩⟩, Or.inl hk'⟩
          refine cut_intro F (sel := sel2) (Finset.filter_subset _ _) ?_ ?_ ?_
          · rintro ⟨e, he⟩ h1 h2
            cases e with
            | rl j' =>
              simp [inI, inJ] at h1 h2
              subst h1
              have hk : KeepC F c c₀ α (.relay (F.n + c + 1)) := ⟨by omega, by omega⟩
              exact ⟨.relay (F.n + c + 1), (hmem2 _).2 ⟨⟨by simp, (hmem _).2 ⟨hb _ hk, hk⟩⟩,
                Or.inr rfl⟩, rfl⟩
            | ch j' t => simp [inI, inJ] at h1 h2; omega
            | perm j' t => simp [inJ] at h2
            | lit j' t => simp [inI] at h1
            | kap c' => simp [inI, inJ] at h1 h2; omega
          · intro z' hz'
            obtain ⟨-, hk2'⟩ := (hmem2 z').1 hz'
            cases z' with
            | br j' t =>
              rcases hk2' with hk2' | hk2'
              · refine cut_empty F fun e h1 h2 => ?_
                have := hk2'.1
                cases e <;> simp [inI, inJ] at h1 h2 <;> omega
              · cases hk2'
            | relay j' => exact cut_empty F fun e h1 _ => by cases e <;> simp [inI] at h1
            | res j' t => exact cut_empty F fun e h1 _ => by cases e <;> simp [inI] at h1
            | cl c' =>
              rcases hk2' with hk2' | hk2'
              · have h3 : c' = c₀ := hk2'
                subst h3
                refine cut_lit F hc₀ _ fun l hl => ?_
                exact Finset.mem_erase.2 ⟨by simp, hin2 _ (hresk _ l hl)⟩
              · cases hk2'
          · intro z' hz'
            obtain ⟨-, hk2'⟩ := (hmem2 z').1 hz'
            cases z' with
            | br j' t => exact cut_empty F fun e _ h2 => by cases e <;> simp [inJ] at h2
            | relay j' =>
              by_cases hj' : j' = F.n + c + 1
              · subst hj'
                exact ih (c + 1) true (by omega) (by omega) (sel2.erase (.relay (F.n + c + 1)))
                  fun z'' hk'' => Finset.mem_erase.2 ⟨(keepC_step F hk'').2.1, hin2 _ hk''⟩
              · refine cut_empty F fun e h1 h2 => ?_
                rcases hk2' with hk2' | hk2'
                · have := hk2'.1
                  cases e <;> simp [inI, inJ] at h1 h2 <;> omega
                · injection hk2' with h
                  exact hj' h
            | res j' t =>
              rcases hk2' with hk2' | hk2'
              · refine cut_empty F fun e h1 h2 => ?_
                have := hk2'.2.1
                cases e <;> simp [inI, inJ] at h1 h2
                omega
              · cases hk2'
            | cl c' => exact cut_empty F fun e _ h2 => by cases e <;> simp [inJ] at h2
        · refine cut_empty F fun e h1 h2 => ?_
          cases e <;> simp [inI, inJ] at h1 h2 <;> omega
      | relay j => exact cut_empty F fun e h1 _ => by cases e <;> simp [inI] at h1
      | res j t => exact cut_empty F fun e h1 _ => by cases e <;> simp [inI] at h1
      | cl c' =>
        have h3 : c' = c₀ := hk
        subst h3
        refine cut_lit F hc₀ _ fun l hl => ?_
        rw [Finset.mem_erase, hmem]
        exact ⟨by simp, hb _ (hresk _ l hl), hresk _ l hl⟩
    · intro z hz
      obtain ⟨hzb, hk⟩ := (hmem z).1 hz
      cases z with
      | br j t => exact cut_empty F fun e _ h2 => by cases e <;> simp [inJ] at h2
      | relay j =>
        refine cut_empty F fun e h1 h2 => ?_
        have := hk.1
        cases e <;> simp [inI, inJ] at h1 h2 <;> omega
      | res j t =>
        refine cut_empty F fun e h1 h2 => ?_
        cases e <;> simp [inI, inJ] at h1 h2
        obtain ⟨rfl, rfl⟩ := h1
        obtain ⟨rfl, rfl⟩ := h2
        obtain ⟨hk1, hk2, hk3⟩ := hk
        have hc0 : c = 0 := by omega
        subst hc0
        exact hk3 (hs rfl).symm
      | cl c' => exact cut_empty F fun e _ h2 => by cases e <;> simp [inJ] at h2

/-- A satisfied matrix leaves no cut in the clause chain. -/
theorem not_cut_clause (hwf : F.WF) (α : ℕ → Bool) (hmat : Matrix F α) :
    ∀ (d c : ℕ) (s : Bool), F.cls.length ≤ c + d → (c < F.cls.length ∨ c = 0) →
    ∀ budget : Finset Vtx, Inv F F.n α budget →
      ¬ CubeCut (rows F) budget (cell F (.br (F.n + c) s) (.relay (F.n + c))) := by
  have test : ∀ (c : ℕ) (sel : Finset Vtx), (∀ z ∈ sel, IsRow F z) →
      (∀ j t, 1 ≤ j → j ≤ F.n → α j = t → Vtx.res j t ∉ sel) → .cl c ∈ sel → ∀ k,
      ¬ CubeCut (rows F) (sel.erase (.cl c)) (cell F (.cl c) (.relay (F.n + k))) := by
    intro c sel hrow hres hz k hcut
    have hcm : c < F.cls.length := hrow _ hz
    obtain ⟨l, hlC, hval⟩ := hmat _ (List.getElem_mem hcm)
    obtain ⟨sel2, hsub2, hcov2, -, -⟩ := cut_inv F hcut
    have hw := hwf _ (List.getElem_mem hcm) _ hlC
    have h1 : inI F (.cl c) (.lit l.1 l.2) = true := by
      change decide ((l.1, l.2) ∈ F.cls.getD c []) = true
      rw [List.getD_eq_getElem F.cls [] hcm]
      exact decide_eq_true hlC
    obtain ⟨z', hz', hm'⟩ := hcov2 ⟨.lit l.1 l.2, mem_labels_of_isLab F hw⟩ h1 (by simp [inJ])
    rw [mark_eq_lit F hm'] at hz'
    exact hres l.1 l.2 hw.1 hw.2 hval (Finset.mem_of_mem_erase (hsub2 hz'))
  intro d
  induction d with
  | zero =>
    intro c s hd hc budget hinv hcut
    obtain ⟨sel, hsub, hcov, hl, -⟩ := cut_inv F hcut
    obtain ⟨z, hz, hm⟩ := hcov ⟨.kap c, mem_labels_of_isLab F hc⟩ (by simp [inI]) (by simp [inJ])
    rcases mark_eq_kap F hm with rfl | ⟨t, rfl⟩
    · exact test c sel (fun z hz => hinv.2 z (hsub hz))
        (fun j t h1 h2 hv hmem => hinv.1 j t h1 h2 hv (hsub hmem)) hz c (hl _ hz)
    · have hrow : IsRow F (.br (F.n + c + 1) t) := hinv.2 _ (hsub hz)
      rcases hrow with h | h <;> omega
  | succ d ih =>
    intro c s hd hc budget hinv hcut
    obtain ⟨sel, hsub, hcov, hl, -⟩ := cut_inv F hcut
    obtain ⟨z, hz, hm⟩ := hcov ⟨.kap c, mem_labels_of_isLab F hc⟩ (by simp [inI]) (by simp [inJ])
    rcases mark_eq_kap F hm with rfl | ⟨t, rfl⟩
    · exact test c sel (fun z hz => hinv.2 z (hsub hz))
        (fun j t h1 h2 hv hmem => hinv.1 j t h1 h2 hv (hsub hmem)) hz c (hl _ hz)
    · have hrow : IsRow F (.br (F.n + c + 1) t) := hinv.2 _ (hsub hz)
      have hc1 : c + 1 < F.cls.length := by rcases hrow with h | h <;> omega
      obtain ⟨sel2, hsub2, hcov2, -, hr2⟩ := cut_inv F (hl _ hz)
      obtain ⟨z2, hz2, hm2⟩ := hcov2
        ⟨.rl (F.n + c + 1), mem_labels_of_isLab F ⟨by omega, Or.inr (by omega)⟩⟩
        (by simp [inI]) (by simp [inJ])
      rw [mark_eq_rl F hm2] at hz2
      have hbudget : ∀ z', z' ∈ sel2.erase (.relay (F.n + c + 1)) → z' ∈ budget := fun z' h =>
        hsub (Finset.mem_of_mem_erase (hsub2 (Finset.mem_of_mem_erase h)))
      exact ih (c + 1) t (by omega) (Or.inl hc1) (sel2.erase (.relay (F.n + c + 1)))
        ⟨fun j t' h1 h2 hv hmem => hinv.1 j t' h1 h2 hv (hbudget _ hmem),
          fun z' hz' => hinv.2 z' (hbudget _ hz')⟩ (hr2 _ hz2)

/-- A false formula has a cut: the cutting side keeps one falsifying branch
at each universal stage and one false clause at the end. -/
theorem cut_of_not_sat (hwf : F.WF) : ∀ (k i : ℕ) (α : ℕ → Bool), i + k = F.n →
    ¬ sat F k i α → ∀ budget : Finset Vtx, (∀ z, Keep F i α z → z ∈ budget) →
      CubeCut (rows F) budget (cell F (.br i (α i)) (.relay i)) := by
  intro k
  induction k with
  | zero =>
    intro i α hi hns budget hb
    have hin : i = F.n := by omega
    subst hin
    rw [sat, Matrix] at hns
    push Not at hns
    obtain ⟨C, hC, hfalse⟩ := hns
    obtain ⟨c₀, hc₀, rfl⟩ := List.getElem_of_mem hC
    exact cut_clause F α hc₀ hfalse (fun l hl => hwf _ (List.getElem_mem hc₀) l hl) c₀ 0
      (α F.n) (by omega) (fun _ => rfl) budget fun z hk => hb z (keep_of_keepC F hc₀ hk)
  | succ k ih =>
    intro i α hi hns budget hb
    classical
    let good : Bool → Prop := fun s => ¬ sat F k (i + 1) (Function.update α (i + 1) s)
    let sel := budget.filter fun z => Keep F i α z ∧ ∀ s, z = Vtx.br (i + 1) s → good s
    have hmem : ∀ z, z ∈ sel ↔
        z ∈ budget ∧ Keep F i α z ∧ ∀ s, z = Vtx.br (i + 1) s → good s := fun z => Finset.mem_filter
    have hbr : ∀ t, Keep F i α (.br (i + 1) t) := fun t =>
      ⟨by omega, Or.inl ⟨by omega, by omega⟩⟩
    have hrelay : Keep F i α (.relay (i + 1)) := ⟨by omega, by omega, Or.inl (by omega)⟩
    refine cut_intro F (sel := sel) (Finset.filter_subset _ _) ?_ ?_ ?_
    · rintro ⟨e, he⟩ h1 h2
      cases e with
      | ch j t =>
        simp [inI, inJ] at h1 h2
        subst h1
        by_cases hex : F.ex (i + 1) = true
        · rw [sat] at hns
          simp only [hex, ↓reduceIte] at hns
          have hall : ∀ s, good s := fun s hs => hns ⟨s, hs⟩
          refine ⟨.br (i + 1) t, (hmem _).2 ⟨hb _ (hbr t), hbr t, fun s _ => hall s⟩, ?_⟩
          simp [mark, hex, h2.1]
        · rw [sat] at hns
          simp only [hex] at hns
          obtain ⟨s₀, hs₀⟩ := not_forall.mp hns
          have ht : t = true := by
            rcases h2.2 with h | h
            · exact h
            · exact absurd h hex
          refine ⟨.br (i + 1) s₀, (hmem _).2 ⟨hb _ (hbr s₀), hbr s₀, fun s h => ?_⟩, ?_⟩
          · injection h with _ h
            subst h
            exact hs₀
          · simp [mark, hex, ht, h2.1]
      | rl j => simp [inI, inJ] at h1 h2; omega
      | perm j t => simp [inJ] at h2
      | lit j t => simp [inI] at h1
      | kap c => simp [inI, inJ] at h1 h2; omega
    · intro z hz
      obtain ⟨hzb, hkeep, hgood⟩ := (hmem z).1 hz
      cases z with
      | br j s =>
        by_cases hj : j = i + 1
        · subst hj
          have hg : good s := hgood s rfl
          let sel2 := (sel.erase (.br (i + 1) s)).filter fun z' =>
            Keep F (i + 1) (Function.update α (i + 1) s) z' ∨ z' = Vtx.relay (i + 1)
          have hmem2 : ∀ z', z' ∈ sel2 ↔ (z' ≠ .br (i + 1) s ∧ z' ∈ sel) ∧
              (Keep F (i + 1) (Function.update α (i + 1) s) z' ∨ z' = Vtx.relay (i + 1)) :=
            fun z' => Finset.mem_filter.trans (and_congr Finset.mem_erase Iff.rfl)
          refine cut_intro F (sel := sel2) (Finset.filter_subset _ _) ?_ ?_ ?_
          · rintro ⟨e, he⟩ h1 h2
            cases e with
            | rl j' =>
              simp [inI, inJ] at h1 h2
              subst h1
              exact ⟨.relay (i + 1), (hmem2 _).2 ⟨⟨by simp, (hmem _).2
                ⟨hb _ hrelay, hrelay, fun s' h => by cases h⟩⟩, Or.inr rfl⟩, rfl⟩
            | ch j' t => simp [inI, inJ] at h1 h2; omega
            | perm j' t => simp [inJ] at h2
            | lit j' t => simp [inI] at h1
            | kap c => simp [inI, inJ] at h1 h2; omega
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
                exact hk2.2 le_rfl (Function.update_self ..)
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
      obtain ⟨hzb, hkeep, hgood⟩ := (hmem z).1 hz
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
        exact hkeep.2 le_rfl rfl
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
    subst hin
    rw [sat] at hs
    exact not_cut_clause F hwf α hs F.cls.length 0 (α F.n) (by omega) (Or.inr rfl) budget
      hinv hcut
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
    obtain ⟨z, hz, hm⟩ := hcov
      ⟨.ch (i + 1) s, mem_labels_of_isLab F ⟨by omega, by omega⟩⟩ (by simp [inI]) hJ
    obtain ⟨s', rfl, -, hs'⟩ := mark_eq_ch F hm
    have hsat := hnext s' hs'
    obtain ⟨sel2, hsub2, hcov2, -, hr2⟩ := cut_inv F (hl _ hz)
    have hres : Vtx.res (i + 1) s' ∉ sel2 := by
      intro hmem
      obtain ⟨sel3, -, hcov3, -, -⟩ := cut_inv F (hr2 _ hmem)
      obtain ⟨z3, -, hm3⟩ := hcov3
        ⟨.perm (i + 1) s', mem_labels_of_isLab F ⟨by omega, by omega⟩⟩
        (by simp [inI]) (by simp [inJ])
      exact mark_ne_perm F z3 _ _ hm3
    obtain ⟨z2, hz2, hm2⟩ := hcov2
      ⟨.rl (i + 1), mem_labels_of_isLab F ⟨by omega, Or.inl (by omega)⟩⟩
      (by simp [inI]) (by simp [inJ])
    rw [mark_eq_rl F hm2] at hz2
    have hcut' := hr2 _ hz2
    have hbudget : ∀ z', z' ∈ sel2.erase (.relay (i + 1)) → z' ∈ budget := fun z' h =>
      hsub (Finset.mem_of_mem_erase (hsub2 (Finset.mem_of_mem_erase h)))
    refine ih (i + 1) (Function.update α (i + 1) s') (by omega) hsat
      (sel2.erase (.relay (i + 1))) ⟨fun j t hj1 hj2 hval hmem => ?_,
        fun z' hz' => hinv.2 z' (hbudget _ hz')⟩ ?_
    · by_cases hji : j = i + 1
      · subst hji
        rw [Function.update_self] at hval
        subst hval
        exact hres (Finset.mem_of_mem_erase hmem)
      · rw [Function.update_of_ne hji] at hval
        exact hinv.1 j t hj1 (by omega) hval (hbudget _ hmem)
    · rw [Function.update_self]
      exact hcut'

/-- The formula is false exactly when its rows admit a cut at the start. -/
theorem cut_iff_not_sat (hwf : F.WF) (α : ℕ → Bool) :
    CubeCut (rows F) (allRows F) (cell F (.br 0 (α 0)) (.relay 0)) ↔ ¬ sat F F.n 0 α := by
  constructor
  · intro hcut hs
    refine not_cut_of_sat F hwf F.n 0 α (by omega) hs (allRows F) ⟨fun j t hj1 hj2 => ?_,
      fun z hz => (mem_allRows F z).1 hz⟩ hcut
    omega
  · intro hns
    refine cut_of_not_sat F hwf F.n 0 α (by omega) hns (allRows F) fun z hz => ?_
    rw [mem_allRows]
    cases z with
    | br j s => exact hz.2
    | relay j => exact hz.2
    | res j s => exact hz.1
    | cl c => exact hz

/-- Truth of a quantified formula is the existence of a pure term that omits
every mark of its rows and separates the two starting endpoints. -/
theorem sat_iff_separator (hwf : F.WF) (α : ℕ → Bool) :
    sat F F.n 0 α ↔ ∃ t : Term (FLab F), t.IsPure ∧
      (∀ z ∈ allRows F, t.eval (rows F z) ≠ .possible) ∧
      (cell F (.br 0 (α 0)) (.relay 0)).Holds t := by
  rw [← not_iff_not, ← cut_iff_not_sat F hwf α, cubeCut_iff]
  constructor
  · rintro h ⟨t, ht, hs, hq⟩
    exact h t ht hs hq
  · intro h t ht hs hq
    exact h ⟨t, ht, hs, hq⟩

end KFOL.Bichain.Quantified
