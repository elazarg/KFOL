module

public import KFOL.Core.GridRows

/-! # Profile separation in the padded rectangle -/

@[expose] public section

namespace KFOL.Core.Grid

universe u

variable {Role : Type u} [DecidableEq Role]

attribute [local instance] Native.structureOf

/-- Boolean row and column supports in the enlarged generator set. -/
def fProfile {r s : ℕ} (i : Fin r) : Option (Variable r s) → Bool :=
  fun v => decide (v ∈ fBlock i)
def gProfile {r s : ℕ} (j : Fin s) : Option (Variable r s) → Bool :=
  fun v => decide (v ∈ gBlock j)

omit [DecidableEq Role] in
theorem fRow_marker {r s : ℕ} (three : Fin 3 ↪ Role)
    (p : {p : Fin r × Fin r // p.1 ≠ p.2}) (a : Option (Fin s)) :
    rawValue three (.inl (p, a)) (some (fMarker p.val.1 a)) = Native.upper := by
  simp [rawValue]
omit [DecidableEq Role] in
theorem gRow_marker {r s : ℕ} (three : Fin 3 ↪ Role)
    (p : {p : Fin s × Fin s // p.1 ≠ p.2}) (a : Option (Fin r)) :
    rawValue three (.inr (.inl (p, a))) (some (gMarker p.val.1 a)) = Native.upper := by
  simp [rawValue]

omit [DecidableEq Role] in
/-- No atom occurs on the protected first block of an F-row. -/
theorem fRow_no_atom_on_first {r s : ℕ} (three : Fin 3 ↪ Role)
    (p : {p : Fin r × Fin r // p.1 ≠ p.2}) (a : Option (Fin s))
    (v : Option (Variable r s)) (hv : v ∈ fBlock p.val.1) (b : Role) :
    rawValue three (.inl (p, a)) v ≠ Native.atom b := by
  obtain ⟨z, rfl⟩ := exists_fMarker p.val.1 v hv
  have hi := p.property
  cases a <;> cases z <;>
    simp [rawValue, fMarker, cell, row, col, fBlock, hi, Ne.symm hi]
  all_goals split_ifs <;> simp

omit [DecidableEq Role] in
theorem gRow_no_atom_on_first {r s : ℕ} (three : Fin 3 ↪ Role)
    (p : {p : Fin s × Fin s // p.1 ≠ p.2}) (a : Option (Fin r))
    (v : Option (Variable r s)) (hv : v ∈ gBlock p.val.1) (b : Role) :
    rawValue three (.inr (.inl (p, a))) v ≠ Native.atom b := by
  obtain ⟨z, rfl⟩ := exists_gMarker p.val.1 v hv
  have hi := p.property
  cases a <;> cases z <;>
    simp [rawValue, gMarker, cell, row, col, gBlock, hi, Ne.symm hi]
  all_goals split_ifs <;> simp

/-- Different f-profiles force an upper marker at one of the explicitly
included F-rows. The generators may be reused arbitrarily in the term. -/
theorem upper_of_f_difference {r s : ℕ} (three : Fin 3 ↪ Role)
    (t : Equational.Term (Equational.CoreSymbol Role) (Option (Variable r s)))
    (i k : Fin r) (hi : profile (three 0) (fProfile i) t = true)
    (hk : profile (three 0) (fProfile k) t = false) :
    ∃ a : Option (Fin s), t.realize (rawValue three (.inl (⟨(i,k), by
      change i ≠ k; intro he; subst k; rw [hi] at hk; cases hk⟩, a))) = Native.upper := by
  classical
  have hik : i ≠ k := by intro he; subst k; rw [hi] at hk; cases hk
  let p : {p : Fin r × Fin r // p.1 ≠ p.2} := ⟨(i,k), hik⟩
  let selector (x : Option (Variable r s)) : Option (Fin s) :=
    if hx : x ∈ fBlock i then (exists_fMarker i x hx).choose else none
  have select (x : Option (Variable r s)) (hx : x ∈ fBlock i) :
      x = some (fMarker i (selector x)) := by
    simpa only [selector, dite_eq_left hx] using (exists_fMarker i x hx).choose_spec
  obtain ⟨x, _, hx⟩ := marker_of_profile_difference (three 0) (fProfile i) (fProfile k)
    (fun x => rawValue three (.inl (p, selector x)))
    (fun x hx => by
      have hx' : x ∈ fBlock i := of_decide_eq_true hx
      exact (congrArg (rawValue three (.inl (p, selector x))) (select x hx')).trans
        (fRow_marker three p (selector x)))
    (fun x _ z => by simpa only [fProfile, decide_eq_true_eq] using fRow_atom three p (selector x) z)
    (fun x _ _ _ z hz => fRow_no_atom_on_first three p (selector x) z (of_decide_eq_true hz) _)
    t hi hk
  exact ⟨selector x, hx⟩

theorem upper_of_g_difference {r s : ℕ} (three : Fin 3 ↪ Role)
    (t : Equational.Term (Equational.CoreSymbol Role) (Option (Variable r s)))
    (j l : Fin s) (hj : profile (three 1) (gProfile j) t = true)
    (hl : profile (three 1) (gProfile l) t = false) :
    ∃ a : Option (Fin r), t.realize (rawValue three (.inr (.inl (⟨(j,l), by
      change j ≠ l; intro he; subst l; rw [hj] at hl; cases hl⟩, a)))) = Native.upper := by
  classical
  have hjl : j ≠ l := by intro he; subst l; rw [hj] at hl; cases hl
  let p : {p : Fin s × Fin s // p.1 ≠ p.2} := ⟨(j,l), hjl⟩
  let selector (x : Option (Variable r s)) : Option (Fin r) :=
    if hx : x ∈ gBlock j then (exists_gMarker j x hx).choose else none
  have select (x : Option (Variable r s)) (hx : x ∈ gBlock j) :
      x = some (gMarker j (selector x)) := by
    simpa only [selector, dite_eq_left hx] using (exists_gMarker j x hx).choose_spec
  obtain ⟨x, _, hx⟩ := marker_of_profile_difference (three 1) (gProfile j) (gProfile l)
    (fun x => rawValue three (.inr (.inl (p, selector x))))
    (fun x hx => by
      have hx' : x ∈ gBlock j := of_decide_eq_true hx
      exact (congrArg (rawValue three (.inr (.inl (p, selector x)))) (select x hx')).trans
        (gRow_marker three p (selector x)))
    (fun x _ z => by simpa only [gProfile, decide_eq_true_eq] using gRow_atom three p (selector x) z)
    (fun x _ _ _ z hz => gRow_no_atom_on_first three p (selector x) z (of_decide_eq_true hz) _)
    t hj hl
  exact ⟨selector x, hx⟩

/-- Simultaneous row and column profiles force the annotation marker. -/
theorem upper_of_crossing {r s : ℕ} (three : Fin 3 ↪ Role)
    (t : Equational.Term (Equational.CoreSymbol Role) (Option (Variable r s)))
    (i : Fin r) (j : Fin s)
    (hi : profile (three 0) (fProfile i) t = true)
    (hj : profile (three 1) (gProfile j) t = true) :
    t.realize (rawValue three (.inr (.inr (i,j)))) = Native.upper := by
  apply marker_of_two_profiles (three 0) (three 1) (three.injective.ne (by decide))
    (fProfile i) (gProfile j) (rawValue three (.inr (.inr (i,j)))) _ _ _ _ t hi hj
  · intro x hx hy
    obtain ⟨a, rfl⟩ := exists_fMarker i x (of_decide_eq_true hx)
    cases a with
    | none => simp [gProfile, fMarker] at hy
    | some k =>
      have hk : k = j := by simpa [gProfile, fMarker] using hy
      subst k
      simp [rawValue, fMarker]
  · intro x
    have h20 := three.injective.ne (show (2 : Fin 3) ≠ 0 by decide)
    cases x with
    | none => simp [rawValue]
    | some x => simp only [rawValue]; split_ifs <;> simp_all
  · intro x
    have h21 := three.injective.ne (show (2 : Fin 3) ≠ 1 by decide)
    cases x with
    | none => simp [rawValue]
    | some x => simp only [rawValue]; split_ifs <;> simp_all
  · intro b _ _ x hx hy
    obtain ⟨a, rfl⟩ := exists_fMarker i x (of_decide_eq_true hx)
    cases a with
    | none => simp [gProfile, fMarker] at hy
    | some k =>
      have hk : k = j := by simpa [gProfile, fMarker] using hy
      subst k
      simp [rawValue, fMarker]

end KFOL.Core.Grid
