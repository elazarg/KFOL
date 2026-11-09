module

public import KFOL.Core.GridPrivate

/-! # The only three possible patterns below the lower grid tuple -/

@[expose] public section

namespace KFOL.Core.Grid

universe u

variable {Role : Type u} [DecidableEq Role]

attribute [local instance] Native.structureOf Equational.coreStructure structureOf

/-- The three patterns allowed in the lower ideal: lower, alpha on F-rows,
and beta on G-rows. Membership of all three in the generated algebra is
proved separately by the explicit padded fold terms. -/
def pattern {r s : ℕ} (three : Fin 3 ↪ Role) : Option Bool → Coordinate r s → Native Role
  | some false, .inl _ => .atom (three 0)
  | some true, .inr (.inl _) => .atom (three 1)
  | _, _ => .lower

/-- Absence of upper markers makes every row profile identical. -/
theorem fProfile_uniform {r s : ℕ} (three : Fin 3 ↪ Role)
    (t : Equational.Term (Equational.CoreSymbol Role) (Option (Variable r s)))
    (noUpper : ∀ c : Coordinate r s, t.realize (rawValue three c) ≠ Native.upper)
    (i k : Fin r) : profile (three 0) (fProfile i) t = profile (three 0) (fProfile k) t := by
  by_contra he
  cases hi : profile (three 0) (fProfile i) t <;>
    cases hk : profile (three 0) (fProfile k) t
  · exact he (hi.trans hk.symm)
  · obtain ⟨a,ha⟩ := upper_of_f_difference three t k i hk hi
    exact noUpper _ ha
  · obtain ⟨a,ha⟩ := upper_of_f_difference three t i k hi hk
    exact noUpper _ ha
  · exact he (hi.trans hk.symm)

theorem gProfile_uniform {r s : ℕ} (three : Fin 3 ↪ Role)
    (t : Equational.Term (Equational.CoreSymbol Role) (Option (Variable r s)))
    (noUpper : ∀ c : Coordinate r s, t.realize (rawValue three c) ≠ Native.upper)
    (j l : Fin s) : profile (three 1) (gProfile j) t = profile (three 1) (gProfile l) t := by
  by_contra he
  cases hj : profile (three 1) (gProfile j) t <;>
    cases hl : profile (three 1) (gProfile l) t
  · exact he (hj.trans hl.symm)
  · obtain ⟨a,ha⟩ := upper_of_g_difference three t l j hl hj
    exact noUpper _ ha
  · obtain ⟨a,ha⟩ := upper_of_g_difference three t j l hj hl
    exact noUpper _ ha
  · exact he (hj.trans hl.symm)

theorem profiles_disjoint {r s : ℕ} (three : Fin 3 ↪ Role)
    (t : Equational.Term (Equational.CoreSymbol Role) (Option (Variable r s)))
    (noUpper : ∀ c : Coordinate r s, t.realize (rawValue three c) ≠ Native.upper)
    (i : Fin r) (j : Fin s) :
    ¬ (profile (three 0) (fProfile i) t = true ∧ profile (three 1) (gProfile j) t = true) :=
  fun h => noUpper _ (upper_of_crossing three t i j h.1 h.2)

omit [DecidableEq Role] in
theorem raw_fRow_no_other_atom {r s : ℕ} (three : Fin 3 ↪ Role)
    (p : {p : Fin r × Fin r // p.1 ≠ p.2}) (a : Option (Fin s))
    (v : Option (Variable r s)) (b : Role) (h0 : b ≠ three 0) (h2 : b ≠ three 2) :
    rawValue three (.inl (p,a)) v ≠ Native.atom b := by
  cases v with
  | none => simp [rawValue]
  | some v => simp only [rawValue]; split_ifs <;> simp_all [Ne.symm h0, Ne.symm h2]

omit [DecidableEq Role] in
theorem raw_gRow_no_other_atom {r s : ℕ} (three : Fin 3 ↪ Role)
    (p : {p : Fin s × Fin s // p.1 ≠ p.2}) (a : Option (Fin r))
    (v : Option (Variable r s)) (b : Role) (h1 : b ≠ three 1) (h2 : b ≠ three 2) :
    rawValue three (.inr (.inl (p,a))) v ≠ Native.atom b := by
  cases v with
  | none => simp [rawValue]
  | some v => simp only [rawValue]; split_ifs <;> simp_all [Ne.symm h1, Ne.symm h2]

omit [DecidableEq Role] in
theorem raw_annotation_no_other_atom {r s : ℕ} (three : Fin 3 ↪ Role)
    (i : Fin r) (j : Fin s) (v : Option (Variable r s)) (b : Role) (h2 : b ≠ three 2) :
    rawValue three (.inr (.inr (i,j))) v ≠ Native.atom b := by
  cases v with
  | none => simp [rawValue]
  | some v => simp only [rawValue]; split_ifs <;> simp_all [Ne.symm h2]

theorem value_fRow {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role)
    (t : Equational.Term (Equational.CoreSymbol Role) (Option (Variable r s)))
    (noUpper : ∀ c : Coordinate r s, t.realize (rawValue three c) ≠ Native.upper)
    (p : {p : Fin r × Fin r // p.1 ≠ p.2}) (a : Option (Fin s)) :
    t.realize (rawValue three (.inl (p,a))) =
      if profile (three 0) (fProfile p.val.2) t then Native.atom (three 0) else Native.lower := by
  have hgamma := no_third_atom hr hs three t noUpper (.inl (p,a))
  have hatom : t.realize (rawValue three (.inl (p,a))) = Native.atom (three 0) ↔
      profile (three 0) (fProfile p.val.2) t = true := by
    rw [realize_eq_atom_iff_profile]
    have heq : (fun v => decide (rawValue three (.inl (p,a)) v = Native.atom (three 0))) =
        fProfile p.val.2 := by
      funext v
      apply Bool.eq_iff_iff.mpr
      simpa only [fProfile, decide_eq_true_eq] using fRow_atom three p a v
    rw [heq]
  have hval := noUpper (.inl (p,a))
  cases he : t.realize (rawValue three (.inl (p,a))) with
  | upper => exact False.elim (hval he)
  | lower =>
    have hf : profile (three 0) (fProfile p.val.2) t = false := by
      apply Bool.eq_false_iff.mpr
      intro hp; have ha := hatom.mpr hp; rw [he] at ha; cases ha
    simp [hf]
  | atom b =>
    by_cases hb : b = three 0
    · subst b
      simp [hatom.mp he]
    · by_cases hb2 : b = three 2
      · subst b; exact False.elim (hgamma he)
      · exact False.elim (no_atom_of_valuation b _
          (fun v => raw_fRow_no_other_atom three p a v b hb hb2) t he)

theorem value_gRow {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role)
    (t : Equational.Term (Equational.CoreSymbol Role) (Option (Variable r s)))
    (noUpper : ∀ c : Coordinate r s, t.realize (rawValue three c) ≠ Native.upper)
    (p : {p : Fin s × Fin s // p.1 ≠ p.2}) (a : Option (Fin r)) :
    t.realize (rawValue three (.inr (.inl (p,a)))) =
      if profile (three 1) (gProfile p.val.2) t then Native.atom (three 1) else Native.lower := by
  have hgamma := no_third_atom hr hs three t noUpper (.inr (.inl (p,a)))
  have hatom : t.realize (rawValue three (.inr (.inl (p,a)))) = Native.atom (three 1) ↔
      profile (three 1) (gProfile p.val.2) t = true := by
    rw [realize_eq_atom_iff_profile]
    have heq : (fun v => decide (rawValue three (.inr (.inl (p,a))) v = Native.atom (three 1))) =
        gProfile p.val.2 := by
      funext v
      apply Bool.eq_iff_iff.mpr
      simpa only [gProfile, decide_eq_true_eq] using gRow_atom three p a v
    rw [heq]
  have hval := noUpper (.inr (.inl (p,a)))
  cases he : t.realize (rawValue three (.inr (.inl (p,a)))) with
  | upper => exact False.elim (hval he)
  | lower =>
    have hf : profile (three 1) (gProfile p.val.2) t = false := by
      apply Bool.eq_false_iff.mpr
      intro hp; have ha := hatom.mpr hp; rw [he] at ha; cases ha
    simp [hf]
  | atom b =>
    by_cases hb : b = three 1
    · subst b
      simp [hatom.mp he]
    · by_cases hb2 : b = three 2
      · subst b; exact False.elim (hgamma he)
      · exact False.elim (no_atom_of_valuation b _
          (fun v => raw_gRow_no_other_atom three p a v b hb hb2) t he)

theorem value_annotation {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role)
    (t : Equational.Term (Equational.CoreSymbol Role) (Option (Variable r s)))
    (noUpper : ∀ c : Coordinate r s, t.realize (rawValue three c) ≠ Native.upper)
    (i : Fin r) (j : Fin s) :
    t.realize (rawValue three (.inr (.inr (i,j)))) = Native.lower := by
  have hgamma := no_third_atom hr hs three t noUpper (.inr (.inr (i,j)))
  have hval := noUpper (.inr (.inr (i,j)))
  cases he : t.realize (rawValue three (.inr (.inr (i,j)))) with
  | upper => exact False.elim (hval he)
  | lower => rfl
  | atom b =>
    by_cases hb2 : b = three 2
    · subst b; exact False.elim (hgamma he)
    · exact False.elim (no_atom_of_valuation b _
        (fun v => raw_annotation_no_other_atom three i j v b hb2) t he)

/-- The unrestricted source-term classification underlying the three-element
lower ideal. No term-size bound, search, or assumed table completeness occurs. -/
theorem pattern_of_no_upper {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role)
    (t : Equational.Term (Equational.CoreSymbol Role) (Option (Variable r s)))
    (noUpper : ∀ c : Coordinate r s, t.realize (rawValue three c) ≠ Native.upper) :
    ∃ kind : Option Bool, ∀ c : Coordinate r s, t.realize (rawValue three c) = pattern three kind c := by
  let i : Fin r := ⟨0, by omega⟩
  let j : Fin s := ⟨0, by omega⟩
  by_cases hf : profile (three 0) (fProfile i) t = true
  · have hg (l : Fin s) : profile (three 1) (gProfile l) t = false :=
      Bool.eq_false_iff.mpr (fun hl => profiles_disjoint three t noUpper i l ⟨hf,hl⟩)
    refine ⟨some false, ?_⟩
    intro c
    rcases c with ⟨p,a⟩ | (⟨p,a⟩ | ⟨k,l⟩)
    · rw [value_fRow hr hs three t noUpper]
      rw [fProfile_uniform three t noUpper p.val.2 i, hf]
      rfl
    · rw [value_gRow hr hs three t noUpper, hg]
      rfl
    · exact value_annotation hr hs three t noUpper k l
  · have hf' (k : Fin r) : profile (three 0) (fProfile k) t = false := by
      rw [fProfile_uniform three t noUpper k i]
      exact Bool.eq_false_iff.mpr hf
    by_cases hg : profile (three 1) (gProfile j) t = true
    · refine ⟨some true, ?_⟩
      intro c
      rcases c with ⟨p,a⟩ | (⟨p,a⟩ | ⟨k,l⟩)
      · rw [value_fRow hr hs three t noUpper, hf']
        rfl
      · rw [value_gRow hr hs three t noUpper]
        rw [gProfile_uniform three t noUpper p.val.2 j, hg]
        rfl
      · exact value_annotation hr hs three t noUpper k l
    · have hg' (l : Fin s) : profile (three 1) (gProfile l) t = false := by
        rw [gProfile_uniform three t noUpper l j]
        exact Bool.eq_false_iff.mpr hg
      refine ⟨none, ?_⟩
      intro c
      rcases c with ⟨p,a⟩ | (⟨p,a⟩ | ⟨k,l⟩)
      · rw [value_fRow hr hs three t noUpper, hf']
        rfl
      · rw [value_gRow hr hs three t noUpper, hg']
        rfl
      · exact value_annotation hr hs three t noUpper k l

end KFOL.Core.Grid
