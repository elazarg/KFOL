module

public import KFOL.Definitions.AtomicBasis
public import KFOL.Core.ModelLaws
public import KFOL.Core.Profiles

/-! # The atomic quotient and its separating Boolean owner images -/

@[expose] public section

namespace KFOL.Core.AtomicBasis

universe u v

open FirstOrder

variable {Role : Type u} [DecidableEq Role]

@[simp] theorem choice_eq_some (r i : Role) (x y : Carrier Role) :
    choice r x y = some i ↔
      if r = i then x = some i ∨ y = some i else x = some i ∧ y = some i := by
  by_cases hri : r = i
  · subst i
    by_cases h : x = some r ∨ y = some r
    · simp [choice, h]
    · simp only [choice, ite_eq_right h]
      by_cases hxy : x = y
      · simp only [ite_eq_left hxy]
        exact ⟨fun hx => False.elim (h (.inl hx)), fun hx => False.elim (h hx)⟩
      · simp [hxy, h]
  · by_cases h : x = some r ∨ y = some r
    · have hn : ¬(x = some i ∧ y = some i) := by
        rintro ⟨hx, hy⟩
        rcases h with h | h
        · exact hri (Option.some.inj (h.symm.trans hx))
        · exact hri (Option.some.inj (h.symm.trans hy))
      simp [choice, h, hri, hn]
    · simp only [choice, ite_eq_right h, ite_eq_right hri]
      by_cases hxy : x = y
      · simp [hxy]
      · have hn : ¬(x = some i ∧ y = some i) := fun hh => hxy (hh.1.trans hh.2.symm)
        simp [hxy, hn]

omit [DecidableEq Role] in
@[simp] theorem collapse_eq_some (A : WinnerSet Role) (r : Role) :
    collapse A = some r ↔ A = WinnerSet.singleton r := by
  classical
  unfold collapse
  split
  next h =>
    simp only [Option.some.injEq]
    exact ⟨fun he => he ▸ h.choose_spec,
      fun he => WinnerSet.singleton_inj.mp (h.choose_spec.symm.trans he)⟩
  next h => simp_all

omit [DecidableEq Role] in
theorem ext_atoms {x y : Carrier Role}
    (h : ∀ r, x = some r ↔ y = some r) : x = y := by
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some r => cases (h r).mpr rfl
  | some r => exact ((h r).mp rfl).symm

theorem collapse_choice (r : Role) (A B : WinnerSet Role) :
    collapse (WinnerSet.choice r A B) = choice r (collapse A) (collapse B) := by
  apply ext_atoms
  intro i
  rw [collapse_eq_some, choice_eq_some]
  by_cases hri : r = i
  · subst i
    simp [collapse_eq_some, WinnerSet.choice_eq_owner_iff]
  · simp only [ite_eq_right hri, collapse_eq_some,
      WinnerSet.choice_eq_other_iff A B r hri]

omit [DecidableEq Role] in
theorem collapse_surjective (three : Fin 3 ↪ Role) : Function.Surjective (collapse (Role := Role)) := by
  intro x
  cases x with
  | some r => exact ⟨WinnerSet.singleton r, (collapse_eq_some _ _).mpr rfl⟩
  | none =>
    let A := (WinnerSet.singleton (three 0)).union (WinnerSet.singleton (three 1))
    refine ⟨A, ?_⟩
    cases he : collapse A with
    | none => rfl
    | some r =>
      have ha := (collapse_eq_some A r).mp he
      have h0 : three 0 = r := by
        have : three 0 ∈ (WinnerSet.singleton r).val := ha ▸ (Or.inl rfl)
        exact this
      have h1 : three 1 = r := by
        have : three 1 ∈ (WinnerSet.singleton r).val := ha ▸ (Or.inr rfl)
        exact this
      exact False.elim (three.injective.ne (by decide) (h0.trans h1.symm))

noncomputable def collapseHom :
    letI := Equational.coreStructure Role
    letI := structureOf Role
    WinnerSet Role →[Equational.language (Equational.CoreSymbol Role)] Carrier Role := by
  letI := Equational.coreStructure Role
  letI := structureOf Role
  refine { toFun := collapse, map_fun' := ?_ }
  intro n f args
  cases f with
  | choice r => exact collapse_choice r (args 0) (args 1)

def indicator (i : Role) (x : Carrier Role) : Bool := decide (x = some i)

theorem indicator_choice (i r : Role) (x y : Carrier Role) :
    indicator i (choice r x y) =
      if r = i then indicator i x || indicator i y else indicator i x && indicator i y := by
  simp only [indicator, choice_eq_some]
  split <;> simp

theorem indicators_separate {x y : Carrier Role}
    (h : ∀ i, indicator i x = indicator i y) : x = y := by
  apply ext_atoms
  intro i
  have hh : (indicator i x = true) ↔ (indicator i y = true) := by rw [h i]
  simpa [indicator] using hh

def indicatorHom (i : Role) :
    letI := structureOf Role
    letI := booleanStructure i
    Carrier Role →[Equational.language (Equational.CoreSymbol Role)] Bool := by
  letI := structureOf Role
  letI := booleanStructure i
  refine { toFun := indicator i, map_fun' := ?_ }
  intro n f args
  cases f with
  | choice r => exact indicator_choice i r (args 0) (args 1)

theorem indicator_surjective (i : Role) : Function.Surjective (indicator i) := by
  intro b
  cases b
  · exact ⟨none, by simp [indicator]⟩
  · exact ⟨some i, by simp [indicator]⟩

/-- Owner indicators interpret every core term by its Boolean profile. -/
theorem realize_indicator {Var : Type v} (t : Equational.Term (Equational.CoreSymbol Role) Var)
    (i : Role) (v : Var → Carrier Role) :
    letI := structureOf Role
    indicator i (t.realize v) = profile i (fun j => indicator i (v j)) t := by
  let _ := structureOf Role
  induction t using induction_choice with
  | var j => rfl
  | choice r s t hs ht =>
    change indicator i (choice r (s.realize v) (t.realize v)) = _
    rw [indicator_choice, profile_choice, hs, ht]


end KFOL.Core.AtomicBasis
