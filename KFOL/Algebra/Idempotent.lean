module

public import KFOL.Algebra.PairTests
public import KFOL.Definitions.Core

/-! # Idempotent syntax and extraction of the intrinsic core -/

@[expose] public section

namespace KFOL

universe u v

namespace WinnerSet

variable {Role : Type u}

theorem ambiguous_of_two_mem (A : WinnerSet Role) (a b : Role) (hab : a ≠ b)
    (ha : a ∈ A.val) (hb : b ∈ A.val) : Ambiguous A := by
  intro r he
  have har : a = r := by simpa [he] using ha
  have hbr : b = r := by simpa [he] using hb
  exact hab (har.trans hbr.symm)

theorem Ambiguous.sameStatus {A B : WinnerSet Role} (hA : Ambiguous A) (hB : Ambiguous B) :
    SameStatus A B := fun r => by simp [hA r, hB r]

theorem Ambiguous.rename {A : WinnerSet Role} (hA : Ambiguous A) (p : Equiv.Perm Role) :
    Ambiguous (rename p A) := by
  intro r he
  obtain ⟨s, rfl⟩ := p.surjective r
  exact hA s ((rename_eq_singleton_iff A s p).mp he)

theorem choice_of_ambiguous (r : Role) {A B : WinnerSet Role}
    (hA : Ambiguous A) (hB : Ambiguous B) : choice r A B = union A B := by
  classical
  simp [choice, hA r, hB r]

theorem Ambiguous.union_left {A B : WinnerSet Role} (hA : Ambiguous A) :
    Ambiguous (union A B) := by
  intro r he
  exact hA r ((union_eq_singleton_iff A B r).mp he).1

end WinnerSet

namespace Term

variable {Role : Type u} {Var : Type v}

/-- A winner leaf forces a constant output contribution on each status cell. -/
theorem exists_constant_on_cell (t : Term Role Var) (v : Var → WinnerSet Role)
    (ht : t.HasWinner) :
    ∃ k, ∀ w : Var → WinnerSet Role,
      (∀ x, WinnerSet.SameStatus (v x) (w x)) → k ∈ (t.eval w).val := by
  classical
  induction t with
  | winner r => exact ⟨r, fun _ _ => rfl⟩
  | var => exact False.elim ht
  | rename p t ih =>
    obtain ⟨k, hk⟩ := ih ht
    exact ⟨p k, fun w hs => ⟨k, hk w hs, rfl⟩⟩
  | choice r s t hs ht' =>
    have transfer : ∀ w, (∀ x, WinnerSet.SameStatus (v x) (w x)) →
        (s.eval v = WinnerSet.singleton r ∨ t.eval v = WinnerSet.singleton r ↔
         s.eval w = WinnerSet.singleton r ∨ t.eval w = WinnerSet.singleton r) := by
      intro w h
      exact or_congr ((s.eval_sameStatus v w h) r) ((t.eval_sameStatus v w h) r)
    by_cases hc : s.eval v = WinnerSet.singleton r ∨ t.eval v = WinnerSet.singleton r
    · refine ⟨r, ?_⟩
      intro w h
      simp [eval, WinnerSet.choice, (transfer w h).mp hc]
    · rcases ht with h | h
      · obtain ⟨k, hk⟩ := hs h
        refine ⟨k, ?_⟩
        intro w h
        have hn := fun hh => hc ((transfer w h).mpr hh)
        simp only [eval, WinnerSet.choice, ite_eq_right hn, WinnerSet.val_union]
        exact Or.inl (hk w h)
      · obtain ⟨k, hk⟩ := ht' h
        refine ⟨k, ?_⟩
        intro w h
        have hn := fun hh => hc ((transfer w h).mpr hh)
        simp only [eval, WinnerSet.choice, ite_eq_right hn, WinnerSet.val_union]
        exact Or.inr (hk w h)

/-- With no winner leaves, every intermediate value stays ambiguous when all
inputs are ambiguous. -/
theorem eval_ambiguous_of_no_winner (t : Term Role Var) (ht : ¬t.HasWinner)
    (v : Var → WinnerSet Role) (hv : ∀ x, WinnerSet.Ambiguous (v x)) :
    WinnerSet.Ambiguous (t.eval v) := by
  induction t with
  | winner => exact False.elim (ht trivial)
  | var x => exact hv x
  | rename p t ih => exact (ih ht).rename p
  | choice r s t hs ht' =>
    have hS := hs (fun h => ht (Or.inl h))
    have hT := ht' (fun h => ht (Or.inr h))
    rw [eval, WinnerSet.choice_of_ambiguous r hS hT]
    exact hS.union_left

/-- Every accumulated input occurrence contributes on the all-ambiguous cell. -/
theorem input_subset_eval (t : Term Role Var) (ht : ¬t.HasWinner)
    (v : Var → WinnerSet Role) (hv : ∀ x, WinnerSet.Ambiguous (v x)) :
    ∀ x p, (x, p) ∈ t.inputOccurrences →
      (WinnerSet.rename p (v x)).val ⊆ (t.eval v).val := by
  induction t with
  | winner => exact False.elim (ht trivial)
  | var j =>
    intro x p hp
    have he : (x, p) = (j, 1) := by simpa [inputOccurrences] using hp
    cases he
    simp [eval]
  | choice r s t hs ht' =>
    have hnS : ¬s.HasWinner := fun h => ht (Or.inl h)
    have hnT : ¬t.HasWinner := fun h => ht (Or.inr h)
    have hS := s.eval_ambiguous_of_no_winner hnS v hv
    have hT := t.eval_ambiguous_of_no_winner hnT v hv
    intro x p hp
    rw [eval, WinnerSet.choice_of_ambiguous r hS hT]
    rcases List.mem_append.mp hp with hp | hp
    · exact (hs hnS x p hp).trans Set.subset_union_left
    · exact (ht' hnT x p hp).trans Set.subset_union_right
  | rename q t ih =>
    intro x p hp
    obtain ⟨⟨y, s⟩, hs, he⟩ := List.mem_map.mp hp
    cases he
    simp only [eval, WinnerSet.rename_mul]
    exact Set.image_mono (ih ht _ _ hs)

/-- Idempotency rules out every winner leaf, including hidden ones. -/
theorem no_winner_of_idempotent (three : Fin 3 ↪ Role) (t : Term Role Var)
    (hd : ∀ A : WinnerSet Role, t.eval (fun _ => A) = A) : ¬t.HasWinner := by
  intro ht
  let top : WinnerSet Role := ⟨Set.univ, three 0, trivial⟩
  have htop : WinnerSet.Ambiguous top := WinnerSet.ambiguous_of_two_mem top
    (three 0) (three 1) (three.injective.ne (by decide)) trivial trivial
  obtain ⟨k, hk⟩ := t.exists_constant_on_cell (fun _ => top) ht
  obtain ⟨a, hak, _⟩ := exists_role_outside_pair three k k
  obtain ⟨b, hba, hbk⟩ := exists_role_outside_pair three a k
  let A := WinnerSet.union (WinnerSet.singleton a) (WinnerSet.singleton b)
  have hA : WinnerSet.Ambiguous A := WinnerSet.ambiguous_of_two_mem A
    a b hba.symm (Or.inl rfl) (Or.inr rfl)
  have hm := hk (fun _ => A) (fun _ => htop.sameStatus hA)
  rw [hd A] at hm
  exact hm.elim (fun h => hak h.symm) (fun h => hbk h.symm)

/-- Every input-occurrence permutation of an idempotent term is identity. -/
theorem input_eq_one_of_idempotent (three : Fin 3 ↪ Role) (t : Term Role Var)
    (hd : ∀ A : WinnerSet Role, t.eval (fun _ => A) = A)
    (x : Var) (p : Equiv.Perm Role) (hp : (x, p) ∈ t.inputOccurrences) : p = 1 := by
  have hn := t.no_winner_of_idempotent three hd
  apply Equiv.ext
  intro a
  change p a = a
  apply Classical.byContradiction
  intro hpa
  obtain ⟨b, hba, hbp⟩ := exists_role_outside_pair three a (p a)
  let A := WinnerSet.union (WinnerSet.singleton a) (WinnerSet.singleton b)
  have hA : WinnerSet.Ambiguous A := WinnerSet.ambiguous_of_two_mem A
    a b hba.symm (Or.inl rfl) (Or.inr rfl)
  have hm := t.input_subset_eval hn (fun _ => A) (fun _ => hA) x p hp
    (show p a ∈ (WinnerSet.rename p A).val from ⟨a, Or.inl rfl, rfl⟩)
  rw [hd A] at hm
  exact hm.elim hpa (fun h => hbp h.symm)

/-- Proof invariant for transporting an accumulated permutation through a term.
It is independent of the extraction algorithm. -/
def CleanUnder (p : Equiv.Perm Role) (t : Term Role Var) : Prop :=
  ¬t.HasWinner ∧ ∀ x q, (x, q) ∈ t.inputOccurrences → p * q = 1

private theorem cleanUnder_choice {p : Equiv.Perm Role} {r : Role} {s t : Term Role Var}
    (h : CleanUnder p (.choice r s t)) : CleanUnder p s ∧ CleanUnder p t := by
  exact ⟨⟨fun hs => h.1 (Or.inl hs),
      fun x q hq => h.2 x q (List.mem_append_left _ hq)⟩,
    ⟨fun ht => h.1 (Or.inr ht),
      fun x q hq => h.2 x q (List.mem_append_right _ hq)⟩⟩

private theorem cleanUnder_rename {p q : Equiv.Perm Role} {t : Term Role Var}
    (h : CleanUnder p (.rename q t)) : CleanUnder (p * q) t := by
  refine ⟨h.1, ?_⟩
  intro x s hs
  have hh := h.2 x (q * s) (List.mem_map.mpr ⟨(x, s), hs, rfl⟩)
  simpa only [mul_assoc] using hh

private theorem cleanUnder_choice_iff {p : Equiv.Perm Role} {r : Role}
    {s t : Term Role Var} :
    CleanUnder p (.choice r s t) ↔ CleanUnder p s ∧ CleanUnder p t := by
  constructor
  · exact cleanUnder_choice
  · rintro ⟨hs, ht⟩
    refine ⟨fun h => h.elim hs.1 ht.1, ?_⟩
    intro x q hq
    exact (List.mem_append.mp hq).elim (hs.2 x q) (ht.2 x q)

private theorem cleanUnder_rename_iff {p q : Equiv.Perm Role} {t : Term Role Var} :
    CleanUnder p (.rename q t) ↔ CleanUnder (p * q) t := by
  constructor
  · exact cleanUnder_rename
  · intro ht
    refine ⟨ht.1, ?_⟩
    intro x s hs
    obtain ⟨⟨y, a⟩, ha, he⟩ := List.mem_map.mp hs
    cases he
    simpa only [mul_assoc] using ht.2 _ _ ha

/-- Pushing permutations removes every internal switch and preserves the
constant-free property. -/
theorem pushRenames_isCore (t : Term Role Var) (p : Equiv.Perm Role)
    (ht : ¬t.HasWinner) : (t.pushRenames p).IsCore := by
  induction t generalizing p with
  | winner => exact False.elim (ht trivial)
  | var => trivial
  | choice r s t hs ht' =>
    exact ⟨hs p (fun h => ht (Or.inl h)), ht' p (fun h => ht (Or.inr h))⟩
  | rename q t ih => exact ih (p * q) ht

/-- The extraction is correct at every valuation, not only the diagonal or
all-ambiguous cell. -/
theorem pushRenames_correct (t : Term Role Var) (p : Equiv.Perm Role)
    (ht : CleanUnder p t) (v : Var → WinnerSet Role) :
    (t.pushRenames p).eval v = WinnerSet.rename p (t.eval v) := by
  induction t generalizing p with
  | winner => exact False.elim (ht.1 trivial)
  | var x =>
    have hh := ht.2 x 1 (by simp [inputOccurrences])
    have hp : p = 1 := by simpa using hh
    simp [pushRenames, eval, hp]
  | choice r s t hs ht' =>
    obtain ⟨hS, hT⟩ := cleanUnder_choice ht
    simp only [pushRenames, eval, hs p hS, ht' p hT, WinnerSet.rename_choice]
  | rename q t ih =>
    simpa only [pushRenames, eval, WinnerSet.rename_mul] using
      ih (p * q) (cleanUnder_rename ht)

/-- The core fragment is idempotent for every role type. -/
theorem IsCore.eval_diagonal {t : Term Role Var} (ht : t.IsCore) (A : WinnerSet Role) :
    t.eval (fun _ => A) = A := by
  induction t with
  | winner => exact False.elim ht
  | var => rfl
  | choice r s t hs ht' => simp only [eval, hs ht.1, ht' ht.2, WinnerSet.choice_self]
  | rename => exact False.elim ht

/-- Exact syntactic characterization of full-language idempotency. -/
theorem idempotent_iff_clean (three : Fin 3 ↪ Role) (t : Term Role Var) :
    (∀ A : WinnerSet Role, t.eval (fun _ => A) = A) ↔
      ¬t.HasWinner ∧ ∀ x p, (x, p) ∈ t.inputOccurrences → p = 1 := by
  constructor
  · intro hd
    exact ⟨t.no_winner_of_idempotent three hd, t.input_eq_one_of_idempotent three hd⟩
  · intro hc A
    have hh : CleanUnder 1 t := by simpa only [CleanUnder, one_mul] using hc
    have he := t.pushRenames_correct 1 hh (fun _ => A)
    rw [WinnerSet.rename_one] at he
    exact he.symm.trans ((t.pushRenames_isCore 1 hc.1).eval_diagonal A)

/-- Extraction never increases the number of constructor occurrences.
This is a syntax-size theorem, not a machine running-time claim. -/
theorem size_pushRenames_le (t : Term Role Var) (p : Equiv.Perm Role) :
    (t.pushRenames p).size ≤ t.size := by
  induction t generalizing p with
  | winner => exact Nat.le_refl _
  | var => exact Nat.le_refl _
  | choice r s t hs ht =>
    exact Nat.add_le_add_right (Nat.add_le_add (hs p) (ht p)) 1
  | rename q t ih => exact (ih (p * q)).trans (Nat.le_add_right _ _)

/-- Deterministic core extraction for every idempotent full-language term. -/
theorem idempotent_extraction (three : Fin 3 ↪ Role) (t : Term Role Var)
    (hd : ∀ A : WinnerSet Role, t.eval (fun _ => A) = A) :
    (t.pushRenames 1).IsCore ∧
      (∀ v : Var → WinnerSet Role, (t.pushRenames 1).eval v = t.eval v) ∧
      (t.pushRenames 1).size ≤ t.size := by
  obtain ⟨hn, hp⟩ := (t.idempotent_iff_clean three).mp hd
  refine ⟨t.pushRenames_isCore 1 hn, ?_, t.size_pushRenames_le 1⟩
  intro v
  have hh : CleanUnder 1 t := ⟨hn, by simpa only [one_mul] using hp⟩
  simpa only [WinnerSet.rename_one] using t.pushRenames_correct 1 hh v

/-- The idempotent operations are precisely those expressible in the core. -/
theorem idempotent_iff_core (three : Fin 3 ↪ Role) (t : Term Role Var) :
    (∀ A : WinnerSet Role, t.eval (fun _ => A) = A) ↔
      ∃ c : Term Role Var, c.IsCore ∧ ∀ v, c.eval v = t.eval v := by
  constructor
  · intro hd
    obtain ⟨hc, he, _⟩ := t.idempotent_extraction three hd
    exact ⟨t.pushRenames 1, hc, he⟩
  · rintro ⟨c, hc, he⟩ A
    exact (he (fun _ => A)).symm.trans (hc.eval_diagonal A)

/-- Every clean term succeeds in the executable finite-role extractor. -/
theorem extractCore?_of_clean [Fintype Role] [DecidableEq Role]
    (t : Term Role Var) (p : Equiv.Perm Role) (ht : CleanUnder p t) :
    t.extractCore? p = some (t.pushRenames p) := by
  induction t generalizing p with
  | winner => exact False.elim (ht.1 trivial)
  | var x =>
    have hh := ht.2 x 1 (by simp [inputOccurrences])
    have hp : p = 1 := by simpa using hh
    simp [extractCore?, pushRenames, hp]
  | choice r s t hs ht' =>
    obtain ⟨hS, hT⟩ := cleanUnder_choice ht
    simp only [extractCore?, hs p hS, ht' p hT, pushRenames]
  | rename q t ih => exact ih (p * q) (cleanUnder_rename ht)

/-- Success of the executable extractor certifies the syntactic invariant. -/
theorem cleanUnder_of_extractCore? [Fintype Role] [DecidableEq Role]
    (t : Term Role Var) (p : Equiv.Perm Role) (c : Term Role Var)
    (he : t.extractCore? p = some c) : CleanUnder p t := by
  induction t generalizing p c with
  | winner => simp [extractCore?] at he
  | var x =>
    by_cases hp : ∀ r, p r = r
    · have hp' : p = 1 := Equiv.ext hp
      simp [CleanUnder, HasWinner, inputOccurrences, hp']
    · simp [extractCore?, hp] at he
  | choice r s t hs ht =>
    cases hS : s.extractCore? p with
    | none => simp [extractCore?, hS] at he
    | some cS =>
      cases hT : t.extractCore? p with
      | none => simp [extractCore?, hS, hT] at he
      | some cT =>
        exact cleanUnder_choice_iff.mpr ⟨hs p cS hS, ht p cT hT⟩
  | rename q t ih => exact cleanUnder_rename_iff.mpr (ih (p * q) c he)

/-- The checked extractor has a unique specified result whenever it succeeds. -/
theorem extractCore?_eq_some_iff [Fintype Role] [DecidableEq Role]
    (t : Term Role Var) (p : Equiv.Perm Role) (c : Term Role Var) :
    t.extractCore? p = some c ↔ CleanUnder p t ∧ c = t.pushRenames p := by
  constructor
  · intro he
    have hc := t.cleanUnder_of_extractCore? p c he
    exact ⟨hc, (Option.some.inj (he.symm.trans (t.extractCore?_of_clean p hc)))⟩
  · rintro ⟨hc, rfl⟩
    exact t.extractCore?_of_clean p hc

/-- The executable test succeeds exactly for idempotent full-language terms. -/
theorem extractCore?_isSome_iff [Fintype Role] [DecidableEq Role]
    (three : Fin 3 ↪ Role) (t : Term Role Var) :
    (∃ c, t.extractCore? 1 = some c) ↔
      ∀ A : WinnerSet Role, t.eval (fun _ => A) = A := by
  rw [t.idempotent_iff_clean three]
  constructor
  · rintro ⟨c, hc⟩
    simpa only [CleanUnder, one_mul] using t.cleanUnder_of_extractCore? 1 c hc
  · intro hc
    refine ⟨t.pushRenames 1, t.extractCore?_of_clean 1 ?_⟩
    simpa only [CleanUnder, one_mul] using hc

/-- Successful checked extraction returns a core term with equal semantics on
all inputs and no increase in syntax size. -/
theorem extractCore?_correct [Fintype Role] [DecidableEq Role]
    (t : Term Role Var) (c : Term Role Var) (he : t.extractCore? 1 = some c) :
    c.IsCore ∧ (∀ v : Var → WinnerSet Role, c.eval v = t.eval v) ∧ c.size ≤ t.size := by
  obtain ⟨hc, rfl⟩ := (t.extractCore?_eq_some_iff 1 c).mp he
  refine ⟨t.pushRenames_isCore 1 hc.1, ?_, t.size_pushRenames_le 1⟩
  intro v
  simpa only [WinnerSet.rename_one] using t.pushRenames_correct 1 hc v

end Term
end KFOL
